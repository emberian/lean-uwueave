/-
# Uwueave.EraKernel — the executable ERA arbitration kernel.

THIS IS LEAN-AUTHORED SEMANTICS COMPILED TO C. The Rust crate does not
implement epoch arbitration; it marshals bytes to `uwueave_era_resolve` (the
`@[export]` below), which lake compiles to C, and `build.rs` links into the
crate. Rust's remaining jobs are the deliberately dumb ones: recording events
and cuts, value-keying, merging, IO (`rust/src/era.rs`). `Uwueave/Era.lean` is
the protocol model this kernel executes — and the decision layer here is
*literally* `Era.resolve`: this file adds a byte codec and a status trace
around the exact function `duelling_admins_resolved`, `resolve_same_sets` and
`final_view_immune` are theorems about. No second copy of the semantics
exists on either side of the FFI.

## The contract — ERA FORMAT v1

Input `ByteArray`, little-endian 64-bit words:

```
word 0                       : nc — cut count
word 1                       : ne — event count
words 2 .. 2+2nc             : the cut records, 2 words each: (epoch, eid) —
                               the arbiter's announcement stream (Era §2)
words 2+2nc .. 2+2nc+5ne     : the events, 5 words each:
                               (eid, kind, actor, target, role) — kind codes
                               0 join, 1 write, 2 promote, 3 demote (Era §1);
                               any other kind is junk: never authorised,
                               reported with status 2
```

Output `ByteArray`, little-endian 64-bit words, `3 + 2·nu + 2·ns` of them:

```
word 0                       : started — 1 iff any join executed, else 0
word 1                       : nu — user count
word 2                       : ns — status count (execution-order length)
words 3 .. 3+2nu             : nu × (user, role) pairs, strictly ascending
                               user order — one per distinct user named as
                               actor or target of any decoded event
                               (authorised or not; outsiders included); role
                               is the resolved view's code (0 outsider,
                               1 reader, 2 writer, 3 admin)
words 3+2nu .. 3+2nu+2ns     : ns × (eid, status) pairs, in EXECUTION order
                               (`Era.execOrder`, the arbitration order):
                               0 = applied, 1 = skipped-unauthorised (the
                               paper's ✗ mark, judged at the point of
                               execution), 2 = skipped-invalid (unknown kind)
```

All three dimensions are in the response, so it parses unambiguously.
`ns ≤ ne`: exact duplicates in the request are canonicalised away by
`execOrder` (`insertE` skips them), so the status block covers the *set* of
distinct events — at-least-once delivery is exactly as good as exactly-once,
which is `resolve_same_sets`' point made visible in the trace's length.

Statuses are attributed by eid. Era.lean needs no eid-uniqueness premise
(distinct events sharing an eid are still totally ordered, and this kernel
emits one pair per distinct *event*), but a consumer that keys statuses by
eid sees unambiguous attribution only when eids are unique — `rust/src/era.rs`
value-keys events by eid and refuses duplicate-eid-different-content at
record and merge, which is exactly that premise, enforced where it is needed.

## Claim discipline

By construction (no proof debt): `eraReplay` is literally
`encodeWords ∘ responseWords ∘ (decodeCuts, decodeEvents)` — a composition,
not a re-implementation — and `responseWords` reads its view from
`Era.resolve` *verbatim* and its order from `Era.execOrder` *verbatim*. The
one mirrored computation is the status trace (`statusOf`, Exec-v2 style),
whose faithfulness is pinned by `applyEvent_skip_of_statusOf_ne_zero`: a
nonzero status really is a no-op on the view.

**Proved, in this file** (axioms ⊆ `{propext, Classical.choice, Quot.sound}`;
no `sorry`/`native_decide`/`#guard`):

  * `eraReplay_same_sets` / `responseWords_same_sets` — **whole-response
    delivery-independence**: membership-equivalent cut lists and event lists
    (any order, duplication, batching) produce byte-identical responses.
    `resolve_same_sets` + `execOrder_same_sets` carry the view and the trace;
    the user block needs its own canonicality (`usersOf_same_sets`, proved
    here by the `sorted_unique` route on ascending user lists).
  * Size lemmas: `size_eraReplay` (= `8·(3 + 2nu + 2ns)` bytes exactly),
    `length_responseWords`, `length_statusesFrom` (one status per
    execution-order entry), `length_decodeCuts` / `length_decodeEvents`.
  * Output codec, word level, ExecRefine §7 style: `getWord_encodeWords` /
    `getWord_eraReplay` — word `j` of the response IS response word `j` (the
    round trip is cheaper than Exec's: every emitted value is a `Nat` in u64
    range, so there is no two's-complement leg) — and the header observables
    `eraReplay_word0/1/2`.
  * Trace faithfulness: `statusOf_eq_zero_iff`,
    `applyEvent_skip_of_statusOf_ne_zero`.
  * The duel, through this kernel's layers: `duel_trace_marks_the_skip`
    (e5's ✗ is visible in the trace exactly where `duel_pending_verdict`
    says the demote lost) and `duel_response_words` (the full response of
    the Fig. 2 scenario, word for word).

**Determinism**: `eraReplay` is a pure function of its input bytes — equal
bytes give equal bytes with nothing to prove. The claim with content is the
set-function one, and it is proved (`eraReplay_same_sets`).

## Non-claims — the honest boundary

  * **The input codec is not proved.** Like `SeqKernel.lean` (and unlike
    `Exec.lean` §8), there is no Lean-side canonical request encoder and no
    canonicality checker: the Rust marshaller's agreement with the layout
    above is test evidence only. The export surface stays at exactly one
    symbol by design.
  * **ERA's price is Era.lean's price**, restated not re-proved: the arbiter
    is trusted (equivocation degrades to re-ordering, never divergence —
    `resolve_same_sets` has no honesty hypothesis), the pending suffix is
    rollback-able, and prefix stability under cut growth is NOT claimed.
  * Statuses judge authorisation against the *canonicalised execution
    order*, not request order — that is the protocol (§3.2), not a codec
    quirk.
  * **Everything downstream of the C backend is trusted**, as everywhere in
    this library.
-/
import Uwueave.Era
import Uwueave.ExecRefine

namespace Uwueave.EraKernel

open Uwueave.Era
open Uwueave.Exec (getWord pushWord size_pushWord getWord_pushWord getWord_pushWord_lt)

/-! ## §1. Decode — the input side of ERA FORMAT v1

`Exec.getWord` is total (`0` out of range), so malformed input degrades to
junk output, never to a crash — the house discipline. Every field is a plain
`Nat` read; ERA has no signed values. -/

/-- Decode the `nc` cut records (`nc` = word 0): words `2 .. 2+2nc`, two words
per record, `(epoch, eid)`. -/
def decodeCuts (input : ByteArray) : List Cut :=
  let nc := (getWord input 0).toNat
  (List.range nc).map fun i =>
    ((getWord input (2 + 2 * i)).toNat, (getWord input (2 + 2 * i + 1)).toNat)

/-- Decode the `ne` events (`ne` = word 1) following the cut block: five words
per event, `(eid, kind, actor, target, role)`. -/
def decodeEvents (input : ByteArray) : List Event :=
  let nc := (getWord input 0).toNat
  let ne := (getWord input 1).toNat
  (List.range ne).map fun j =>
    let o := 2 + 2 * nc + 5 * j
    { eid    := (getWord input o).toNat
      kind   := (getWord input (o + 1)).toNat
      actor  := (getWord input (o + 2)).toNat
      target := (getWord input (o + 3)).toNat
      role   := (getWord input (o + 4)).toNat }

/-- The decoded cut list has exactly `nc` records. -/
theorem length_decodeCuts (input : ByteArray) :
    (decodeCuts input).length = (getWord input 0).toNat := by
  simp [decodeCuts]

/-- The decoded event list has exactly `ne` events. -/
theorem length_decodeEvents (input : ByteArray) :
    (decodeEvents input).length = (getWord input 1).toNat := by
  simp [decodeEvents]

/-! ## §2. The user roster — every user the request names, once, ascending

The response reports a role for each user named as actor or target of any
decoded event. The roster is canonicalised by sorted insertion (the
`insertE`/`sorted_unique` discipline of `Era.lean` §3, on `Nat` with `<`), so
it is a function of the event SET — the third leg `responseWords_same_sets`
needs beside `resolve_same_sets` and `execOrder_same_sets`. -/

/-- Ordered duplicate-skipping insertion into an ascending user list. -/
def insertUser (x : Nat) : List Nat → List Nat
  | [] => [x]
  | a :: l =>
    if x = a then a :: l
    else if x < a then x :: a :: l
    else a :: insertUser x l

/-- The users named by a delivery log — actors and targets of every event
(authorised or not), each once, strictly ascending. -/
def usersOf (log : List Event) : List Nat :=
  log.foldr (fun e acc => insertUser e.actor (insertUser e.target acc)) []

theorem mem_insertUser {x y : Nat} :
    ∀ {l : List Nat}, y ∈ insertUser x l ↔ y = x ∨ y ∈ l := by
  intro l
  induction l with
  | nil => simp [insertUser]
  | cons a t ih =>
    by_cases h1 : x = a
    · subst h1
      simp only [insertUser]
      constructor
      · exact Or.inr
      · rintro (rfl | hm)
        · exact List.Mem.head t
        · exact hm
    · by_cases h2 : x < a
      · simp only [insertUser, if_neg h1, if_pos h2]
        constructor
        · intro hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact Or.inl rfl
          · exact Or.inr hm
        · rintro (rfl | hm)
          · exact List.Mem.head _
          · exact List.Mem.tail _ hm
      · simp only [insertUser, if_neg h1, if_neg h2]
        constructor
        · intro hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact Or.inr (List.Mem.head t)
          · rcases ih.mp hm with h | h
            · exact Or.inl h
            · exact Or.inr (List.Mem.tail a h)
        · rintro (rfl | hm)
          · exact List.Mem.tail a (ih.mpr (Or.inl rfl))
          · rcases List.mem_cons.mp hm with rfl | h
            · exact List.Mem.head _
            · exact List.Mem.tail _ (ih.mpr (Or.inr h))

theorem pairwise_insertUser {x : Nat} :
    ∀ {l : List Nat}, l.Pairwise (· < ·) → (insertUser x l).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil =>
    intro _
    exact List.Pairwise.cons (fun b hb => by cases hb) List.Pairwise.nil
  | cons a t ih =>
    intro hp
    cases hp with
    | cons ha ht =>
      by_cases h1 : x = a
      · simp only [insertUser, if_pos h1]
        exact List.Pairwise.cons ha ht
      · by_cases h2 : x < a
        · simp only [insertUser, if_neg h1, if_pos h2]
          refine List.Pairwise.cons ?_ (List.Pairwise.cons ha ht)
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact h2
          · exact Nat.lt_trans h2 (ha b hb)
        · simp only [insertUser, if_neg h1, if_neg h2]
          refine List.Pairwise.cons ?_ (ih ht)
          intro b hb
          rcases mem_insertUser.mp hb with rfl | hb
          · omega
          · exact ha b hb

/-- The roster is strictly ascending (hence duplicate-free). -/
theorem pairwise_usersOf : ∀ log : List Event, (usersOf log).Pairwise (· < ·)
  | [] => List.Pairwise.nil
  | _ :: t => pairwise_insertUser (pairwise_insertUser (pairwise_usersOf t))

/-- Roster membership: exactly the actors and targets of the log. -/
theorem mem_usersOf {u : Nat} : ∀ {log : List Event},
    u ∈ usersOf log ↔ ∃ e ∈ log, u = e.actor ∨ u = e.target := by
  intro log
  induction log with
  | nil => simp [usersOf]
  | cons e t ih =>
    show u ∈ insertUser e.actor (insertUser e.target (usersOf t)) ↔ _
    rw [mem_insertUser, mem_insertUser, ih]
    constructor
    · rintro (rfl | rfl | ⟨e', he', hu⟩)
      · exact ⟨e, List.Mem.head t, Or.inl rfl⟩
      · exact ⟨e, List.Mem.head t, Or.inr rfl⟩
      · exact ⟨e', List.Mem.tail e he', hu⟩
    · rintro ⟨e', he', hu⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · rcases hu with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨e', he', hu⟩)

/-- Strictly ascending `Nat` lists with the same members are equal —
`Era.sorted_unique` for the roster's order. -/
theorem sorted_nat_unique : ∀ {l l' : List Nat},
    l.Pairwise (· < ·) → l'.Pairwise (· < ·) →
    (∀ x, x ∈ l ↔ x ∈ l') → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' _ _ hmem
    cases l' with
    | nil => rfl
    | cons a t => exact absurd ((hmem a).mpr (List.Mem.head t)) (by simp)
  | cons a t ih =>
    intro l' hp hp' hmem
    cases l' with
    | nil => exact absurd ((hmem a).mp (List.Mem.head t)) (by simp)
    | cons a' t' =>
      cases hp with
      | cons ha ht =>
        cases hp' with
        | cons ha' ht' =>
          have heq : a = a' := by
            rcases List.mem_cons.mp ((hmem a).mp (List.Mem.head t)) with h | h
            · exact h
            · rcases List.mem_cons.mp ((hmem a').mpr (List.Mem.head t'))
                with h' | h'
              · exact h'.symm
              · have h1 := ha' a h
                have h2 := ha a' h'
                omega
          subst heq
          have hmem' : ∀ x, x ∈ t ↔ x ∈ t' := by
            intro x
            constructor
            · intro hx
              rcases List.mem_cons.mp ((hmem x).mp (List.Mem.tail a hx))
                with rfl | h
              · exact absurd (ha x hx) (by omega)
              · exact h
            · intro hx
              rcases List.mem_cons.mp ((hmem x).mpr (List.Mem.tail a hx))
                with rfl | h
              · exact absurd (ha' x hx) (by omega)
              · exact h
          rw [ih ht ht' hmem']

/-- The roster is a function of the event SET — the user-block leg of
delivery-independence. -/
theorem usersOf_same_sets {log log' : List Event}
    (hl : ∀ e, e ∈ log ↔ e ∈ log') : usersOf log = usersOf log' := by
  refine sorted_nat_unique (pairwise_usersOf log) (pairwise_usersOf log') ?_
  intro u
  rw [mem_usersOf, mem_usersOf]
  constructor
  · rintro ⟨e, he, hu⟩
    exact ⟨e, (hl e).mp he, hu⟩
  · rintro ⟨e, he, hu⟩
    exact ⟨e, (hl e).mpr he, hu⟩

/-! ## §3. The status trace — Fig. 2's ✗ marks, Exec-v2 style

One status per execution-order entry, judged against the view the event
actually met — the mirror of `Exec.opStatus`. The mirror's faithfulness is
`applyEvent_skip_of_statusOf_ne_zero`: a nonzero status is an exact no-op on
the view, so the trace partitions the execution into events that acted and
events that did not. -/

/-- Status of one event against the view it met: `0` = applied, `1` =
skipped-unauthorised (a known kind refused at its point of execution — the ✗
mark), `2` = skipped-invalid (unknown kind; such an event is *also* never
authorised — `authorised`'s catch-all — the two codes split the refusal by
its reason, exactly as Exec v2 splits cycle-skips from malformed ops). -/
def statusOf (v : GroupView) (e : Event) : Nat :=
  if authorised v e then 0
  else if e.kind ≤ 3 then 1 else 2

/-- A zero status is exactly an authorised event. -/
theorem statusOf_eq_zero_iff {v : GroupView} {e : Event} :
    statusOf v e = 0 ↔ authorised v e = true := by
  unfold statusOf
  cases ha : authorised v e
  · by_cases hk : e.kind ≤ 3 <;> simp [hk]
  · simp

/-- **The mirror is faithful**: a nonzero status is an exact no-op on the
view (`Exec.applyOp_skip_of_opStatus_ne_zero`'s analogue). -/
theorem applyEvent_skip_of_statusOf_ne_zero {v : GroupView} {e : Event}
    (h : statusOf v e ≠ 0) : applyEvent v e = v := by
  have hf : authorised v e = false := by
    cases hh : authorised v e
    · rfl
    · exact absurd (statusOf_eq_zero_iff.mpr hh) h
  exact applyEvent_unauthorised hf

/-- The status trace of an execution order, walked from view `v`: each event
is judged against the view every earlier event (applied or skipped) left
behind — the same fold discipline as `Era.resolve`, with the same
`applyEvent`, on the same list. -/
def statusesFrom (v : GroupView) : List Event → List Nat
  | [] => []
  | e :: rest => statusOf v e :: statusesFrom (applyEvent v e) rest

/-- One status word per execution-order entry, from any starting view. -/
theorem length_statusesFrom (v : GroupView) :
    ∀ l : List Event, (statusesFrom v l).length = l.length
  | [] => rfl
  | e :: rest => by
    simp only [statusesFrom, List.length_cons]
    rw [length_statusesFrom (applyEvent v e) rest]

/-! ### Indexed status execution

The public trace above deliberately mirrors the proof-facing `GroupView`
semantics. Executing it literally would rebuild the same role-update closure
chain as `resolve`, then repeatedly traverse that chain while authorising
later events. The compiled response instead walks the order once with
`Era.IndexedGroupView`, accumulating both the final indexed view and the
status list. The equality proofs below keep this an implementation change,
not a second semantics. -/

/-- Status against an indexed execution view. -/
def indexedStatusOf (v : IndexedGroupView) (e : Event) : Nat :=
  if indexedAuthorised v e then 0
  else if e.kind ≤ 3 then 1 else 2

/-- Indexed and public status judgements agree exactly. -/
theorem indexedStatusOf_eq (v : IndexedGroupView) (e : Event) :
    indexedStatusOf v e = statusOf (materializeIndexed v) e := by
  unfold indexedStatusOf statusOf
  rw [indexedAuthorised_eq]

/-- Result of one indexed walk: the final view and one status per input
event. Keeping them together avoids replaying the order a second time. -/
structure IndexedTrace where
  view : IndexedGroupView
  statuses : List Nat

/-- Walk an execution order once using balanced-map role reads and writes. -/
def traceIndexed (v : IndexedGroupView) : List Event → IndexedTrace
  | [] => ⟨v, []⟩
  | e :: rest =>
    let status := indexedStatusOf v e
    let tail := traceIndexed (applyEventIndexed v e) rest
    ⟨tail.view, status :: tail.statuses⟩

/-- The indexed trace's final view is exactly the existing public fold. -/
theorem traceIndexed_view : ∀ (l : List Event) (v : IndexedGroupView),
    materializeIndexed (traceIndexed v l).view =
      l.foldl applyEvent (materializeIndexed v) := by
  intro l
  induction l with
  | nil => intro v; rfl
  | cons e rest ih =>
    intro v
    simp only [traceIndexed, List.foldl_cons]
    rw [ih, materialize_applyEventIndexed]

/-- The indexed trace's statuses are exactly the existing public status
walker, entry for entry. -/
theorem traceIndexed_statuses : ∀ (l : List Event) (v : IndexedGroupView),
    (traceIndexed v l).statuses = statusesFrom (materializeIndexed v) l := by
  intro l
  induction l with
  | nil => intro v; rfl
  | cons e rest ih =>
    intro v
    simp only [traceIndexed, statusesFrom]
    rw [ih, indexedStatusOf_eq, materialize_applyEventIndexed]

/-! ## §4. The response, and the entry point -/

/-- The user block: `(user, role)` word pairs, roles read from the resolved
view — `Era.resolve`'s output, verbatim. -/
def roleWords (v : GroupView) : List Nat → List UInt64
  | [] => []
  | u :: us => UInt64.ofNat u :: UInt64.ofNat (v.role u) :: roleWords v us

theorem length_roleWords (v : GroupView) :
    ∀ us : List Nat, (roleWords v us).length = 2 * us.length
  | [] => rfl
  | u :: us => by
    simp only [roleWords, List.length_cons]
    rw [length_roleWords v us]
    omega

/-- The status block: `(eid, status)` word pairs, in execution order. -/
def statusWords : List Event → List Nat → List UInt64
  | [], _ => []
  | _ :: _, [] => []
  | e :: es, s :: ss => UInt64.ofNat e.eid :: UInt64.ofNat s :: statusWords es ss

theorem length_statusWords : ∀ (es : List Event) (ss : List Nat),
    es.length = ss.length → (statusWords es ss).length = 2 * es.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | e :: es, s :: ss, h => by
    simp only [statusWords, List.length_cons]
    rw [length_statusWords es ss (by simpa using h)]
    omega

/-- **The full response, as words** — the decision layer is `Era.resolve`
and `Era.execOrder` *verbatim* (no re-implementation): the started flag and
every role word read the resolved view; the status block walks the
arbitration order. Layout per the contract header. -/
def responseWords (cuts : List Cut) (log : List Event) : List UInt64 :=
  let v := resolve cuts log
  let users := usersOf log
  let order := execOrder cuts log
  (if v.started then 1 else 0)
    :: UInt64.ofNat users.length
    :: UInt64.ofNat order.length
    :: (roleWords v users ++ statusWords order (statusesFrom initView order))

/-- The response is exactly `3 + 2·nu + 2·ns` words. -/
theorem length_responseWords (cuts : List Cut) (log : List Event) :
    (responseWords cuts log).length
      = 3 + 2 * (usersOf log).length + 2 * (execOrder cuts log).length := by
  simp only [responseWords, List.length_cons, List.length_append,
    length_roleWords,
    length_statusWords _ _ (length_statusesFrom initView _).symm]
  omega

/-- Compiled implementation of the full response. Ordering is shared with
the public specification, while view resolution and status production share
one balanced-map execution walk. -/
def responseWordsIndexed (cuts : List Cut) (log : List Event) : List UInt64 :=
  let users := usersOf log
  let order := execOrder cuts log
  let trace := traceIndexed initIndexedView order
  let v := materializeIndexed trace.view
  (if v.started then 1 else 0)
    :: UInt64.ofNat users.length
    :: UInt64.ofNat order.length
    :: (roleWords v users ++ statusWords order trace.statuses)

/-- The one-pass indexed response is byte-for-byte identical at word level to
the public `resolve`/`statusesFrom` specification. -/
theorem responseWordsIndexed_eq_responseWords (cuts : List Cut)
    (log : List Event) :
    responseWordsIndexed cuts log = responseWords cuts log := by
  unfold responseWordsIndexed responseWords
  have hv := traceIndexed_view (execOrder cuts log) initIndexedView
  have hs := traceIndexed_statuses (execOrder cuts log) initIndexedView
  rw [materialize_initIndexedView] at hv hs
  simp only
  rw [show materializeIndexed
        (traceIndexed initIndexedView (execOrder cuts log)).view = resolve cuts log by
      simpa only [resolve] using hv]
  rw [hs]

/-- Compile the response to its proved one-pass balanced-map implementation.
The proof-facing API and every theorem about `responseWords` remain unchanged. -/
@[csimp] theorem responseWords_eq_responseWordsIndexed :
    @responseWords = @responseWordsIndexed := by
  funext cuts log
  exact (responseWordsIndexed_eq_responseWords cuts log).symm

/-- Encode a word list, little-endian, via `Exec.pushWord`. -/
def encodeWords (ws : List UInt64) : ByteArray :=
  ws.foldl pushWord ByteArray.empty

/-- **The replay**: literally decode → resolve/order/trace → encode. The byte
layer's agreement with the decision layer is by construction — this is a
composition, not a re-implementation. -/
def eraReplay (input : ByteArray) : ByteArray :=
  encodeWords (responseWords (decodeCuts input) (decodeEvents input))

/-- The C entry point. Owned `ByteArray` in, owned `ByteArray` out. -/
@[export uwueave_era_resolve]
def eraResolveKernel (input : ByteArray) : ByteArray :=
  eraReplay input

/-! ## §5. Delivery-independence of the whole response

`Era.resolve_same_sets` covers the view; `Era.execOrder_same_sets` covers the
trace's order (and hence, entry by entry, the statuses); `usersOf_same_sets`
covers the roster. Together: the RESPONSE BYTES are a function of the two
sets. This is the theorem the FFI property suite exercises end to end
(`rust/tests/properties.rs`, delivery-order independence through the real
kernel). -/

/-- Membership-equivalent cut lists and event lists produce the same response
words — delivery order, duplication and batching all invisible. -/
theorem responseWords_same_sets {cuts cuts' : List Cut}
    {log log' : List Event} (hc : ∀ c, c ∈ cuts ↔ c ∈ cuts')
    (hl : ∀ e, e ∈ log ↔ e ∈ log') :
    responseWords cuts log = responseWords cuts' log' := by
  unfold responseWords
  rw [resolve_same_sets hc hl, execOrder_same_sets hc hl, usersOf_same_sets hl]

/-- **Delivery-independence at the byte level**: two requests whose decoded
cut and event lists are membership-equivalent get byte-identical responses. -/
theorem eraReplay_same_sets {i₁ i₂ : ByteArray}
    (hc : ∀ c, c ∈ decodeCuts i₁ ↔ c ∈ decodeCuts i₂)
    (hl : ∀ e, e ∈ decodeEvents i₁ ↔ e ∈ decodeEvents i₂) :
    eraReplay i₁ = eraReplay i₂ := by
  unfold eraReplay
  rw [responseWords_same_sets hc hl]

/-! ## §6. Output codec: the word level round-trips (ExecRefine §7 style)

Cheaper than Exec's round trip: every emitted value is a `Nat` pushed as a
u64, so there is no two's-complement leg — word `j` of the response IS
response word `j`. -/

theorem size_foldl_pushWord (ws : List UInt64) :
    ∀ b : ByteArray, (ws.foldl pushWord b).size = b.size + 8 * ws.length := by
  induction ws with
  | nil => intro b; simp
  | cons w t ih =>
    intro b
    rw [List.foldl_cons, ih, size_pushWord, List.length_cons]
    omega

/-- The encoded response is exactly one word per response word. -/
theorem size_encodeWords (ws : List UInt64) :
    (encodeWords ws).size = 8 * ws.length := by
  unfold encodeWords
  rw [size_foldl_pushWord]
  simp

/-- **The size lemma**: the response is exactly `8·(3 + 2·nu + 2·ns)` bytes —
the Rust decoder's refusal condition, proved from this side of the wire. -/
theorem size_eraReplay (input : ByteArray) :
    (eraReplay input).size
      = 8 * (3 + 2 * (usersOf (decodeEvents input)).length
              + 2 * (execOrder (decodeCuts input) (decodeEvents input)).length) := by
  unfold eraReplay
  rw [size_encodeWords, length_responseWords]

theorem getWord_foldl_pushWord_lt (ws : List UInt64) :
    ∀ (b : ByteArray) (i : Nat), 8 * (i + 1) ≤ b.size →
      getWord (ws.foldl pushWord b) i = getWord b i := by
  induction ws with
  | nil => intro b i _; rfl
  | cons w t ih =>
    intro b i h
    rw [List.foldl_cons, ih _ _ (by rw [size_pushWord]; omega),
        getWord_pushWord_lt _ _ h]

theorem getWord_foldl_pushWord (ws : List UInt64) :
    ∀ (b : ByteArray) (w : Nat), b.size = 8 * w →
      ∀ (j : Nat), (hj : j < ws.length) →
        getWord (ws.foldl pushWord b) (w + j) = ws[j] := by
  induction ws with
  | nil => intro b w _ j hj; simp at hj
  | cons x t ih =>
    intro b w hb j hj
    rw [List.foldl_cons]
    match j with
    | 0 =>
      rw [Nat.add_zero,
          getWord_foldl_pushWord_lt t _ _ (by rw [size_pushWord, hb]; omega),
          getWord_pushWord _ _ hb]
      rfl
    | j + 1 =>
      have := ih (pushWord b x) (w + 1)
        (by rw [size_pushWord, hb]; omega) j (by simpa using hj)
      rw [show w + (j + 1) = w + 1 + j by omega, this]
      rfl

/-- Word `j` of an encoded word list is word `j` of the list. -/
theorem getWord_encodeWords (ws : List UInt64) {j : Nat} (hj : j < ws.length) :
    getWord (encodeWords ws) j = ws[j] := by
  unfold encodeWords
  have := getWord_foldl_pushWord ws ByteArray.empty 0 (by simp) j hj
  simpa using this

/-- **Output codec round trip**: reading word `j` of the shipped response
recovers response word `j` exactly. -/
theorem getWord_eraReplay (input : ByteArray) {j : Nat}
    (hj : j < (responseWords (decodeCuts input) (decodeEvents input)).length) :
    getWord (eraReplay input) j
      = (responseWords (decodeCuts input) (decodeEvents input))[j] :=
  getWord_encodeWords _ hj

/-- Header word 0 of the shipped bytes is the started flag of `Era.resolve`
on the decoded input — the view this kernel reports is the theorem-bearing
function, read back through the codec. -/
theorem eraReplay_word0 (input : ByteArray) :
    getWord (eraReplay input) 0
      = if (resolve (decodeCuts input) (decodeEvents input)).started
        then 1 else 0 := by
  rw [getWord_eraReplay input (j := 0) (by rw [length_responseWords]; omega)]
  rfl

/-- Header word 1 is the user count. -/
theorem eraReplay_word1 (input : ByteArray) :
    getWord (eraReplay input) 1
      = UInt64.ofNat (usersOf (decodeEvents input)).length := by
  rw [getWord_eraReplay input (j := 1) (by rw [length_responseWords]; omega)]
  rfl

/-- Header word 2 is the status count — the execution order's length. -/
theorem eraReplay_word2 (input : ByteArray) :
    getWord (eraReplay input) 2
      = UInt64.ofNat
          (execOrder (decodeCuts input) (decodeEvents input)).length := by
  rw [getWord_eraReplay input (j := 2) (by rw [length_responseWords]; omega)]
  rfl

/-! ## §7. The duel, through this kernel's layers

`Era.duelling_admins_resolved` is about `resolve`, which this kernel ships
verbatim; what is new here is the *trace* and the *bytes*. Both pinned on the
paper's Fig. 2 scenario. -/

/-- **The ✗ mark is visible in the trace**: on the pending duel
(`Era.setupCuts`/`Era.duelLog`), the execution order runs e1–e4 applied and
e5 — Bob's demote, unauthorised once Alice's demote executed first —
skipped-unauthorised. The trace names exactly the loser
`duel_pending_verdict` implies. -/
theorem duel_trace_marks_the_skip :
    statusesFrom initView (execOrder setupCuts duelLog) = [0, 0, 0, 0, 1] := by
  decide

/-- The full response of the duel scenario, word for word: started; two
users — Alice (1) an admin (3), Bob (2) a reader (1); five statuses in
execution order, e5's ✗ last. One concrete anchor for the whole layout. -/
theorem duel_response_words :
    responseWords setupCuts duelLog
      = [1, 2, 5, 1, 3, 2, 1, 1, 0, 2, 0, 3, 0, 4, 0, 5, 1] := by
  decide

end Uwueave.EraKernel
