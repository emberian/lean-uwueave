/-
# Uwueave.Era — the ERA protocol core: epoch-resolved arbitration, executable.

`Seams.lean` §1 read ERA through Whittaker's segmentation lens on a miniature
carrier and was explicit about its debt: "ERA's actual protocol — how replicas
*learn* an epoch's arbitration verdict, how an epoch change is proposed and
settled — is not formalized; here the verdict stream is an oracle parameter".
This file pays that debt at miniature scale: the protocol core of ERA (Kegan
Dougal, "ERA: Epoch-Resolved Arbitration for Duelling Admins in Group
Management CRDTs", PaPoC 2026, arXiv:2601.22963), implemented as executable
Lean over the house substrates, with the safety theorems the design rests on.

## The protocol, per the paper

  * **Group state and operations (§3).** Each user holds a role,
    Reader < Writer < Admin. The operations: `join(a)` (any user, no prior
    permission; the FIRST user to join is an Admin, subsequent joiners are
    Readers), `write(a)` (requires Writer or Admin), `promote(a,b,r)` (`a`
    must be Admin; raises `b` to `r`), `demote(a,b,r)` (`a` must be Admin;
    lowers `b` to `r`; self-demotion `a = b` is valid). Authorisation is
    judged *at the point of execution* (§3.2): whether `demote(b,a,·)` is
    authorised depends on whether `demote(a,b,·)` already executed — the
    operations genuinely do not commute, and no encoding makes them commute.
  * **Arbitration (§3.2, §4).** ERA's answer is a deterministic global total
    order — the *execution order* — in which events are executed one by one,
    unauthorised ones skipped (the ✗ marks of the paper's Fig. 2). The order
    is supplied by a mutually trusted *finality arbiter*: a distinguished
    peer that periodically announces its current DAG sources as *epoch
    events* (§4.1), slicing the event set into onion layers. Events are
    ordered **by epoch first**; an event not inside any announced epoch is
    in the *pending epoch* and executes after all others, whatever its
    causal position (§4.1, Figs. 6-7). Within an epoch any deterministic
    tiebreak serves (Fig. 7: "revocation, timestamp, event hash, etc.");
    this file uses the event id, the miniature's stand-in for the hash.
  * **Finality (§2.1, §5).** Once every event of a prefix is inside an
    announced epoch, late-arriving pending events cannot change what that
    prefix executes — finalised events are safe from rollback even if the
    arbiter then disappears (§5.2). That is the finality plain CRDTs lack
    and ERA buys; the price is trust in one peer's announcement stream and
    rollback-ability of the still-pending suffix.

## What is implemented and proved

  * The event vocabulary and execution semantics of §3 (`Event`,
    `authorised`, `applyEvent`), the epoch assignment of §4.1 (`Cut`,
    `epochOf`, `advance`), the execution order (`execOrder`) and the
    arbitration function (`resolve`), all computable over `Nat` ids.
  * **(a) Join laws for free**: the replicated state is `GSet Cut ×
    GSet Event`, both components grow-only; `MergeState` is inherited from
    the product/GSet instances (`inferInstance` — zero new merge proofs),
    and `encode_merge` shows the list-carried transport lands on ⊔.
  * **(b) Arbitration is delivery-independent** (`resolve_same_sets`,
    `same_state_same_view`): replicas holding the same event-set and
    cut-set — any order, duplication, batching — resolve to the SAME view.
    Not because the steps commute (they don't, §3.2) but because `resolve`
    is a function of the sets: it canonicalises into the execution order
    before folding. This is the design choice that makes the theorem true,
    and it is exactly the paper's mechanism: arbitration imposes the order.
  * **(c) Duelling admins get one deterministic survivor**
    (`duelling_admins_resolved`): the paper's Fig. 2 scenario, resolved
    identically at every replica, with a named survivor — the theorem the
    whole feature exists for, and the clash `Authority.lean` proved has no
    coordination-free fix (`sole_admin_not_iconfluent`,
    `duelling_revocations_not_iconfluent`: fail-closed annihilates both).
  * **(d) Epoch order governs execution** (`elt_of_epoch_lt`,
    `elt_final_pending`, `execOrder_split_by`, `resolve_resumes_final`):
    earlier epochs execute first, pending events last; the full view is the
    finalised view with the pending suffix folded on top. **Finality**
    (`final_view_immune`): events still outside every epoch cannot perturb
    the finalised view. `duel_finalised_verdict` shows the arbiter's cut
    placement — never a named winner — flipping the duel's survivor.
  * **(e) §1's membership lifecycle** (§8), carried beside the role codes
    because it provably cannot be carried inside them
    (`departed_indistinguishable_from_stranger`): `traceLife` computes
    invited/member/left alongside the paper's own semantics and
    `traceLife_role` proves that free — the resolved view is `resolve`'s, so
    (a)-(d) stand verbatim. Two doors §3 leaves open are exhibited
    (`departed_rejoins_unchecked`, `promote_admits_nonmember`) and closed by
    the invitation discipline `lifeAuthorised`/`resolveGated`, which refuses
    strictly more than §3 (`lifeAuthorised_refuses_more`), admits the founder
    (`gated_founder_admitted`), and keeps delivery-independence
    (`resolveGated_same_sets`).

## Corrections to `Seams.lean`'s reading, from the paper

  1. Seams modelled the arbiter as a per-epoch *verdict* oracle
     `arb : Nat → Nat` ("epoch e's admin is `arb e`"). The real arbiter
     never names an admin: it announces epoch cuts that only ORDER events
     (§4, §4.1); the survivor is *derived* by deterministic authorised
     execution. "The verdict rides the seam" refines to: the seam carries
     an ordering, and the verdict falls out of it.
  2. Seams' carrier kept a per-replica "current epoch" merged by `max`
     ("a replica never returns to a settled epoch"). ERA has no per-replica
     epoch at all: every replica holds events of all epochs plus a pending
     set, and epoch tags are per-event (least cut naming the event).
  3. Seams' modal reading "coordinate exactly to cross an epoch boundary"
     is Whittaker's lens, not ERA's mechanism: in ERA *nobody coordinates* —
     the boundary is announced unilaterally by a trusted peer, replicas
     never wait (P1, §3), and the cost is trust plus rollback of the
     pending suffix (§5), not an inter-replica coordination event.
  4. Absent from Seams, central to the paper: the pending epoch (§4.1),
     rollback of unfinalised events (§2.1), and within-epoch order still
     mattering (same-epoch admin events do not commute; the tiebreak,
     not a free merge, handles them).

## Not modelled, honestly (and why the arbitration core survives)

  * **The hash DAG**: event ids stand in for hashes; causal predecessors,
    recursive hash linking and equivocation detection (§2) are dropped. No
    uniqueness premise is needed — two distinct events sharing an id are
    still totally ordered by the remaining fields (they would share an
    epoch assignment, the collision analogue).
  * **Epoch assignment from causal closure**: a `Cut` names the events of
    an epoch's closed past *extensionally*; computing that closure from
    announced sources and DAG edges (§4.1, Fig. 6) is the dropped plumbing.
    An event named by several cuts takes the least epoch — so an
    equivocating arbiter (concurrent epochs, §5.1, Fig. 8) degrades to
    deterministic re-ordering, never divergence: `resolve_same_sets` holds
    with no honesty hypothesis. Prefix stability under *cut* growth is
    correspondingly NOT claimed (only `epochOf_mono` and
    `final_view_immune`); the paper accepts the same (detectable
    backdating, §5.1) and answers with signatures and fraud proofs, both
    out of scope here.
  * **Backdating detection (§2.2), signatures, arbiter lists, transparency
    (§5.1), liveness/reliability (P1 as a liveness claim, §5.2), the
    Creator role (§5.3), timestamps** (the within-epoch tiebreak is the
    event id; any strict total order serves the general theorems — the
    concrete verdicts of course depend on the choice, which is the paper's
    own event-based-arbitration caveat, bounded by epoch batching).
  * The paper's per-event `Final`/`Rollback` predicates (Eqs. 1-2) appear
    only in prefix form (`final_view_immune`), not event-by-event.

Arbitration semantics is the paper's; every protocol-semantic choice below
cites its section. `Nat` role codes add `0` ("not a member") to §3's three
roles so membership is explicit; §1's invited/left lifecycle is §8, where the
invitation is a new event kind and the admission rule that reads it is a
second, parallel authorisation predicate — §3's is never touched.
-/
import Uwueave.Catalog
import Std.Data.TreeMap

namespace Uwueave.Era

open Uwueave Uwueave.Catalog

/-! ## §1. Roles and events — the operation vocabulary of the paper's §3 -/

/-- Not a member. Not one of §3's roles: the code for "no role", from which
`join` admits (§3 op 1) and to which a demotion may expel (§1's "left"
membership state, reached only through `demote`'s strictly-lowering rule). -/
def outsider : Nat := 0

/-- Reader — "can read events in the DAG. The lowest level role" (§3). -/
def reader : Nat := 1

/-- Writer — "can write events into the DAG, in addition to Reader" (§3). -/
def writer : Nat := 2

/-- Admin — "can change the role of other users, in addition to Writer" (§3). -/
def admin : Nat := 3

/-- A group-management event. `eid` is the event id — the miniature's stand-in
for the event hash (§2's recursive hash linking is not modelled). `kind` codes
the §3 operation set: `0` join, `1` write, `2` promote, `3` demote. `actor` is
the user performing the operation, `target` the user acted on (= `actor` for
join/write), `role` the role argument of promote/demote (`0` otherwise). -/
structure Event where
  eid    : Nat
  kind   : Nat
  actor  : Nat
  target : Nat
  role   : Nat
  deriving DecidableEq, Repr

theorem Event.ext {a b : Event} (h1 : a.eid = b.eid) (h2 : a.kind = b.kind)
    (h3 : a.actor = b.actor) (h4 : a.target = b.target) (h5 : a.role = b.role) :
    a = b := by
  cases a; cases b; simp_all

/-- `join(a)` — §3 op 1: any user may join, no prior permission. -/
def joinEv (eid a : Nat) : Event := ⟨eid, 0, a, a, 0⟩

/-- `write(a)` — §3 op 2: requires Writer or Admin; no effect on roles. -/
def writeEv (eid a : Nat) : Event := ⟨eid, 1, a, a, 0⟩

/-- `promote(a, b, r)` — §3 op 3: `a` raises `b`'s role to `r`. -/
def promoteEv (eid a b r : Nat) : Event := ⟨eid, 2, a, b, r⟩

/-- `demote(a, b, r)` — §3 op 4: `a` lowers `b`'s role to `r`. -/
def demoteEv (eid a b r : Nat) : Event := ⟨eid, 3, a, b, r⟩

/-! ## §2. Epoch cuts — the arbiter's announcement stream (paper §4.1)

A finality arbiter "periodically announces the event IDs of its current
sources"; each announcement closes an onion layer. A `Cut` `(k, i)` records
"the arbiter's epoch-`k` announcement contains event `i` in its closed past"
— the layer carried extensionally, causal-closure computation dropped (see
the header). An event's epoch is the LEAST epoch naming it: layers are
nested, so an event sits in every layer from its first onward, and Fig. 6
assigns it to that first one (`b₃` is pending though it points into epoch 1;
`d₁` is epoch 2 though it points into epoch 1 — membership of the event
itself, not of its causal past, decides). The least-rule also makes an
equivocating arbiter (Fig. 8) a deterministic re-ordering, never a fork. -/

/-- One arbiter announcement record: `(epoch, event id)`. -/
abbrev Cut := Nat × Nat

/-- Core's `Nat.min_def` is stated via `Min.min`, which does not match the
`Nat.min` applications below; this is the same fact in the spelling `rw` can
find — the `nat_max_def` move of `Catalog.lean`, for `min`. -/
theorem nat_min_def (m n : Nat) : Nat.min m n = if m ≤ n then m else n :=
  Nat.min_def

/-- The epoch of event id `eid` under the announcement records `cuts`: the
least `k` with `(k, eid) ∈ cuts`, or `none` — the *pending epoch* of §4.1 —
if no announcement names it. -/
def epochOf : List Cut → Nat → Option Nat
  | [], _ => none
  | c :: cs, eid =>
    if c.2 = eid then
      match epochOf cs eid with
      | none => some c.1
      | some m => some (Nat.min c.1 m)
    else epochOf cs eid

/-- Balanced eid-keyed index of the least announced epoch. `TreeMap` is a
self-balancing binary search tree, so lookup is logarithmic in the number of
distinct announced ids rather than linear in the cut-list length. -/
abbrev EpochIndex := Std.TreeMap Nat Nat

/-- Build the epoch index once. Processing the tail first mirrors `epochOf`'s
least-epoch fold exactly; `alter` combines repeated ids with `Nat.min`. -/
def epochIndex : List Cut → EpochIndex
  | [] => ∅
  | c :: cs =>
    (epochIndex cs).alter c.2 fun
      | none => some c.1
      | some m => some (Nat.min c.1 m)

/-- Logarithmic lookup in a preprocessed epoch index. -/
def epochLookup (idx : EpochIndex) (eid : Nat) : Option Nat :=
  idx[eid]?

/-- The balanced index is extensionally exact: every lookup returns the same
least epoch (or `none`) as the original list scan. -/
theorem epochLookup_epochIndex (cuts : List Cut) (eid : Nat) :
    epochLookup (epochIndex cuts) eid = epochOf cuts eid := by
  induction cuts with
  | nil => simp [epochIndex, epochLookup, epochOf]
  | cons c cs ih =>
    unfold epochLookup at ih
    by_cases h : c.2 = eid
    · subst eid
      simp [epochIndex, epochLookup, epochOf, ih]
    · rw [epochLookup, epochIndex, Std.TreeMap.getElem?_alter]
      rw [if_neg (fun hc => h (Nat.compare_eq_eq.mp hc)), ih]
      simp [epochOf, h]

/-- Unfolding equation for `epochOf` at a record that names the queried
event: the answer folds the record's epoch into the tail's by `Nat.min`. -/
theorem epochOf_cons_pos {c : Cut} {cs : List Cut} {eid : Nat} (hc : c.2 = eid) :
    epochOf (c :: cs) eid =
      (match epochOf cs eid with
       | none => some c.1
       | some m => some (Nat.min c.1 m)) := by
  simp [epochOf, hc]

/-- Unfolding equation for `epochOf` at a record that does not name the
queried event: the record is invisible. -/
theorem epochOf_cons_neg {c : Cut} {cs : List Cut} {eid : Nat}
    (hc : ¬ c.2 = eid) : epochOf (c :: cs) eid = epochOf cs eid := by
  simp [epochOf, hc]

/-- `epochOf` answers `none` exactly on events no announcement names —
membership-characterisation, `none` half. -/
theorem epochOf_none_iff {eid : Nat} : ∀ {cuts : List Cut},
    epochOf cuts eid = none ↔ ∀ k, ¬ ((k, eid) ∈ cuts) := by
  intro cuts
  induction cuts with
  | nil => simp [epochOf]
  | cons c cs ih =>
    by_cases hc : c.2 = eid
    · have hne : epochOf (c :: cs) eid ≠ none := by
        rw [epochOf_cons_pos hc]
        cases epochOf cs eid <;> simp
      have hmem : (c.1, eid) ∈ c :: cs := by
        have hce : c = (c.1, eid) := by rw [← hc]
        rw [← hce]
        exact List.Mem.head cs
      exact iff_of_false hne (fun h => h c.1 hmem)
    · rw [epochOf_cons_neg hc, ih]
      constructor
      · intro h k hk
        rcases List.mem_cons.mp hk with heq | htl
        · exact absurd (by rw [← heq]) hc
        · exact h k htl
      · intro h k hk
        exact h k (List.Mem.tail c hk)

/-- A `some` answer is an announced record: `epochOf cuts eid = some m`
implies `(m, eid) ∈ cuts` — membership-characterisation, witness half. -/
theorem epochOf_some_mem : ∀ {cuts : List Cut} {eid m : Nat},
    epochOf cuts eid = some m → (m, eid) ∈ cuts := by
  intro cuts
  induction cuts with
  | nil => intro eid m h; simp [epochOf] at h
  | cons c cs ih =>
    intro eid m h
    by_cases hc : c.2 = eid
    · have hce : c = (c.1, eid) := by rw [← hc]
      rw [epochOf_cons_pos hc] at h
      cases hcs : epochOf cs eid with
      | none =>
        simp only [hcs, Option.some.injEq] at h
        rw [← h, ← hce]
        exact List.Mem.head cs
      | some m' =>
        simp only [hcs, Option.some.injEq] at h
        rw [nat_min_def] at h
        split at h
        · rw [← h, ← hce]; exact List.Mem.head cs
        · rw [← h]; exact List.Mem.tail c (ih hcs)
    · rw [epochOf_cons_neg hc] at h
      exact List.Mem.tail c (ih h)

/-- A `some` answer is the LEAST announced epoch: every record naming `eid`
sits at or above it — membership-characterisation, minimality half. -/
theorem epochOf_some_le : ∀ {cuts : List Cut} {eid m k : Nat},
    epochOf cuts eid = some m → (k, eid) ∈ cuts → m ≤ k := by
  intro cuts
  induction cuts with
  | nil => intro _ _ _ _ hk; cases hk
  | cons c cs ih =>
    intro eid m k h hk
    rcases List.mem_cons.mp hk with hck | htl
    · have hc2 : c.2 = eid := by rw [← hck]
      have hc1 : c.1 = k := by rw [← hck]
      rw [epochOf_cons_pos hc2] at h
      cases hcs : epochOf cs eid with
      | none => simp only [hcs, Option.some.injEq] at h; omega
      | some m' =>
        simp only [hcs, Option.some.injEq] at h
        rw [nat_min_def] at h
        split at h <;> omega
    · by_cases hc : c.2 = eid
      · rw [epochOf_cons_pos hc] at h
        cases hcs : epochOf cs eid with
        | none => exact absurd htl (epochOf_none_iff.mp hcs k)
        | some m' =>
          simp only [hcs, Option.some.injEq] at h
          have := ih hcs htl
          rw [nat_min_def] at h
          split at h <;> omega
      · rw [epochOf_cons_neg hc] at h
        exact ih h htl

/-- Epoch assignment is a function of the announcement SET: membership-
equivalent cut lists — any order, duplication, multiplicity — assign every
event the same epoch. The cut-side half of delivery-independence. -/
theorem epochOf_congr {cuts cuts' : List Cut}
    (h : ∀ c, c ∈ cuts ↔ c ∈ cuts') (eid : Nat) :
    epochOf cuts eid = epochOf cuts' eid := by
  cases h1 : epochOf cuts eid with
  | none =>
    cases h2 : epochOf cuts' eid with
    | none => rfl
    | some m =>
      exact absurd ((h _).mpr (epochOf_some_mem h2)) (epochOf_none_iff.mp h1 m)
  | some m =>
    cases h2 : epochOf cuts' eid with
    | none =>
      exact absurd ((h _).mp (epochOf_some_mem h1)) (epochOf_none_iff.mp h2 m)
    | some m' =>
      have hle : m ≤ m' := epochOf_some_le h1 ((h _).mpr (epochOf_some_mem h2))
      have hge : m' ≤ m := epochOf_some_le h2 ((h _).mp (epochOf_some_mem h1))
      rw [Nat.le_antisymm hle hge]

/-- **Epoch advance** — the arbiter's operation (§4.1): announce that the
events `eids` lie in epoch `k`'s closed past. Pure growth of the cut set;
"epochs are triggered based on the number of events in the pending epoch,
but could also be triggered on-demand for non-monotonic events such as
demotions" (§4.1) — the trigger policy is the arbiter's, not modelled. -/
def advance (cuts : List Cut) (k : Nat) (eids : List Nat) : List Cut :=
  cuts ++ eids.map fun i => (k, i)

/-- **Finalisation is monotone information**: once any replica sees `eid`
assigned an epoch, every replica whose cuts extend it sees it assigned — at
the same epoch or lower (lower only if the arbiter equivocated; an honest
arbiter's later layers never re-announce with a smaller epoch). The stable
half of §5.1's "consistency of finalised events relies on the monotonic
creation of epochs". -/
theorem epochOf_mono {cuts cuts' : List Cut} (hsub : ∀ c ∈ cuts, c ∈ cuts')
    {eid m : Nat} (h : epochOf cuts eid = some m) :
    ∃ m', epochOf cuts' eid = some m' ∧ m' ≤ m := by
  have hmem := hsub _ (epochOf_some_mem h)
  cases h' : epochOf cuts' eid with
  | none => exact absurd hmem (epochOf_none_iff.mp h' m)
  | some m' => exact ⟨m', rfl, epochOf_some_le h' hmem⟩

/-! ## §3. The execution order — "events are ordered by their epoch first"

§3.2: *"Arbitration is a global total order of events that all peers will
eventually agree upon."* §4.1: epoch first, pending last; within an epoch a
deterministic tiebreak (Fig. 7) — here the event id, then the remaining
fields so the order is total on all distinct events. The order is realised
by a reducible sorted-insertion specification and a proved compiled
implementation that indexes cuts once, merge-sorts, then deduplicates:
`execOrder` turns any delivery log into THE execution order, and
`sorted_unique` proves that order a function of the event set — which is what
§3.2's "all peers agree" needs. -/

/-- Epoch priority class of an event: `0` if the arbiter has placed it in an
epoch, `1` if it is pending — §4.1's "events not in any epoch are in a
pending epoch which executes after all other epochs, regardless of what the
causal predecessors are". -/
def epri (cuts : List Cut) (e : Event) : Nat :=
  match epochOf cuts e.eid with
  | some _ => 0
  | none => 1

/-- Epoch number of an event (`0` when pending; `epri` already separates the
classes, so the default never collides). -/
def epnum (cuts : List Cut) (e : Event) : Nat :=
  (epochOf cuts e.eid).getD 0

/-- The execution-order comparison — the paper's arbitration order (§3.2,
§4.1), lexicographic: finalised before pending (`epri`), then epoch number
(`epnum`), then event id (the within-epoch tiebreak, Fig. 7's "event hash"),
then the remaining fields (total on distinct events even under id
collision). Within-epoch hash order is gameable in isolation — the paper's
own critique of event-based arbitration — and bounded here exactly as there,
by the epoch layer outranking it. -/
def elt (cuts : List Cut) (a b : Event) : Prop :=
  epri cuts a < epri cuts b ∨ (epri cuts a = epri cuts b ∧
  (epnum cuts a < epnum cuts b ∨ (epnum cuts a = epnum cuts b ∧
  (a.eid < b.eid ∨ (a.eid = b.eid ∧
  (a.kind < b.kind ∨ (a.kind = b.kind ∧
  (a.actor < b.actor ∨ (a.actor = b.actor ∧
  (a.target < b.target ∨ (a.target = b.target ∧
  a.role < b.role)))))))))))

instance (cuts : List Cut) (a b : Event) : Decidable (elt cuts a b) := by
  unfold elt; infer_instance

theorem elt_irrefl (cuts : List Cut) (a : Event) : ¬ elt cuts a a := by
  unfold elt; omega

theorem elt_asymm {cuts : List Cut} {a b : Event}
    (h1 : elt cuts a b) (h2 : elt cuts b a) : False := by
  unfold elt at h1 h2; omega

theorem elt_trans {cuts : List Cut} {a b c : Event}
    (h1 : elt cuts a b) (h2 : elt cuts b c) : elt cuts a c := by
  unfold elt at h1 h2 ⊢; omega

/-- Totality on distinct events: the execution order really is a global
total order (§3.2), with no uniqueness premise on ids. -/
theorem elt_connex (cuts : List Cut) {a b : Event} (h : a ≠ b) :
    elt cuts a b ∨ elt cuts b a := by
  have hf : ¬ (a.eid = b.eid ∧ a.kind = b.kind ∧ a.actor = b.actor ∧
      a.target = b.target ∧ a.role = b.role) := by
    rintro ⟨h1, h2, h3, h4, h5⟩
    exact h (Event.ext h1 h2 h3 h4 h5)
  unfold elt
  omega

theorem epri_congr {cuts cuts' : List Cut} (h : ∀ c, c ∈ cuts ↔ c ∈ cuts')
    (e : Event) : epri cuts e = epri cuts' e := by
  unfold epri; rw [epochOf_congr h e.eid]

theorem epnum_congr {cuts cuts' : List Cut} (h : ∀ c, c ∈ cuts ↔ c ∈ cuts')
    (e : Event) : epnum cuts e = epnum cuts' e := by
  unfold epnum; rw [epochOf_congr h e.eid]

/-- The comparison is a function of the cut SET — membership-equivalent
announcement lists order every pair identically. -/
theorem elt_congr {cuts cuts' : List Cut} (h : ∀ c, c ∈ cuts ↔ c ∈ cuts')
    (a b : Event) : elt cuts a b ↔ elt cuts' a b := by
  unfold elt
  rw [epri_congr h a, epri_congr h b, epnum_congr h a, epnum_congr h b]

/-- **Earlier epoch executes first** (§4.1: "events are then ordered by
their epoch first") — whatever the events' own fields say. -/
theorem elt_of_epoch_lt {cuts : List Cut} {a b : Event} {j k : Nat}
    (ha : epochOf cuts a.eid = some j) (hb : epochOf cuts b.eid = some k)
    (hjk : j < k) : elt cuts a b := by
  have h1 : epri cuts a = 0 := by simp [epri, ha]
  have h2 : epri cuts b = 0 := by simp [epri, hb]
  have h3 : epnum cuts a = j := by simp [epnum, ha]
  have h4 : epnum cuts b = k := by simp [epnum, hb]
  unfold elt; omega

/-- **Finalised executes before pending** (§4.1: the pending epoch "executes
after all other epochs, regardless of what the causal predecessors are"). -/
theorem elt_final_pending {cuts : List Cut} {a b : Event} {j : Nat}
    (ha : epochOf cuts a.eid = some j) (hb : epochOf cuts b.eid = none) :
    elt cuts a b := by
  have h1 : epri cuts a = 0 := by simp [epri, ha]
  have h2 : epri cuts b = 1 := by simp [epri, hb]
  unfold elt; omega

/-- Ordered insertion into an execution order, skipping an exact duplicate —
the reducible reference canonicalisation step. Compiled uses of `execOrder`
are replaced by the proved indexed merge sort below; this definition and its
proofs retain the direct specification that at-least-once delivery must be
exactly as good as exactly-once (the paper's DAG gives this by construction;
the list transport must earn it). -/
def insertE (cuts : List Cut) (e : Event) : List Event → List Event
  | [] => [e]
  | a :: l =>
    if e = a then a :: l
    else if elt cuts e a then e :: a :: l
    else a :: insertE cuts e l

/-- Reflexive closure of the strict arbitration order: the non-strict
comparison consumed by `List.mergeSort`. -/
def ele (cuts : List Cut) (a b : Event) : Prop :=
  a = b ∨ elt cuts a b

/-- Executable spelling of `ele`. Keeping the disjunction at `Bool` avoids an
opaque synthesized `Decidable (ele ...)` in concrete `by decide` examples. -/
def eleb (cuts : List Cut) (a b : Event) : Bool :=
  decide (a = b) || decide (elt cuts a b)

theorem eleb_eq_true_iff {cuts : List Cut} {a b : Event} :
    eleb cuts a b = true ↔ ele cuts a b := by
  simp [eleb, ele, Bool.or_eq_true, decide_eq_true_eq]

/-- Epoch priority read from the preprocessed balanced index. -/
def indexedEpri (idx : EpochIndex) (e : Event) : Nat :=
  match epochLookup idx e.eid with
  | some _ => 0
  | none => 1

/-- Epoch number read from the preprocessed balanced index. -/
def indexedEpnum (idx : EpochIndex) (e : Event) : Nat :=
  (epochLookup idx e.eid).getD 0

/-- Arbitration order using logarithmic epoch-index lookups. -/
def indexedElt (idx : EpochIndex) (a b : Event) : Prop :=
  indexedEpri idx a < indexedEpri idx b ∨ (indexedEpri idx a = indexedEpri idx b ∧
  (indexedEpnum idx a < indexedEpnum idx b ∨ (indexedEpnum idx a = indexedEpnum idx b ∧
  (a.eid < b.eid ∨ (a.eid = b.eid ∧
  (a.kind < b.kind ∨ (a.kind = b.kind ∧
  (a.actor < b.actor ∨ (a.actor = b.actor ∧
  (a.target < b.target ∨ (a.target = b.target ∧
  a.role < b.role)))))))))))

instance (idx : EpochIndex) (a b : Event) : Decidable (indexedElt idx a b) := by
  unfold indexedElt
  infer_instance

/-- Executable non-strict indexed comparator consumed by merge sort. -/
def indexedEleb (idx : EpochIndex) (a b : Event) : Bool :=
  decide (a = b) || decide (indexedElt idx a b)

theorem indexedEpri_epochIndex (cuts : List Cut) (e : Event) :
    indexedEpri (epochIndex cuts) e = epri cuts e := by
  unfold indexedEpri epri
  rw [epochLookup_epochIndex]

theorem indexedEpnum_epochIndex (cuts : List Cut) (e : Event) :
    indexedEpnum (epochIndex cuts) e = epnum cuts e := by
  unfold indexedEpnum epnum
  rw [epochLookup_epochIndex]

/-- Indexed and list-scanning arbitration comparisons are extensionally
identical. -/
theorem indexedElt_epochIndex (cuts : List Cut) (a b : Event) :
    indexedElt (epochIndex cuts) a b ↔ elt cuts a b := by
  unfold indexedElt elt
  rw [indexedEpri_epochIndex cuts a, indexedEpri_epochIndex cuts b,
    indexedEpnum_epochIndex cuts a, indexedEpnum_epochIndex cuts b]

theorem indexedEleb_epochIndex (cuts : List Cut) (a b : Event) :
    indexedEleb (epochIndex cuts) a b = eleb cuts a b := by
  unfold indexedEleb eleb
  rw [decide_eq_decide.mpr (indexedElt_epochIndex cuts a b)]

theorem indexedEleb_eq_true_iff {cuts : List Cut} {a b : Event} :
    indexedEleb (epochIndex cuts) a b = true ↔ ele cuts a b := by
  rw [indexedEleb_epochIndex]
  exact eleb_eq_true_iff

/-- Tail of a consecutive-duplicate pass, remembering the last event emitted. -/
def dedupSortedFrom (prev : Event) : List Event → List Event
  | [] => []
  | a :: rest =>
    if prev = a then dedupSortedFrom prev rest
    else a :: dedupSortedFrom a rest

/-- Remove consecutive duplicate events. Merge sort puts equal events in one
run, so this linear pass is enough to canonicalise at-least-once delivery. -/
def dedupSorted : List Event → List Event
  | [] => []
  | a :: rest => a :: dedupSortedFrom a rest

/-- Merge-sort implementation of the execution order: first index `c` cuts in
a balanced tree, sort `n` events with logarithmic index lookups, then remove
each run of exact duplicates. Worst-case time is
`O(c log(c+1) + n log n log(c+1) + n)` and auxiliary space is `O(c+n)`;
the repeated linear cut scan is gone. -/
def execOrderMerge (cuts : List Cut) (log : List Event) : List Event :=
  let idx := epochIndex cuts
  dedupSorted (log.mergeSort (indexedEleb idx))

/-- **The execution order** of a delivery log, as the reducible specification
used by proofs and concrete `by decide` regression theorems. The proved
`execOrder_eq_execOrderMerge` compiler substitution below replaces this
quadratic specification with `execOrderMerge` in executable kernels.
Everything the protocol decides — who wins a duel included — is decided by
folding `applyEvent` over THIS canonical list. -/
def execOrder (cuts : List Cut) (log : List Event) : List Event :=
  log.foldr (insertE cuts) []

theorem mem_insertE {cuts : List Cut} {e b : Event} :
    ∀ {l : List Event}, b ∈ insertE cuts e l ↔ b = e ∨ b ∈ l := by
  intro l
  induction l with
  | nil => simp [insertE]
  | cons a t ih =>
    by_cases h1 : e = a
    · simp only [insertE, if_pos h1]
      constructor
      · intro hmem; exact Or.inr hmem
      · rintro (rfl | hmem)
        · rw [h1]; exact List.Mem.head t
        · exact hmem
    · by_cases h2 : elt cuts e a
      · simp only [insertE, if_neg h1, if_pos h2]
        constructor
        · intro hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact Or.inl rfl
          · exact Or.inr hmem
        · rintro (rfl | hmem)
          · exact List.Mem.head _
          · exact List.Mem.tail _ hmem
      · simp only [insertE, if_neg h1, if_neg h2]
        constructor
        · intro hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact Or.inr (List.Mem.head t)
          · rcases ih.mp hmem with h' | h'
            · exact Or.inl h'
            · exact Or.inr (List.Mem.tail a h')
        · rintro (rfl | hmem)
          · exact List.Mem.tail a (ih.mpr (Or.inl rfl))
          · rcases List.mem_cons.mp hmem with rfl | h'
            · exact List.Mem.head _
            · exact List.Mem.tail _ (ih.mpr (Or.inr h'))

theorem mem_cons_dedupSortedFrom {b : Event} :
    ∀ (prev : Event) (l : List Event),
      b ∈ prev :: dedupSortedFrom prev l ↔ b ∈ prev :: l := by
  intro prev l
  induction l generalizing prev with
  | nil => simp [dedupSortedFrom]
  | cons a t ih =>
    by_cases h : prev = a
    · subst a
      simpa [dedupSortedFrom] using ih prev
    · simp only [dedupSortedFrom, if_neg h]
      simp only [List.mem_cons]
      exact or_congr Iff.rfl (by simpa only [List.mem_cons] using ih a)

theorem mem_dedupSorted {b : Event} {l : List Event} :
    b ∈ dedupSorted l ↔ b ∈ l := by
  cases l with
  | nil => simp [dedupSorted]
  | cons a t =>
    exact mem_cons_dedupSortedFrom a t

theorem mem_execOrderMerge {cuts : List Cut} {b : Event} {log : List Event} :
    b ∈ execOrderMerge cuts log ↔ b ∈ log := by
  simp [execOrderMerge, mem_dedupSorted]

theorem mem_execOrder {cuts : List Cut} {b : Event} :
    ∀ {log : List Event}, b ∈ execOrder cuts log ↔ b ∈ log := by
  intro log
  induction log with
  | nil => simp [execOrder]
  | cons e t ih =>
    show b ∈ insertE cuts e (execOrder cuts t) ↔ b ∈ e :: t
    rw [mem_insertE, ih]
    exact List.mem_cons.symm

theorem pairwise_insertE {cuts : List Cut} {e : Event} :
    ∀ {l : List Event}, l.Pairwise (elt cuts) →
      (insertE cuts e l).Pairwise (elt cuts) := by
  intro l
  induction l with
  | nil =>
    intro _
    exact List.Pairwise.cons (fun b hb => by cases hb) List.Pairwise.nil
  | cons a t ih =>
    intro hp
    cases hp with
    | cons ha ht =>
      by_cases h1 : e = a
      · simp only [insertE, if_pos h1]
        exact List.Pairwise.cons ha ht
      · by_cases h2 : elt cuts e a
        · simp only [insertE, if_neg h1, if_pos h2]
          refine List.Pairwise.cons ?_ (List.Pairwise.cons ha ht)
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hbt
          · exact h2
          · exact elt_trans h2 (ha b hbt)
        · simp only [insertE, if_neg h1, if_neg h2]
          refine List.Pairwise.cons ?_ (ih ht)
          intro b hb
          rcases mem_insertE.mp hb with rfl | hbt
          · rcases elt_connex cuts h1 with h | h
            · exact absurd h h2
            · exact h
          · exact ha b hbt

/-- Every specification execution order is sorted by the arbitration order. -/
theorem pairwise_execOrder (cuts : List Cut) :
    ∀ log : List Event, (execOrder cuts log).Pairwise (elt cuts)
  | [] => List.Pairwise.nil
  | _ :: t => pairwise_insertE (pairwise_execOrder cuts t)

theorem ele_trans {cuts : List Cut} {a b c : Event}
    (hab : ele cuts a b) (hbc : ele cuts b c) : ele cuts a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · exact Or.inr (elt_trans hab hbc)

theorem ele_total (cuts : List Cut) (a b : Event) :
    ele cuts a b ∨ ele cuts b a := by
  by_cases h : a = b
  · exact Or.inl (Or.inl h)
  · rcases elt_connex cuts h with hab | hba
    · exact Or.inl (Or.inr hab)
    · exact Or.inr (Or.inr hba)

/-- Removing runs from a non-strictly sorted list yields a strictly sorted
list. Totality of `elt` on distinct events makes equal events contiguous. -/
theorem pairwise_cons_dedupSortedFrom {cuts : List Cut} :
    ∀ (prev : Event) (l : List Event), (prev :: l).Pairwise (ele cuts) →
      (prev :: dedupSortedFrom prev l).Pairwise (elt cuts) := by
  intro prev l
  induction l generalizing prev with
  | nil => intro _; exact List.Pairwise.cons (fun b hb => by cases hb) List.Pairwise.nil
  | cons a t ih =>
    intro hp
    cases hp with
    | cons hprev htail =>
      by_cases h : prev = a
      · subst a
        rw [dedupSortedFrom, if_pos rfl]
        exact ih prev htail
      · rw [dedupSortedFrom, if_neg h]
        refine List.Pairwise.cons ?_ (ih a htail)
        intro b hb
        have hb' : b ∈ a :: t := (mem_cons_dedupSortedFrom a t).mp hb
        have hpa : elt cuts prev a :=
          (hprev a (List.Mem.head t)).resolve_left h
        have hne : prev ≠ b := by
          intro hpb
          subst b
          rcases List.mem_cons.mp hb' with hpa' | hpt
          · exact h hpa'
          · have haprev : ele cuts a prev := by
              cases htail with
              | cons ha _ => exact ha prev hpt
            rcases haprev with haprev | haprev
            · exact h haprev.symm
            · exact (elt_asymm hpa haprev).elim
        exact (hprev b hb').resolve_left hne

theorem pairwise_dedupSorted {cuts : List Cut} {l : List Event}
    (h : l.Pairwise (ele cuts)) :
    (dedupSorted l).Pairwise (elt cuts) := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons a t => exact pairwise_cons_dedupSortedFrom a t h

/-- Every merge-sort implementation order is sorted by the arbitration order. -/
theorem pairwise_execOrderMerge (cuts : List Cut) (log : List Event) :
    (execOrderMerge cuts log).Pairwise (elt cuts) := by
  unfold execOrderMerge
  apply pairwise_dedupSorted
  apply (List.pairwise_mergeSort
    (le := indexedEleb (epochIndex cuts)) ?_ ?_ log).imp
  · intro a b h
    exact indexedEleb_eq_true_iff.mp h
  · intro a b c hab hbc
    exact indexedEleb_eq_true_iff.mpr
      (ele_trans (indexedEleb_eq_true_iff.mp hab)
        (indexedEleb_eq_true_iff.mp hbc))
  · intro a b
    rw [Bool.or_eq_true]
    rcases ele_total cuts a b with hab | hba
    · exact Or.inl (indexedEleb_eq_true_iff.mpr hab)
    · exact Or.inr (indexedEleb_eq_true_iff.mpr hba)

theorem pairwise_mono {R S : Event → Event → Prop}
    (h : ∀ a b, R a b → S a b) :
    ∀ {l : List Event}, l.Pairwise R → l.Pairwise S := by
  intro l hp
  induction hp with
  | nil => exact List.Pairwise.nil
  | cons ha _ ih => exact List.Pairwise.cons (fun b hb => h _ _ (ha b hb)) ih

theorem pairwise_append_of {R : Event → Event → Prop} :
    ∀ {l₁ l₂ : List Event}, l₁.Pairwise R → l₂.Pairwise R →
      (∀ a ∈ l₁, ∀ b ∈ l₂, R a b) → (l₁ ++ l₂).Pairwise R := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ h2 _; exact h2
  | cons a t ih =>
    intro l₂ h1 h2 hcross
    cases h1 with
    | cons ha ht =>
      refine List.Pairwise.cons ?_
        (ih ht h2 (fun x hx b hb => hcross x (List.Mem.tail a hx) b hb))
      intro b hb
      rcases List.mem_append.mp hb with h | h
      · exact ha b h
      · exact hcross a (List.Mem.head t) b h

/-- **Sorted lists are canonical**: two lists sorted by the (irreflexive,
asymmetric) arbitration order with the same members are EQUAL. This is the
theorem that turns "sort your local DAG" (§3.2) into "all peers agree": the
execution order is a function of the event set, however it arrived. -/
theorem sorted_unique {cuts : List Cut} :
    ∀ {l l' : List Event}, l.Pairwise (elt cuts) → l'.Pairwise (elt cuts) →
      (∀ b, b ∈ l ↔ b ∈ l') → l = l' := by
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
            apply Classical.byContradiction
            intro hne
            have h1 : a ∈ a' :: t' := (hmem a).mp (List.Mem.head t)
            have h2 : a' ∈ a :: t := (hmem a').mpr (List.Mem.head t')
            rcases List.mem_cons.mp h1 with h | h
            · exact hne h
            · rcases List.mem_cons.mp h2 with h' | h'
              · exact hne h'.symm
              · exact elt_asymm (ha' a h) (ha a' h')
          subst heq
          have hmem' : ∀ b, b ∈ t ↔ b ∈ t' := by
            intro b
            constructor
            · intro hb
              rcases List.mem_cons.mp ((hmem b).mp (List.Mem.tail a hb))
                with rfl | h
              · exact absurd (ha b hb) (elt_irrefl cuts b)
              · exact h
            · intro hb
              rcases List.mem_cons.mp ((hmem b).mpr (List.Mem.tail a hb))
                with rfl | h
              · exact absurd (ha' b hb) (elt_irrefl cuts b)
              · exact h
          rw [ih ht ht' hmem']

/-- The merge-sort implementation computes exactly the canonical execution
order specification: both are strictly sorted and have exactly the log's
members. -/
theorem execOrder_eq_execOrderMerge_apply (cuts : List Cut) (log : List Event) :
    execOrder cuts log = execOrderMerge cuts log := by
  refine sorted_unique (pairwise_execOrder cuts log)
    (pairwise_execOrderMerge cuts log) ?_
  intro b
  rw [mem_execOrder, mem_execOrderMerge]

/-- Compile every `execOrder` call to the proved `O(n log n)` merge-sort
implementation. This is the same proof-carrying compiler-substitution pattern
Lean core uses for `List.mergeSort`'s own efficient runtime implementation. -/
@[csimp] theorem execOrder_eq_execOrderMerge : @execOrder = @execOrderMerge := by
  funext cuts log
  exact execOrder_eq_execOrderMerge_apply cuts log

/-- The execution order is a function of the two SETS — cut records and
events — with delivery order, duplication and multiplicity all invisible.
`sorted_unique` on the two computed orders, with the cut side carried
through `elt_congr`. -/
theorem execOrder_same_sets {cuts cuts' : List Cut} {log log' : List Event}
    (hc : ∀ c, c ∈ cuts ↔ c ∈ cuts') (hl : ∀ e, e ∈ log ↔ e ∈ log') :
    execOrder cuts log = execOrder cuts' log' := by
  refine sorted_unique (pairwise_execOrder cuts log) ?_ ?_
  · exact pairwise_mono (fun a b hab => (elt_congr hc a b).mpr hab)
      (pairwise_execOrder cuts' log')
  · intro b
    rw [mem_execOrder, mem_execOrder]
    exact hl b

/-! ## §4. Execution — authorisation at the point of execution (paper §3)

The materialised view is computed by executing events in the execution
order, skipping unauthorised ones — Fig. 2's annotation discipline: "each
event's validity is contingent on the other not having executed first"
(§3.2). Authorisation safety (P2) is by construction: the fold is guarded,
so an event that lacks permission at its execution point is an exact no-op
(`applyEvent_unauthorised`). -/

/-- The materialised group view: `started` records whether any join has
executed (so §3's "the first user to join is an Admin" is decidable), and
`role` assigns every user a role code (`outsider` = not a member). Derived
state in the `Move.lean` sense: recomputed from the replicated sets, never
itself replicated. -/
structure GroupView where
  started : Bool
  role : Nat → Nat

/-- The empty group: nobody has joined, everybody an outsider. -/
def initView : GroupView := ⟨false, fun _ => outsider⟩

/-- Authorisation at the point of execution, §3's rules verbatim:
join — any user not already a member (op 1; re-join is a no-op);
write — Writer or Admin (op 2);
promote — actor is Admin, and the move strictly RAISES the target within
§3's role set (op 3: "increases the role", capped at Admin);
demote — actor is Admin, and the move strictly LOWERS the target (op 4:
"decreases the role"; `b` may hold any role, so self-demotion is valid,
and lowering to `outsider` is expulsion — §1's "left"). -/
def authorised (v : GroupView) (e : Event) : Bool :=
  match e.kind with
  | 0 => decide (v.role e.actor = outsider)
  | 1 => decide (writer ≤ v.role e.actor)
  | 2 => decide (v.role e.actor = admin) && decide (v.role e.target < e.role)
          && decide (e.role ≤ admin)
  | 3 => decide (v.role e.actor = admin) && decide (e.role < v.role e.target)
  | _ => false

/-- One execution step: apply the event if authorised, else skip it exactly
(Fig. 2's ✗). Join makes the first joiner Admin and every later joiner a
Reader (§3 op 1); promote/demote write the argument role to the target;
write touches no role. -/
def applyEvent (v : GroupView) (e : Event) : GroupView :=
  if authorised v e then
    match e.kind with
    | 0 => { started := true,
             role := fun u => if u = e.actor
               then (if v.started then reader else admin) else v.role u }
    | 2 => { v with role := fun u => if u = e.target then e.role else v.role u }
    | 3 => { v with role := fun u => if u = e.target then e.role else v.role u }
    | _ => v
  else v

/-- An unauthorised event is an exact no-op on the view — authorisation
safety (P2) at the step level, by construction. -/
theorem applyEvent_unauthorised {v : GroupView} {e : Event}
    (h : authorised v e = false) : applyEvent v e = v := by
  simp [applyEvent, h]

/-! ### Indexed execution

`GroupView.role` is the public mathematical interface, but repeated updates to
that function form a closure chain. The executable fold below instead keeps a
balanced finite map and materialises the same role function only at its
boundary. -/

/-- Balanced finite role map used only while executing an event order. Missing
users have the public default role `outsider`. -/
abbrev RoleIndex := Std.TreeMap Nat Nat

/-- Execution-side group view with logarithmic role reads and writes. -/
structure IndexedGroupView where
  started : Bool
  roles : RoleIndex

/-- Read a role from the indexed view, defaulting to `outsider`. -/
def indexedRole (v : IndexedGroupView) (u : Nat) : Nat :=
  v.roles[u]?.getD outsider

/-- Materialise the public proof-facing view from an indexed execution view. -/
def materializeIndexed (v : IndexedGroupView) : GroupView :=
  ⟨v.started, indexedRole v⟩

/-- Empty indexed view. -/
def initIndexedView : IndexedGroupView := ⟨false, ∅⟩

/-- Update one role in logarithmic time. -/
def setIndexedRole (v : IndexedGroupView) (u r : Nat) : IndexedGroupView :=
  { v with roles := v.roles.insert u r }

theorem indexedRole_set (v : IndexedGroupView) (u r x : Nat) :
    indexedRole (setIndexedRole v u r) x =
      if x = u then r else indexedRole v x := by
  unfold indexedRole setIndexedRole
  rw [Std.TreeMap.getElem?_insert]
  by_cases h : x = u
  · subst u
    simp
  · have hc : compare u x ≠ Ordering.eq := by
      intro heq
      exact h (Nat.compare_eq_eq.mp heq).symm
    simp [h, hc]

theorem materialize_initIndexedView :
    materializeIndexed initIndexedView = initView := by
  unfold materializeIndexed initIndexedView initView
  congr

theorem materialize_setIndexedRole (v : IndexedGroupView) (u r : Nat) :
    materializeIndexed (setIndexedRole v u r) =
      { materializeIndexed v with
        role := fun x => if x = u then r else (materializeIndexed v).role x } := by
  cases v
  unfold materializeIndexed
  congr
  funext x
  exact indexedRole_set _ u r x

theorem materialize_setIndexedStarted (v : IndexedGroupView) (b : Bool) :
    materializeIndexed { v with started := b } =
      { materializeIndexed v with started := b } := by
  rfl

/-- Authorisation against the indexed role map; branch-for-branch identical
to public `authorised`. -/
def indexedAuthorised (v : IndexedGroupView) (e : Event) : Bool :=
  match e.kind with
  | 0 => decide (indexedRole v e.actor = outsider)
  | 1 => decide (writer ≤ indexedRole v e.actor)
  | 2 => decide (indexedRole v e.actor = admin) &&
      decide (indexedRole v e.target < e.role) && decide (e.role ≤ admin)
  | 3 => decide (indexedRole v e.actor = admin) &&
      decide (e.role < indexedRole v e.target)
  | _ => false

theorem indexedAuthorised_eq (v : IndexedGroupView) (e : Event) :
    indexedAuthorised v e = authorised (materializeIndexed v) e := by
  rfl

/-- One indexed execution step. Role updates are balanced-tree inserts rather
than one more function-closure frame. -/
def applyEventIndexed (v : IndexedGroupView) (e : Event) : IndexedGroupView :=
  if indexedAuthorised v e then
    match e.kind with
    | 0 => { setIndexedRole v e.actor (if v.started then reader else admin) with
             started := true }
    | 2 => setIndexedRole v e.target e.role
    | 3 => setIndexedRole v e.target e.role
    | _ => v
  else v

/-- One indexed step materialises to exactly the public closure-based step. -/
theorem materialize_applyEventIndexed (v : IndexedGroupView) (e : Event) :
    materializeIndexed (applyEventIndexed v e) =
      applyEvent (materializeIndexed v) e := by
  unfold applyEventIndexed applyEvent
  rw [indexedAuthorised_eq]
  by_cases h : authorised (materializeIndexed v) e
  · rw [if_pos h, if_pos h]
    split
    · rw [materialize_setIndexedStarted, materialize_setIndexedRole]
      simp [materializeIndexed]
      funext x
      rfl
    · exact materialize_setIndexedRole v e.target e.role
    · exact materialize_setIndexedRole v e.target e.role
    · rfl
  · rw [if_neg h, if_neg h]

/-- **The arbitration function**: resolve a delivery log against the
arbiter's announcements — canonicalise into the execution order, then
execute with authorisation checking. This composition IS ERA (§3.2 + §4.1):
the epoch layer orders, the guarded fold arbitrates. -/
def resolve (cuts : List Cut) (log : List Event) : GroupView :=
  (execOrder cuts log).foldl applyEvent initView

/-- Materialising after an indexed fold is exactly the existing public fold. -/
theorem materialize_foldl_applyEventIndexed :
    ∀ (l : List Event) (v : IndexedGroupView),
      materializeIndexed (l.foldl applyEventIndexed v) =
        l.foldl applyEvent (materializeIndexed v) := by
  intro l
  induction l with
  | nil => intro v; rfl
  | cons e t ih =>
    intro v
    simp only [List.foldl_cons]
    rw [ih, materialize_applyEventIndexed]

/-- Execution-side implementation of `resolve`: the same order and guarded
semantics, with a balanced role map throughout the fold. -/
def resolveIndexed (cuts : List Cut) (log : List Event) : GroupView :=
  materializeIndexed
    ((execOrder cuts log).foldl applyEventIndexed initIndexedView)

/-- The indexed execution computes exactly the public arbitration function. -/
theorem resolveIndexed_eq_resolve (cuts : List Cut) (log : List Event) :
    resolveIndexed cuts log = resolve cuts log := by
  unfold resolveIndexed resolve
  rw [materialize_foldl_applyEventIndexed, materialize_initIndexedView]

/-- Compile `resolve` to the proved balanced-map fold. For `n` executed events
and `u` users, role reads and writes are `O(log(u+1))` rather than traversing
an update-closure chain of depth `O(n)`. -/
@[csimp] theorem resolve_eq_resolveIndexed : @resolve = @resolveIndexed := by
  funext cuts log
  exact (resolveIndexed_eq_resolve cuts log).symm

/-! ## §5. Delivery-independence and the CRDT join

The safety half of eventual agreement (P3's substrate): the resolved view is
a function of WHAT was delivered, never of HOW. Note the mechanism — the
steps do NOT commute (§3.2 is explicit that they cannot), so this is not the
`Automata.exec_same_letters` route; it is the set-function route, which is
the protocol's own: impose the order first, then fold. -/

/-- **Same sets, same view** — the epoch-arbitration safety theorem. Two
replicas holding membership-equivalent cut lists and event lists (any
order, any duplication, any batching on both) resolve to the SAME group
view. §3.2's "a global total order of events that all peers will eventually
agree upon", as a theorem about the implementation. -/
theorem resolve_same_sets {cuts cuts' : List Cut} {log log' : List Event}
    (hc : ∀ c, c ∈ cuts ↔ c ∈ cuts') (hl : ∀ e, e ∈ log ↔ e ∈ log') :
    resolve cuts log = resolve cuts' log' := by
  unfold resolve
  rw [execOrder_same_sets hc hl]

/-- Delivery order of event batches is invisible — commutativity of the
transport, an instance of `resolve_same_sets`. -/
theorem resolve_comm (cuts : List Cut) (l₁ l₂ : List Event) :
    resolve cuts (l₁ ++ l₂) = resolve cuts (l₂ ++ l₁) :=
  resolve_same_sets (fun _ => Iff.rfl)
    (fun e => by rw [List.mem_append, List.mem_append]; exact Or.comm)

/-- Re-delivering a whole batch is invisible — idempotence of the
transport, an instance of `resolve_same_sets`. -/
theorem resolve_idem (cuts : List Cut) (l : List Event) :
    resolve cuts (l ++ l) = resolve cuts l :=
  resolve_same_sets (fun _ => Iff.rfl)
    (fun e => by rw [List.mem_append]; exact ⟨fun h => h.elim id id, Or.inl⟩)

/-- Batch grouping is invisible — associativity of the transport, free
because list append is associative on the nose. -/
theorem resolve_assoc (cuts : List Cut) (l₁ l₂ l₃ : List Event) :
    resolve cuts (l₁ ++ l₂ ++ l₃) = resolve cuts (l₁ ++ (l₂ ++ l₃)) := by
  rw [List.append_assoc]

/-- Re-delivering one event the log already holds is invisible — the
per-event idempotence a hash-DAG transport gives by construction. -/
theorem resolve_redeliver (cuts : List Cut) {e : Event} {l : List Event}
    (he : e ∈ l) : resolve cuts (e :: l) = resolve cuts l :=
  resolve_same_sets (fun _ => Iff.rfl) (fun b => by
    rw [List.mem_cons]
    exact ⟨fun h => h.elim (fun hb => by rw [hb]; exact he) id, Or.inr⟩)

/-- The replicated state proper: grow-only cut records and grow-only
events. Both substrates are monotone — the paper's DAG accumulates events,
the arbiter's announcement stream accumulates layers — so the join is
inherited entirely from the `GSet`/product lifts: **zero new merge proofs**
(join laws comm/assoc/idem all come from `Catalog.instMergeStateGSet` and
`Uwueave.instMergeStateProd`). -/
abbrev EraState := GSet Cut × GSet Event

example : MergeState EraState := inferInstance

/-- `decide` distributes over disjunction — stated locally because the core
spelling varies; one `by_cases` pair. -/
theorem decide_or' {p q : Prop} [Decidable p] [Decidable q] :
    decide (p ∨ q) = (decide p || decide q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- The cut list, as the grow-only set it transports. -/
def cutSet (cuts : List Cut) : GSet Cut := fun c => decide (c ∈ cuts)

/-- The event log, as the grow-only set it transports. -/
def eventSet (log : List Event) : GSet Event := fun e => decide (e ∈ log)

/-- A replica's full replicated state from its lists. -/
def encode (cuts : List Cut) (log : List Event) : EraState :=
  (cutSet cuts, eventSet log)

/-- List concatenation transports to the lattice join: syncing two replicas'
lists IS merging their `EraState`s. With `resolve_same_sets` this closes the
loop — the list layer is a faithful transport for the CRDT state. -/
theorem encode_merge (cuts cuts' : List Cut) (log log' : List Event) :
    encode cuts log ⊔ encode cuts' log'
      = encode (cuts ++ cuts') (log ++ log') := by
  show (cutSet cuts ⊔ cutSet cuts', eventSet log ⊔ eventSet log')
      = (cutSet (cuts ++ cuts'), eventSet (log ++ log'))
  have h1 : cutSet cuts ⊔ cutSet cuts' = cutSet (cuts ++ cuts') := by
    funext c
    show (decide (c ∈ cuts) || decide (c ∈ cuts')) = decide (c ∈ cuts ++ cuts')
    rw [← decide_or']
    exact decide_eq_decide.mpr List.mem_append.symm
  have h2 : eventSet log ⊔ eventSet log' = eventSet (log ++ log') := by
    funext e
    show (decide (e ∈ log) || decide (e ∈ log')) = decide (e ∈ log ++ log')
    rw [← decide_or']
    exact decide_eq_decide.mpr List.mem_append.symm
  rw [h1, h2]

/-- **Strong eventual consistency, safety half, against the CRDT state**:
replicas whose replicated `EraState`s are equal resolve to the same view —
`resolve` is well-defined on the lattice, not just on lists. -/
theorem same_state_same_view {cuts cuts' : List Cut} {log log' : List Event}
    (h : encode cuts log = encode cuts' log') :
    resolve cuts log = resolve cuts' log' := by
  have hc : ∀ c, c ∈ cuts ↔ c ∈ cuts' := by
    intro c
    have hfst : decide (c ∈ cuts) = decide (c ∈ cuts') :=
      congrFun (congrArg Prod.fst h) c
    exact decide_eq_decide.mp hfst
  have hl : ∀ e, e ∈ log ↔ e ∈ log' := by
    intro e
    have hsnd : decide (e ∈ log) = decide (e ∈ log') :=
      congrFun (congrArg Prod.snd h) e
    exact decide_eq_decide.mp hsnd
  exact resolve_same_sets hc hl

/-! ## §6. Epoch layering and finality (paper §2.1, §4.1, §5)

"Events are then ordered by their epoch first, thus finalising the
execution order" (§4.1); "if the finality arbiter is unreachable, finalised
events are safe from being rolled back, but no other events will be
finalised" (§6, discussed §5.2). Here: the execution order splits into the
finalised prefix and the pending suffix, the full view resumes from the
finalised view, and fresh pending events cannot perturb it. -/

/-- Has the arbiter placed this event in an epoch? (`false` = pending.) -/
def finalized (cuts : List Cut) (e : Event) : Bool :=
  (epochOf cuts e.eid).isSome

/-- Generic split of the execution order along a downward-closed predicate:
if everything satisfying `p` orders before everything refuting it, the
execution order is the `p`-part followed by the rest. Proved by
`sorted_unique` — both sides are sorted with the same members. -/
theorem execOrder_split_by (cuts : List Cut) (p : Event → Bool)
    (hcross : ∀ a b : Event, p a = true → p b = false → elt cuts a b)
    (log : List Event) :
    execOrder cuts log
      = execOrder cuts (log.filter p)
        ++ execOrder cuts (log.filter fun e => !p e) := by
  refine sorted_unique (pairwise_execOrder cuts log) ?_ ?_
  · refine pairwise_append_of (pairwise_execOrder cuts _)
      (pairwise_execOrder cuts _) ?_
    intro a haf b hbp
    have ha := (List.mem_filter.mp (mem_execOrder.mp haf)).2
    have hb := (List.mem_filter.mp (mem_execOrder.mp hbp)).2
    simp only [Bool.not_eq_true'] at hb
    exact hcross a b ha hb
  · intro b
    rw [mem_execOrder, List.mem_append, mem_execOrder, mem_execOrder]
    cases hb : p b
    · simp [List.mem_filter, hb]
    · simp [List.mem_filter, hb]

/-- The finalised/pending split satisfies the cross condition: every
finalised event orders before every pending one (§4.1). -/
theorem finalized_cross (cuts : List Cut) (a b : Event)
    (ha : finalized cuts a = true) (hb : finalized cuts b = false) :
    elt cuts a b := by
  unfold finalized at ha hb
  cases h1 : epochOf cuts a.eid with
  | none => rw [h1] at ha; simp at ha
  | some j =>
    cases h2 : epochOf cuts b.eid with
    | some k => rw [h2] at hb; simp at hb
    | none => exact elt_final_pending h1 h2

/-- The view at the finality boundary: execute ONLY the events the arbiter
has placed in epochs. This is the state §2.1 calls final — what no missed
concurrent event can roll back. -/
def resolveFinal (cuts : List Cut) (log : List Event) : GroupView :=
  (execOrder cuts (log.filter (finalized cuts))).foldl applyEvent initView

/-- **The full view resumes from the finalised view**: resolve = execute the
finalised prefix, then fold the pending suffix on top. Cross-epoch
supersession in executable form — pending (and by `elt_of_epoch_lt`,
later-epoch) events act on the settled state of earlier layers, never
before it. -/
theorem resolve_resumes_final (cuts : List Cut) (log : List Event) :
    resolve cuts log
      = (execOrder cuts (log.filter fun e => !finalized cuts e)).foldl
          applyEvent (resolveFinal cuts log) := by
  unfold resolve resolveFinal
  rw [execOrder_split_by cuts (finalized cuts) (finalized_cross cuts) log,
    List.foldl_append]

theorem filter_nil_of_false {p : Event → Bool} :
    ∀ {l : List Event}, (∀ e ∈ l, p e = false) → l.filter p = [] := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have ha := h a (List.Mem.head t)
    rw [List.filter_cons, ha, if_neg (by decide)]
    exact ih fun e he => h e (List.Mem.tail a he)

/-- **Finality — the rollback-immunity theorem** (§2.1's `Final`, §5.2, in
prefix form): delivering any batch of still-pending events changes NOTHING
about the finalised view. Concurrent events the arbiter has not blessed
cannot roll back a finalised prefix; if the arbiter vanishes, what was
finalised stays safe (and nothing new finalises — liveness, out of scope). -/
theorem final_view_immune (cuts : List Cut) (log fresh : List Event)
    (hfresh : ∀ e ∈ fresh, finalized cuts e = false) :
    resolveFinal cuts (log ++ fresh) = resolveFinal cuts log := by
  unfold resolveFinal
  rw [List.filter_append, filter_nil_of_false hfresh, List.append_nil]

/-! ## §7. The duelling admins, resolved (paper §1, §3, Fig. 2)

The scenario `Authority.lean` proved unresolvable coordination-free
(`sole_admin_not_iconfluent`; and fail-closed annihilates both duellists,
`duelling_admins_annihilate`): Alice and Bob, both Admins, concurrently
demote each other. ERA's answer, executed: every replica computes the same
execution order, the demote that executes first de-admins the other, and
the second is unauthorised at its point of execution — one deterministic
survivor, no annihilation, at every replica. -/

def alice : Nat := 1
def bob : Nat := 2

/-- Fig. 2's history: Alice joins (becoming the first Admin), Bob joins,
Alice promotes Bob to Admin — then, concurrently, each demotes the other
to Reader. -/
def e1 : Event := joinEv 1 alice
def e2 : Event := joinEv 2 bob
def e3 : Event := promoteEv 3 alice bob admin
def e4 : Event := demoteEv 4 alice bob reader
def e5 : Event := demoteEv 5 bob alice reader

def duelLog : List Event := [e1, e2, e3, e4, e5]

/-- The arbiter's first announcement: epoch 1 contains the settled setup
(both joins and the promotion). The duelling demotes are still pending. -/
def setupCuts : List Cut := [(1, 1), (1, 2), (1, 3)]

/-- A later announcement: epoch 2 contains Bob's demote (e5) — Alice's e4
had not reached the arbiter (Fig. 6's `b₃`/`d₁` situation) and stays
pending. -/
def laterCuts : List Cut := advance setupCuts 2 [5]

/-- With the duel pending, the within-epoch tiebreak (event id) runs e4
first: Alice's demote executes, Bob is a Reader when e5's turn comes, so
e5 is unauthorised — Alice survives as sole Admin. -/
theorem duel_pending_verdict :
    (resolve setupCuts duelLog).role alice = admin ∧
    (resolve setupCuts duelLog).role bob = reader := by
  decide

/-- **The arbiter's cut placement carries the verdict** — same five events,
one more announcement record, opposite survivor: with e5 finalised into
epoch 2 while e4 is pending, e5 executes first (epoch before pending,
`elt_final_pending`), Alice is demoted while Bob is still Admin, and e4 is
then unauthorised — Bob survives. The arbiter never named a winner; it only
ordered. This is `Seams.lean`'s "the verdict rides the seam", with the real
protocol content: what rides the seam is an ORDER, and the verdict is
derived from it. -/
theorem duel_finalised_verdict :
    (resolve laterCuts duelLog).role alice = reader ∧
    (resolve laterCuts duelLog).role bob = admin := by
  decide

/-- Both demotes finalised — e5 into epoch 2, e4 into epoch 3: the EARLIER
epoch executes first (`elt_of_epoch_lt`), so the verdict matches
`duel_finalised_verdict`, not the id tiebreak. Epoch placement outranks
everything an event carries in itself. -/
example :
    (resolve (advance laterCuts 3 [4]) duelLog).role alice = reader ∧
    (resolve (advance laterCuts 3 [4]) duelLog).role bob = admin := by
  decide

/-- **Duelling admins, resolved** — the theorem the feature exists for: ANY
two replicas that received the duel's five events, in any order with any
duplication, resolve to the SAME view, and that view has one deterministic
surviving Admin (Alice) with the other duellist demoted (Bob, Reader).
Compare `Authority.duelling_admins_annihilate`, where fail-closed kills
both: ERA buys the survivor, at the price of the arbiter trust §5.1 prices
out. -/
theorem duelling_admins_resolved (l l' : List Event)
    (hl : ∀ e, e ∈ l ↔ e ∈ duelLog) (hl' : ∀ e, e ∈ l' ↔ e ∈ duelLog) :
    resolve setupCuts l = resolve setupCuts l'
      ∧ (resolve setupCuts l).role alice = admin
      ∧ (resolve setupCuts l).role bob = reader := by
  have h1 : resolve setupCuts l = resolve setupCuts duelLog :=
    resolve_same_sets (fun _ => Iff.rfl) hl
  have h2 : resolve setupCuts l' = resolve setupCuts duelLog :=
    resolve_same_sets (fun _ => Iff.rfl) hl'
  refine ⟨h1.trans h2.symm, ?_, ?_⟩
  · rw [h1]; exact duel_pending_verdict.1
  · rw [h1]; exact duel_pending_verdict.2

/-- Authorisation safety, visible at the resolved view (Fig. 2's ✗ marks,
Fig. 4's flavour): after the pending-duel resolution the demoted Bob may no
longer write, while Alice still may — `write` requires Writer or Admin
(§3 op 2), judged against the arbitrated view. -/
example : authorised (resolve setupCuts duelLog) (writeEv 9 bob) = false := by
  decide

example : authorised (resolve setupCuts duelLog) (writeEv 9 alice) = true := by
  decide

/-! ## §8. The membership lifecycle — invited, member, left (paper §1)

§3's role codes answer *what may this user do*. §1's membership lifecycle
answers *how did they get here*: invited, joined, left. They are different
questions, and the role codes cannot express the second — `outsider` is worn
by a user who never appeared and by one an Admin expelled a minute ago. That
is not a modelling nicety:

  * `departed_indistinguishable_from_stranger` — **no** admission policy
    reading the joiner's own role code (which is all §3's join rule reads) can
    tell a departed member from a stranger; the two histories present the same
    two observables.
  * `departed_rejoins_unchecked` — so under §3 alone the expelled Admin walks
    straight back in as a Reader, with nobody's consent, at every replica.
  * `promote_admits_nonmember` — and the *other* door: §3's promote reads role
    codes only, so an Admin can install a user who never joined.

This section adds the lifecycle **beside** the role machinery, never inside
it. Nothing in §1-§7 changes shape:

  * `inviteEv` is a new event kind (`4`). `authorised` refuses every kind
    above `3` by construction, so an invitation is inert for the role fold
    (`applyEvent_invite_noop`): it carries lifecycle information only.
  * `traceLife` computes the lifecycle alongside the paper's own semantics,
    and `traceLife_role` proves that layer **conservative** — the resolved
    view is `resolve`'s, so every verdict of §7 stands verbatim.
  * `lifeAuthorised` / `resolveGated` are the §1 discipline: a join needs an
    invitation (except for the founder, whom nobody could have invited), and a
    promotion only reaches a member. `lifeAuthorised_refuses_more` keeps
    authorisation safety — the gate can only refuse what §3 allowed, never
    admit what it refused — `gated_founder_admitted` keeps it from refusing
    everything, and `resolveGated_same_sets` keeps the arbitration theorem:
    the gate reads a lifecycle that is itself a function of the execution
    order, so delivery-independence survives the extension.

`gated_return_needs_reinvitation` is the payoff: on one history, §3 readmits
the departed Alice and the gated protocol refuses her until Bob invites her
back. `gated_duel_refuses_uninvited` prices the discipline honestly — on §7's
own history, which contains no invitations at all, only the founder is
admitted. The gate is a different protocol, not a correction to the paper's. -/

/-- `invite(a, b)` — §1's invitation, as event kind `4`. Inert for §3's role
machinery by construction (`authorised` answers `false` for every kind above
`3`), so adding it to a log cannot perturb any verdict of §1-§7; the
lifecycle folds of this section are what read it. -/
def inviteEv (eid a b : Nat) : Event := ⟨eid, 4, a, b, 0⟩

/-- Every kind outside §3's four operations is refused outright — the clause
that makes `inviteEv` inert, stated for all of them, not just kind `4`. -/
theorem authorised_kind_gt_three {v : GroupView} {e : Event} (h : 4 ≤ e.kind) :
    authorised v e = false := by
  obtain ⟨eid, kind, actor, target, role⟩ := e
  revert h
  match kind with
  | 0 => intro h; exact absurd (show (4:Nat) ≤ 0 from h) (by decide)
  | 1 => intro h; exact absurd (show (4:Nat) ≤ 1 from h) (by decide)
  | 2 => intro h; exact absurd (show (4:Nat) ≤ 2 from h) (by decide)
  | 3 => intro h; exact absurd (show (4:Nat) ≤ 3 from h) (by decide)
  | _ + 4 => intro _; rfl

/-- An invitation is an exact no-op on the role view. -/
theorem applyEvent_invite_noop (v : GroupView) (eid a b : Nat) :
    applyEvent v (inviteEv eid a b) = v :=
  applyEvent_unauthorised (authorised_kind_gt_three (Nat.le_refl 4))

/-- **An outsider can only join.** A user at `outsider` — never a member, or
expelled — fails every §3 rule but join: write wants Writer, promote and
demote want Admin. The one door left open is the join door, which is exactly
where §1 puts the invitation. -/
theorem outsider_authorised_only_join {v : GroupView} {e : Event}
    (hout : v.role e.actor = outsider) (hkind : e.kind ≠ 0) :
    authorised v e = false := by
  obtain ⟨eid, kind, actor, target, role⟩ := e
  match kind with
  | 0 => exact absurd rfl hkind
  | 1 => simp [authorised, hout, writer, outsider]
  | 2 => simp [authorised, hout, admin, outsider]
  | 3 => simp [authorised, hout, admin, outsider]
  | _ + 4 => rfl

/-- **A departed member's later history is invisible.** Every non-join event
they issue is unauthorised at its execution point and skipped exactly, so the
whole fold is the identity — expulsion is effective without any further
bookkeeping. -/
theorem outsider_log_noop {v : GroupView} {u : Nat} (hout : v.role u = outsider) :
    ∀ l : List Event, (∀ e ∈ l, e.actor = u ∧ e.kind ≠ 0) →
      l.foldl applyEvent v = v := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e t ih =>
    intro hl
    have he := hl e (List.Mem.head t)
    have hun : authorised v e = false :=
      outsider_authorised_only_join (by rw [he.1]; exact hout) he.2
    show t.foldl applyEvent (applyEvent v e) = v
    rw [applyEvent_unauthorised hun]
    exact ih fun e' he' => hl e' (List.Mem.tail e he')

/-- ⚠ **§3's promote does not check membership.** The rule reads role codes
only, and `outsider < r` is exactly the condition it wants, so an Admin may
promote a user who never joined straight into the group. Gating *join* on an
invitation therefore does not by itself gate membership — `lifeAuthorised`
below gates promote on the target's lifecycle too. -/
theorem promote_admits_nonmember {v : GroupView} {i a b : Nat}
    (hadmin : v.role a = admin) (hout : v.role b = outsider) :
    authorised v (promoteEv i a b admin) = true := by
  simp [authorised, promoteEv, hadmin, hout, admin, outsider]

/-- §1's membership lifecycle: never seen, invited, joined, departed. Carried
beside the role codes, because no function of the role codes can compute it
(`departed_indistinguishable_from_stranger`). -/
inductive Life where
  | never | invited | member | left
  deriving DecidableEq, Repr

/-- The lifecycle of every user — derived state, like `GroupView`. -/
abbrev LifeMap := Nat → Life

/-- Nobody has been seen. -/
def initLife : LifeMap := fun _ => Life.never

/-- Is this invitation good? Kind `4`, the inviter can write (Writer or Admin
— §3's "can write events into the DAG" is the weakest role with standing),
and the invitee is not already in the group. -/
def inviteAuthorised (v : GroupView) (e : Event) : Bool :=
  decide (e.kind = 4) && decide (writer ≤ v.role e.actor) &&
    decide (v.role e.target = outsider)

/-- The lifecycle transition of an event that *executes*: a join makes its
actor a member, a demotion to `outsider` marks its target departed (§1's
"left" — the expulsion `authorised`'s docstring already names), and nothing
else moves the lifecycle. -/
def lifeMark (ls : LifeMap) (e : Event) : LifeMap :=
  match e.kind with
  | 0 => fun u => if u = e.actor then Life.member else ls u
  | 3 => if e.role = outsider
         then fun u => if u = e.target then Life.left else ls u
         else ls
  | _ => ls

/-- One step of the *observational* machine: the paper's semantics unchanged,
with the lifecycle computed alongside it. -/
def traceStep (st : GroupView × LifeMap) (e : Event) : GroupView × LifeMap :=
  if inviteAuthorised st.1 e then
    (st.1, fun u => if u = e.target then Life.invited else st.2 u)
  else if authorised st.1 e then
    (applyEvent st.1 e, lifeMark st.2 e)
  else st

/-- Resolve a log against the arbiter's announcements, tracking the lifecycle
— same execution order, same authorisation, one extra observable. -/
def traceLife (cuts : List Cut) (log : List Event) : GroupView × LifeMap :=
  (execOrder cuts log).foldl traceStep (initView, initLife)

/-- Each observational step's view component is exactly `applyEvent`'s: an
authorised invitation leaves the view alone (it is kind `4`, which §3 refuses)
and every other branch either applies or skips as before. -/
theorem traceStep_view (st : GroupView × LifeMap) (e : Event) :
    (traceStep st e).1 = applyEvent st.1 e := by
  unfold traceStep
  by_cases hinv : inviteAuthorised st.1 e = true
  · rw [if_pos hinv]
    have hk : e.kind = 4 := by
      have := (Bool.and_eq_true _ _ |>.mp ((Bool.and_eq_true _ _).mp hinv).1).1
      exact of_decide_eq_true this
    exact (applyEvent_unauthorised
      (authorised_kind_gt_three (Nat.le_of_eq hk.symm))).symm
  · rw [if_neg hinv]
    by_cases hau : authorised st.1 e = true
    · rw [if_pos hau]
    · rw [if_neg hau]
      exact (applyEvent_unauthorised (Bool.not_eq_true _ ▸ hau)).symm

theorem foldl_traceStep_view : ∀ (l : List Event) (st : GroupView × LifeMap),
    (l.foldl traceStep st).1 = l.foldl applyEvent st.1
  | [], _ => rfl
  | e :: t, st => by
    show (t.foldl traceStep (traceStep st e)).1 = t.foldl applyEvent (applyEvent st.1 e)
    rw [← traceStep_view st e]
    exact foldl_traceStep_view t (traceStep st e)

/-- **The lifecycle layer is conservative.** Tracking invited/member/left
costs the protocol nothing: the resolved view is `resolve`'s, so every verdict
of §7 — the duel's survivor included — holds verbatim in the extended
machine. -/
theorem traceLife_role (cuts : List Cut) (log : List Event) :
    (traceLife cuts log).1 = resolve cuts log :=
  foldl_traceStep_view (execOrder cuts log) (initView, initLife)

/-! ### The two holes, exhibited -/

/-- Alice founds the group (first joiner, so Admin), Bob joins, and Alice then
demotes herself out of the group entirely — §1's "left". -/
def departLog : List Event :=
  [joinEv 1 alice, joinEv 2 bob, demoteEv 3 alice alice outsider]

/-- The same group without Alice in it: Bob founds it and departs the same
way, so Alice is a user this history has never mentioned. -/
def strangerLog : List Event :=
  [joinEv 1 bob, demoteEv 2 bob bob outsider]

/-- ⚠ **A departed member is indistinguishable from a stranger** to every
policy §3's join rule could consult. `P` ranges over ALL functions of the two
things that rule reads — whether the group has started, and the joiner's own
role code — and on these two histories it must answer the same, because both
observables agree: `started = true`, `role alice = outsider`. Alice was an
Admin expelled from the group in one history and has never been mentioned in
the other. No re-phrasing of a *role* predicate escapes this; the lifecycle
has to be carried. -/
theorem departed_indistinguishable_from_stranger (P : Bool → Nat → Bool) :
    P (resolve [] departLog).started ((resolve [] departLog).role alice)
      = P (resolve [] strangerLog).started ((resolve [] strangerLog).role alice) := by
  have hstart : (resolve [] departLog).started
      = (resolve [] strangerLog).started := by decide
  have hrole : (resolve [] departLog).role alice
      = (resolve [] strangerLog).role alice := by decide
  rw [hstart, hrole]

/-- The lifecycle does distinguish them — the same two histories, told apart
by the layer `traceLife` carries. -/
theorem departed_lifecycle_distinguishes :
    (traceLife [] departLog).2 alice = Life.left ∧
    (traceLife [] strangerLog).2 alice = Life.never := by decide

/-- Alice leaves, then simply joins again. -/
def rejoinLog : List Event := departLog ++ [joinEv 4 alice]

/-- ⚠ **The expelled Admin walks back in.** Under §3 alone her rejoin is
authorised — she is an `outsider`, which is the join rule's entire
precondition — and it executes at every replica, deterministically, returning
her as a Reader. Nobody consented; there is no rule to consult, because the
state that would justify refusing (she *left*) is not in the role view. -/
theorem departed_rejoins_unchecked :
    (resolve [] rejoinLog).role alice = reader ∧
    (traceLife [] rejoinLog).2 alice = Life.member := by decide

/-! ### The §1 discipline: admission by invitation -/

/-- **Authorisation under the §1 lifecycle**: §3's rule, and additionally —
a join needs a standing invitation, unless the group has not started (the
founder has nobody to invite them, §3 op 1); a promotion only reaches a user
who is actually a member, closing `promote_admits_nonmember`. Every other
operation is judged exactly as §3 judges it. -/
def lifeAuthorised (v : GroupView) (ls : LifeMap) (e : Event) : Bool :=
  authorised v e &&
    (match e.kind with
     | 0 => decide (ls e.actor = Life.invited) || !v.started
     | 2 => decide (ls e.target = Life.member)
     | _ => true)

/-- **The gate only ever refuses.** Authorisation safety (P2) survives the
extension: nothing the lifecycle admits was refused by §3, so no theorem of
§4 about unauthorised events is weakened. -/
theorem lifeAuthorised_refuses_more {v : GroupView} {ls : LifeMap} {e : Event}
    (h : lifeAuthorised v ls e = true) : authorised v e = true :=
  ((Bool.and_eq_true _ _).mp h).1

/-- Away from admission the gate is invisible: for writes and demotions it IS
§3's rule. -/
theorem lifeAuthorised_of_write_demote {v : GroupView} {ls : LifeMap} {e : Event}
    (h : e.kind = 1 ∨ e.kind = 3) : lifeAuthorised v ls e = authorised v e := by
  unfold lifeAuthorised
  rcases h with h | h <;> rw [h] <;> simp

/-- **A join without an invitation is refused** — the §1 precondition, in
general form (the founder exemption is the `v.started = true` hypothesis). -/
theorem gated_join_needs_invitation {v : GroupView} {ls : LifeMap} {e : Event}
    (hk : e.kind = 0) (hstart : v.started = true)
    (hinv : ls e.actor ≠ Life.invited) : lifeAuthorised v ls e = false := by
  unfold lifeAuthorised
  rw [hk]
  simp [hstart, hinv]

/-- **A promotion cannot reach a non-member** — the other door, closed. -/
theorem gated_promote_needs_member {v : GroupView} {ls : LifeMap} {e : Event}
    (hk : e.kind = 2) (hmem : ls e.target ≠ Life.member) :
    lifeAuthorised v ls e = false := by
  unfold lifeAuthorised
  rw [hk]
  simp [hmem]

/-- **The gate is not a refusal machine**: the founder is admitted, with no
invitation in existence — so the discipline is satisfiable, and a group can
start under it. -/
theorem gated_founder_admitted :
    lifeAuthorised initView initLife (joinEv 1 alice) = true := by decide

/-- One step of the gated machine: invitations are recorded, admissible events
execute and mark the lifecycle, everything else is skipped exactly. -/
def gatedStep (st : GroupView × LifeMap) (e : Event) : GroupView × LifeMap :=
  if inviteAuthorised st.1 e then
    (st.1, fun u => if u = e.target then Life.invited else st.2 u)
  else if lifeAuthorised st.1 st.2 e then
    (applyEvent st.1 e, lifeMark st.2 e)
  else st

/-- ERA under the §1 lifecycle: the same epoch arbitration, the same guarded
fold, with admission judged against the lifecycle as well as the roles. -/
def resolveGated (cuts : List Cut) (log : List Event) : GroupView × LifeMap :=
  (execOrder cuts log).foldl gatedStep (initView, initLife)

/-- **The extension keeps the arbitration theorem.** Replicas holding
membership-equivalent cut and event sets resolve to the same gated view and
the same lifecycle — the gate reads state that is itself a function of the
execution order, so §5's delivery-independence survives it untouched. -/
theorem resolveGated_same_sets {cuts cuts' : List Cut} {log log' : List Event}
    (hc : ∀ c, c ∈ cuts ↔ c ∈ cuts') (hl : ∀ e, e ∈ log ↔ e ∈ log') :
    resolveGated cuts log = resolveGated cuts' log' := by
  unfold resolveGated
  rw [execOrder_same_sets hc hl]

/-- The same for the observational machine. -/
theorem traceLife_same_sets {cuts cuts' : List Cut} {log log' : List Event}
    (hc : ∀ c, c ∈ cuts ↔ c ∈ cuts') (hl : ∀ e, e ∈ log ↔ e ∈ log') :
    traceLife cuts log = traceLife cuts' log' := by
  unfold traceLife
  rw [execOrder_same_sets hc hl]

/-- A lifecycle-complete history: Alice founds the group, invites Bob, Bob
joins on that invitation, Alice promotes him to Admin, and Alice then leaves.
Every admission in it has a warrant. -/
def invitedLog : List Event :=
  [joinEv 1 alice, inviteEv 2 alice bob, joinEv 3 bob,
   promoteEv 4 alice bob admin, demoteEv 5 alice alice outsider]

/-- Alice, having left, tries to walk back in exactly as `rejoinLog` did. -/
def returnLog : List Event := invitedLog ++ [joinEv 6 alice]

/-- Bob invites her back, and she joins on that invitation. -/
def reinviteLog : List Event := returnLog ++ [inviteEv 7 bob alice, joinEv 8 alice]

/-- **The return needs a re-invitation** — the two protocols on one history.
§3 readmits Alice as a Reader (first conjunct: this is
`departed_rejoins_unchecked` again, now inside a history where every other
admission was warranted). The §1 discipline refuses her: her lifecycle reads
`left`, not `invited`, so the join is skipped and she stays outside (second
and third). Bob then invites her, and the same gate admits her (fourth and
fifth) — the refusal is a precondition, not a ban.

Note which layer decided: the merge, the epoch arbitration and the execution
order are identical in all three runs. What changed is the authorisation
predicate, and `lifeAuthorised_refuses_more` bounds how much it could change:
strictly fewer admissions than §3, never more. -/
theorem gated_return_needs_reinvitation :
    (resolve [] returnLog).role alice = reader ∧
    (resolveGated [] returnLog).1.role alice = outsider ∧
    (resolveGated [] returnLog).2 alice = Life.left ∧
    (resolveGated [] reinviteLog).1.role alice = reader ∧
    (resolveGated [] reinviteLog).2 alice = Life.member := by decide

/-- Bob's own membership is warranted throughout: invited by Alice, admitted
on that invitation, and an Admin by the time she leaves — so the refusal above
is about Alice's missing invitation, not about a gate that refuses everyone. -/
theorem gated_invited_join_admitted :
    (resolveGated [] invitedLog).1.role bob = admin ∧
    (resolveGated [] invitedLog).2 bob = Life.member := by decide

/-- **On a history where every admission carries a warrant, the gate is
invisible**: `invitedLog` resolves identically under §3 and under the §1
discipline, user by user. The extension is not a different semantics for
ordinary histories — it refuses exactly the admissions §1 says need a warrant
and had none (`gated_return_needs_reinvitation`,
`gated_duel_refuses_uninvited`), and nothing else. -/
theorem gated_agrees_on_warranted_history :
    (resolveGated [] invitedLog).1.role alice = (resolve [] invitedLog).role alice ∧
    (resolveGated [] invitedLog).1.role bob = (resolve [] invitedLog).role bob ∧
    (resolveGated [] invitedLog).2 alice = (traceLife [] invitedLog).2 alice ∧
    (resolveGated [] invitedLog).2 bob = (traceLife [] invitedLog).2 bob := by decide

/-- ⚠ **What the discipline costs, on §7's own history.** `duelLog` contains
no invitations — it is written against §3, where none exist — so under the
gate only the founder is admitted: Bob's join is refused for want of an
invitation, and Alice's promotion of him is refused because he is not a
member (`gated_promote_needs_member`; under §3 alone
`promote_admits_nonmember` would have installed him anyway). The duel then
has one duellist and no duel.

This is the honest price of the extension, and the reason it is a *parallel*
machine: §7's theorems are about §3's protocol, which `traceLife_role` leaves
exactly as it was. A deployment picks one. -/
theorem gated_duel_refuses_uninvited :
    (resolveGated setupCuts duelLog).1.role alice = admin ∧
    (resolveGated setupCuts duelLog).1.role bob = outsider ∧
    (resolveGated setupCuts duelLog).2 bob = Life.never := by decide

end Uwueave.Era
