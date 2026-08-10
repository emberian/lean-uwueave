/-
# Uwueave.Spec — a fluid, proof-carrying composition DSL.

The point of the catalog is to be *composed*: a real document schema is a
record of fields — a node set here, a per-node register there, a quota, a
bookmark set. This file is the algebra that lets you build the schema
fluently and get, at the top, not a heuristic but a **verdict that carries its
own evidence**:

  * `Verdict.free h`            — an actual `IConfluent` proof, or
  * `Verdict.clash x y …`       — an actual two-replica counterexample,
                                  transported up through every combinator, so
                                  the top-level answer to "can my whole
                                  document replicate coordination-free?" is
                                  either a theorem or a runnable repro, or
  * `SegVerdict …`              — the refined third answer (§3): not free
                                  globally — the clash is carried, not waved
                                  at — yet free within the fibers of a seam
                                  `σ`, so "go to consensus" sharpens to
                                  "coordinate only when `σ` changes".

The design is a *shallow* embedding: a "spec" is just a Lean type with a
`MergeState` instance, built with ordinary `×` and `→`, and classified
invariants compose with ordinary function application. You get binders, `let`,
recursion and notation from Lean itself instead of from a bespoke AST — that
is what makes it fluid. (A deep embedding with a reflective `Spec` inductive
would buy serialization of specs, at the price of universe bookkeeping; if a
tool needs that later, it can quote *into* this layer.)

The worked examples at the bottom are the intended user experience: a loom
document schema assembled in six lines, classified field-by-field; poisoned
variants showing a single field's (and a single *key's*) counterexample
propagating to the whole document; and a budgeted variant whose quota field
reports the seam — spends free, re-allocation the only coordination point.
-/
import Uwueave.Move
import Uwueave.Segmented

namespace Uwueave.Spec

open Uwueave Uwueave.Catalog Uwueave.Segmented

universe u v

/-! ## §1. Verdicts -/

/-- A classified invariant: either provably coordination-free, or refuted by a
concrete clashing pair. `escalation_witness` guarantees every non-confluent
invariant *has* a clash, so this type loses no generality — it just insists the
evidence be produced rather than promised. -/
inductive Verdict {S : Type u} [MergeState S] (I : Invariant S) : Type u where
  /-- Coordination-free, with the proof. -/
  | free (h : IConfluent I)
  /-- Requires coordination; `x`, `y` are legal replica states whose merge is
  illegal — the repro a test suite should replay. -/
  | clash (x y : S) (hx : I x) (hy : I y) (hbad : ¬ I (x ⊔ y))

namespace Verdict

variable {A : Type u} {B : Type v} [MergeState A] [MergeState B]

/-- Conjunction of two free invariants **on the same state** is free. (No
independence needed — both watch the same merge.) -/
def andFree {I J : Invariant A} :
    Verdict I → Verdict J → Option (Verdict (fun s => I s ∧ J s))
  | .free hI, .free hJ => some (.free (and_iconfluent hI hJ))
  | _, _ => none
  -- `none` is honest: a conjunction with a non-confluent conjunct is not
  -- automatically non-confluent (the other conjunct may exclude the clash
  -- states), so no verdict is claimed. Classify the conjunction directly if
  -- you need one.

/-- Two free field invariants give a free record invariant — `product_iconfluent`
as a combinator. -/
def prodFree {IA : Invariant A} {IB : Invariant B} :
    IConfluent IA → IConfluent IB → Verdict (S := A × B) (fun p => IA p.1 ∧ IB p.2) :=
  fun hA hB => .free (product_iconfluent hA hB)

/-- **Counterexample transport, left field.** A clash on field A becomes a clash
on the whole record, holding any legal field-B value fixed (idempotence keeps
it fixed through the merge). This is what makes the DSL's failures *actionable*:
the top-level repro names the exact field and states. -/
def prodClashLeft {IA : Invariant A} {IB : Invariant B}
    (x y : A) (hx : IA x) (hy : IA y) (hbad : ¬ IA (x ⊔ y))
    (b : B) (hb : IB b) : Verdict (S := A × B) (fun p => IA p.1 ∧ IB p.2) :=
  .clash (x, b) (y, b) ⟨hx, hb⟩ ⟨hy, hb⟩
    (fun hmerge => hbad hmerge.1)

/-- Counterexample transport, right field. -/
def prodClashRight {IA : Invariant A} {IB : Invariant B}
    (x y : B) (hx : IB x) (hy : IB y) (hbad : ¬ IB (x ⊔ y))
    (a : A) (ha : IA a) : Verdict (S := A × B) (fun p => IA p.1 ∧ IB p.2) :=
  .clash (a, x) (a, y) ⟨ha, hx⟩ ⟨ha, hy⟩
    (fun hmerge => hbad hmerge.2)

/-- A per-key-free invariant is free over the keyed map — `pi_iconfluent` as a
combinator. -/
def keyedFree {K : Type u} {V : Type v} [MergeState V] {J : K → Invariant V}
    (h : ∀ k, IConfluent (J k)) :
    Verdict (S := K → V) (fun f => ∀ k, J k (f k)) :=
  .free (pi_iconfluent h)

/-- **Counterexample transport through a keyed map** — the Pi cousin of
`prodClashLeft`/`prodClashRight`, and the lift that completes the transport
story: products AND maps carry counterexamples to the top. A clash for `J k₀`
at a single key becomes a clash for the whole keyed invariant: plant `x`/`y`
at `k₀` and the legal default `f₀ k` at every other key. Merge is pointwise
and idempotent, so every other key stays at its default while `k₀` merges
into the bad state — the whole-map repro differs from a legal map at exactly
one key, which is what makes it worth pasting into a test. -/
def keyedClash {K : Type u} {V : Type v} [MergeState V] [DecidableEq K]
    {J : K → Invariant V} (k₀ : K)
    (x y : V) (hx : J k₀ x) (hy : J k₀ y) (hbad : ¬ J k₀ (x ⊔ y))
    (f₀ : K → V) (hf₀ : ∀ k, J k (f₀ k)) :
    Verdict (S := K → V) (fun f => ∀ k, J k (f k)) :=
  .clash (fun k => if k = k₀ then x else f₀ k) (fun k => if k = k₀ then y else f₀ k)
    (fun k => by
      by_cases h : k = k₀
      · subst h; simpa using hx
      · simpa [h] using hf₀ k)
    (fun k => by
      by_cases h : k = k₀
      · subst h; simpa using hy
      · simpa [h] using hf₀ k)
    (fun hall => hbad (by simpa using hall k₀))

/-- Erase the evidence, keep the answer — for reporting. -/
def isFree {S : Type u} [MergeState S] {I : Invariant S} : Verdict I → Bool
  | .free _ => true
  | .clash .. => false

end Verdict

/-! ## §2. The catalog, by name — reusable verdict values.

Composition wants *values*: a schema author assembling a report should cite
`gsetMemFree 0` and `mutexClash`, not re-state proofs. Each entry wraps an
existing catalog theorem — the free entries carry the theorem itself, the
clash entries package the theorem's own witness pair so the repro is a
first-class value the transports (`prodClashLeft` / `prodClashRight` /
`keyedClash`) can lift. No new confluence content lives here. -/

/-- `Catalog.gset_mem_iconfluent`, as a verdict: "contains `a`" on a grow-only
set is coordination-free — anything observed survives every merge. -/
def gsetMemFree {α : Type} (a : α) :
    Verdict (S := GSet α) (fun s => s a = true) :=
  .free (gset_mem_iconfluent a)

/-- `Catalog.gset_notmem_iconfluent`, as a verdict: "does not contain `a`" on
a grow-only set is also coordination-free — a union of two sets both lacking
`a` lacks `a`. -/
def gsetNotMemFree {α : Type} (a : α) :
    Verdict (S := GSet α) (fun s => s a = false) :=
  .free (gset_notmem_iconfluent a)

/-- `Catalog.lww_every_invariant_iconfluent`, as a verdict: a single LWW
register never merge-breaks *any* invariant, because its join selects one of
its two arguments. (Two LWW registers are another story —
`Catalog.lww_cross_field_not_iconfluent`.) -/
def lwwSingleFree (I : Invariant LWW) : Verdict I :=
  .free (lww_every_invariant_iconfluent I)

/-- `Catalog.escrow_local_bound_iconfluent`, as a verdict: per-replica quota
bounds are coordination-free — the escrow rephrasing of a bounded resource,
by name. -/
def escrowFree {ι : Type} (q : ι → Nat) :
    Verdict (S := Escrow ι) (fun f => ∀ i, f i ≤ q i) :=
  .free (escrow_local_bound_iconfluent q)

/-- `Catalog.gset_atMostOne_not_iconfluent`'s witness pair (`{0}` and `{1}`),
packaged as a clash verdict: any uniqueness ceiling on a grow-only set
escalates, and this value carries the two singleton replicas whose union
refutes it. -/
def atMostOneClash :
    Verdict (S := GSet Nat) (fun s => ∀ m n, s m = true → s n = true → m = n) :=
  .clash (fun n => n == 0) (fun n => n == 1)
    (fun m n hm hn => by simp at hm hn; omega)
    (fun m n hm hn => by simp at hm hn; omega)
    (fun h => absurd (h 0 1 (by decide) (by decide)) (by decide))

/-- `Catalog.or_breaks_iconfluence`'s witness pair, packaged as a clash
verdict: mutual exclusion ("only Alice holds the lock or only Bob does")
cannot be replicated coordination-free — each replica satisfies its own
disjunct, the merged state satisfies neither. -/
def mutexClash :
    Verdict (S := GSet Nat)
      (fun s => (s 0 = true ∧ s 1 = false) ∨ (s 1 = true ∧ s 0 = false)) :=
  .clash (fun n => n == 0) (fun n => n == 1)
    (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
    (fun h => h.elim (fun hbad => absurd hbad.2 (by decide))
                     (fun hbad => absurd hbad.2 (by decide)))

/-! ## §3. The seam verdict — between `free` and consensus.

`Verdict.clash` is honest but blunt: it says coordination is needed
*somewhere*, and a schema author's next question is always "on every write?".
`Segmented.lean` holds the refinement — an invariant can fail I-confluence
globally yet be confluent within the fibers of a projection — and this
section gives that refinement a carrier so the DSL can *say* it. -/

/-- **The seam verdict** — the verdict a schema author actually wants when
`clash` alone would send them to consensus: "coordinate only when `σ`
changes". It carries **both** halves of the refined judgement:

  * the **global clash** — legal replicas `x`, `y` whose merge is illegal
    (`hx`, `hy`, `hbad`), so running fully coordination-free is refuted with
    a repro, exactly as in `Verdict.clash`; and
  * the **seam** — a projection `σ` with a `SegmentedIConfluent σ I` proof:
    merges of same-`σ` states preserve the invariant *and stay in the fiber*.

Operationally: replicate freely between coordination events and coordinate
only to change `σ` — the clash says coordination is needed somewhere, the
segmentation says it is needed *only there*. -/
structure SegVerdict {S : Type u} [MergeState S] (I : Invariant S)
    (Seg : Type v) : Type (max u v) where
  /-- The seam: the projection replicas hold fixed between explicit
  coordination events. -/
  σ : S → Seg
  /-- Within a fiber of `σ`, merges preserve `I` and the fiber. -/
  seamFree : SegmentedIConfluent σ I
  /-- One replica of the global clash. -/
  x : S
  /-- The other replica of the global clash. -/
  y : S
  /-- `x` is legal … -/
  hx : I x
  /-- … `y` is legal … -/
  hy : I y
  /-- … and their merge is not — the repro that rules out global freedom. -/
  hbad : ¬ I (x ⊔ y)

namespace SegVerdict

variable {S : Type u} {Seg : Type v} [MergeState S] {I : Invariant S}

/-- The escalation reading: the carried clash refutes global I-confluence
outright. A `SegVerdict` never claims the invariant is free — only that its
coordination has a *shape*. -/
theorem escalatesGlobally (v : SegVerdict I Seg) : ¬ IConfluent I :=
  fun h => v.hbad (h v.x v.y v.hx v.hy)

/-- The free-running reading: merges of same-seam legal replicas are safe —
this is the half a replica exercises on every sync between coordination
events. -/
theorem freeWithinSeam (v : SegVerdict I Seg) {a b : S}
    (hσ : v.σ a = v.σ b) (ha : I a) (hb : I b) : I (a ⊔ b) :=
  (v.seamFree a b hσ ha hb).1

/-- The closure reading: a same-seam merge cannot *leave* the seam. Without
this half, one sync could silently teleport replicas across the boundary and
the free-running guarantee would evaporate — a re-allocation can never happen
behind your back. -/
theorem staysInSeam (v : SegVerdict I Seg) {a b : S}
    (hσ : v.σ a = v.σ b) (ha : I a) (hb : I b) : v.σ (a ⊔ b) = v.σ a :=
  (v.seamFree a b hσ ha hb).2

/-- Forget the seam: every `SegVerdict` demotes to a `Verdict.clash` — the
honest answer for a consumer that only understands the binary judgement. -/
def toClash (v : SegVerdict I Seg) : Verdict I :=
  .clash v.x v.y v.hx v.hy v.hbad

end SegVerdict

/-- **The worked seam instance** — `Segmented.lean`'s punchline pair,
packaged as one value. The clash is `Segmented.budget_not_iconfluent`'s
witness pair (allocations 10+0 and 0+10 against budget 10, merging to the
pointwise max 10+10 — over budget); the seam is `Segmented.budget_segmented`
(segmented over the allocation, `Prod.fst`). Reading: spends never
coordinate; re-allocation is the *only* coordination point — where `clash`
alone would have sent every spend to consensus. -/
def budgetSegVerdict : SegVerdict (BudgetInv 10) (Bool → Nat) where
  σ := Prod.fst
  seamFree := budget_segmented 10
  x := ((fun b => if b then 10 else 0), (fun b => if b then 10 else 0))
  y := ((fun b => if b then 0 else 10), (fun b => if b then 0 else 10))
  hx := by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide
  hy := by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide
  hbad := fun hgood => by
    have := hgood.2
    revert this
    show ¬ (Nat.max 10 0 + Nat.max 0 10 = 10)
    decide

/-! ## §4. Worked example — a loom document schema, assembled and classified.

The schema (deliberately shaped like a universal-weave instance):

  * `nodes`     : a grow-only node-id set              (`GSet Nat`)
  * `meta`      : a per-node LWW register              (`Nat → LWW`)
  * `bookmarks` : per-device bookmark counts against
                  a per-device quota (escrowed)        (`Escrow Bool`)

State and merge come from `×` and `→` — no new instances, no new proofs. -/

/-- The document state. This *is* the DSL: ordinary type formers, instances
resolved by composition. -/
abbrev LoomDoc := GSet Nat × ((Nat → LWW) × Escrow Bool)

example : MergeState LoomDoc := inferInstance

/-- The document invariant: genesis node present; every metadata register's
timestamp at least 1 (i.e. genuinely written); no device over its bookmark
quota. -/
def loomInv (quota : Bool → Nat) : Invariant LoomDoc := fun d =>
  (d.1 0 = true)
  ∧ ((∀ k, 1 ≤ (d.2.1 k).ts) ∧ (∀ i, d.2.2 i ≤ quota i))

/-- **The whole document replicates coordination-free** — built entirely from
catalog verdicts and the two lifts, one combinator per schema node. Read the
term: it *is* the schema's classification report. -/
def loomVerdict (quota : Bool → Nat) : Verdict (loomInv quota) :=
  .free (product_iconfluent
    (gset_mem_iconfluent 0)
    (product_iconfluent
      (pi_iconfluent fun _ => lww_every_invariant_iconfluent (fun r => 1 ≤ r.ts))
      (escrow_local_bound_iconfluent quota)))

/-! ### The poisoned variant

Add one innocent-looking feature — "a document has at most one pinned node",
a uniqueness ceiling on a grow-only set — and the *document* stops being
coordination-free, with the pin-set's `{0}`/`{1}` clash transported to a
whole-document repro. -/

/-- The poisoned schema: the same document plus a pinned-node set that is
supposed to stay a singleton. -/
abbrev PinnedDoc := GSet Nat × GSet Nat  -- (nodes, pins)

def pinnedInv : Invariant PinnedDoc := fun d =>
  (d.1 0 = true) ∧ (∀ m n, d.2 m = true → d.2 n = true → m = n)

/-- ⚠ The uniqueness ceiling's clash, transported: two replicas that each pin a
different node. Both are legal whole documents; their merge pins two nodes.
The evidence is a pair of complete document states — paste them into a test. -/
def pinnedVerdict : Verdict pinnedInv :=
  Verdict.prodClashRight (IA := fun s => s 0 = true)
    (IB := fun s => ∀ m n, s m = true → s n = true → m = n)
    (fun n => n == 0) (fun n => n == 1)
    (fun m n hm hn => by simp at hm hn; omega)
    (fun m n hm hn => by simp at hm hn; omega)
    (fun hmerge => by
      have := hmerge 0 1 (by decide) (by decide)
      omega)
    (fun n => n == 0) (by decide)

/-- The same ceiling poisoning a *keyed* schema: a map `node ↦ pin-set` where
every node's pin-set must stay at-most-one. `keyedClash` transports the
single-key `{0}`/`{1}` pair to the whole map — node 0 takes the clash, every
other node keeps the (legal) empty set. One key clashes, so the map does. -/
def pinnedPerNodeVerdict :
    Verdict (S := Nat → GSet Nat)
      (fun f => ∀ node m n, f node m = true → f node n = true → m = n) :=
  Verdict.keyedClash
    (J := fun _ => fun s => ∀ m n, s m = true → s n = true → m = n) 0
    (fun n => n == 0) (fun n => n == 1)
    (fun m n hm hn => by simp at hm hn; omega)
    (fun m n hm hn => by simp at hm hn; omega)
    (fun h => absurd (h 0 1 (by decide) (by decide)) (by decide))
    (fun _ _ => false)
    (fun _ _ _ hm _ => Bool.noConfusion hm)

/-! ### The budgeted variant — the seam in the schema

Give the document a quota *field* with its budget in the state (allocation
plus per-device spend — `Segmented.QuotaState`), so re-allocation is an
ordinary replicated write. Globally this field clashes — two legal
re-allocations merge over budget, and the pair transports to a
whole-document repro below — but the verdict to *ship* is `budgetSegVerdict`:
spends and every other field run free; replicas coordinate exactly when the
allocation changes. -/

/-- The budgeted document: the loom document plus an in-state budgeted
quota. -/
abbrev BudgetDoc := LoomDoc × QuotaState

/-- The budgeted invariant: the document invariant, plus the budget-10
invariant on the quota field. -/
def budgetDocInv (quota : Bool → Nat) : Invariant BudgetDoc := fun d =>
  loomInv quota d.1 ∧ BudgetInv 10 d.2

/-- ⚠ The blunt whole-document reading: NOT free. `budgetSegVerdict`'s own
clash pair transports through `prodClashRight`, holding a concrete legal base
document fixed — the field's repro *is* the document's repro. The refined
reading is the seam, in the report below. -/
def budgetDocVerdict (quota : Bool → Nat) : Verdict (budgetDocInv quota) :=
  Verdict.prodClashRight (IA := loomInv quota) (IB := BudgetInv 10)
    budgetSegVerdict.x budgetSegVerdict.y
    budgetSegVerdict.hx budgetSegVerdict.hy budgetSegVerdict.hbad
    ((fun n => n == 0), ((fun _ => ⟨1, 0⟩), (fun _ => 0)))
    ⟨rfl, fun _ => Nat.le_refl 1, fun _ => Nat.zero_le _⟩

/-! ### The report — all three verdict kinds, side by side.

`free` (the clean schema), `clash` with a repro (the poisoned variants —
field-level and key-level), and the *seam* (the budgeted variant): globally
refuted, free within an allocation, coordinate only at re-allocation. -/

/-- The report, evaluated: the clean schema is free, the poisoned one is not —
and both answers are backed by the terms above, not by this `Bool`. -/
example : (loomVerdict (fun _ => 64)).isFree = true := rfl
example : pinnedVerdict.isFree = false := rfl

/-- The keyed poison, evaluated: one clashing key sinks the whole map. -/
example : pinnedPerNodeVerdict.isFree = false := rfl

/-- The budgeted document, evaluated bluntly: as a plain verdict it clashes —
this is all a binary consumer sees … -/
example : (budgetDocVerdict (fun _ => 64)).isFree = false := rfl

/-- … and the quota field's seam verdict demotes to the same answer. -/
example : budgetSegVerdict.toClash.isFree = false := rfl

/-- The seam reading, escalation half: globally the budget escalates —
recovering `Segmented.budget_not_iconfluent` from the packaged witnesses. -/
example : ¬ IConfluent (BudgetInv 10) := budgetSegVerdict.escalatesGlobally

/-- The seam reading, free-running half: same-allocation replicas merge
safely — spends never wait. -/
example (a b : QuotaState) (hσ : a.1 = b.1)
    (ha : BudgetInv 10 a) (hb : BudgetInv 10 b) : BudgetInv 10 (a ⊔ b) :=
  budgetSegVerdict.freeWithinSeam hσ ha hb

/-- The seam reading, closure half: a same-allocation sync cannot
re-allocate behind your back. -/
example (a b : QuotaState) (hσ : a.1 = b.1)
    (ha : BudgetInv 10 a) (hb : BudgetInv 10 b) : (a ⊔ b).1 = a.1 :=
  budgetSegVerdict.staysInSeam hσ ha hb

end Uwueave.Spec

