/-
# Uwueave.LiveSegmented — the seam judgement, relative to the protocol that runs.

**This file exists because an external reviewer (codex), in a third review of this
tree, found a second reachability hole and told us exactly what shape the repair
has.** The first hole was already known and is recorded in `Bounds.lean`
(`latticeOnly_clash_still_separated`, `ew_teleport_floor_is_one`): `Cost`'s
workload model has no happens-before, so a floor can be priced against a pair of
states no history reaches. The obvious response — repair the workload — is not
enough, and codex said why:

> Even when an unreachable pair does not raise the displayed floor, the same pair
> still CONSTRAINS THE STRATEGY SPACE, because `SegmentedIConfluent` is
> lattice-global. A protocol might never realize a clash, and every admitted seam
> is still required to separate that pair — which can inflate the optimum
> indirectly even though no live path is charged.

That is a wound in a different organ. `Bounds.valid_seam_separates_clash` is the
tree's own statement of it and reads as a *caution*; read as a *cost*, it says a
deployment can be made to build a coordination domain for a state its protocol
has no operation to produce. §4 below proves exactly that, with numbers.

## The two-certificate discipline — both are kept, and they say different things

  * `Segmented.SegmentedIConfluent σ I` — **carrier-global**, protocol-independent,
    strictly stronger (`segmented_implies_liveSegmented`), and **robust under
    later expansion of the op vocabulary**: it is a statement about the lattice,
    so adding an operation to the protocol can never invalidate it. That is what
    it is *for*, and it is why it is not being replaced.
  * `LiveSegmented P σ I` — **protocol-relative**, valid for the operational
    substrate `P` and no other, and **what a deployment budget should optimise
    over**. It is not robust: enlarge the op vocabulary and a live certificate
    can die. The price of the smaller optimum is that the certificate names the
    protocol it was issued against.

Neither subsumes the other operationally. Keep both, and say which one a number
was computed under — §4's whole content is that the two numbers differ.

## Contents

  * §1 the interface: `RunModel`, `Reachable`, `CoReachable` (two worlds reached
    from a **common base** — the fork shape), and the fact that any two states on
    runs from one base are co-reachable (`coReachable_exec`), from which
    `clashBlocks_head_coReachable` says a `Cost` block carving accuses only live
    pairs — the floors were never the hole.
  * §2 `LiveSegmented`, `LiveIConfluent`, and `segmented_implies_liveSegmented`.
  * §3 the carrier: a three-slot uniqueness ceiling whose protocol can claim two
    of the three slots. Separation witness **#1** — the lattice-only clash
    `(sA, sC)`, which constrains `SegmentedIConfluent` and not `LiveSegmented` —
    and **#2** — the live clash `(sA, sB)`, which constrains both.
  * §4 **THE PRIZE**: `live_optimum_strictly_below_global_optimum`. The least `n`
    for which an `n`-domain live seam exists is **2**; the least `n` for which an
    `n`-domain global seam exists is **3**; and the third domain is charged for
    `(sA, sC)`, a pair no run of the protocol can produce.
  * §5 the live colouring: `liveSegmented_iff_liveProperColoring`. The safety
    clause's colouring characterisation survives protocol-relativisation **in
    full, and needs no covering pool**; the closure clause is untouched and still
    uncharacterised, with a live witness.
  * §6 the `SeamAlgebra` survival table, each row a theorem.

## Non-claims

  * ⟨TERMINAL⟩ Colouring still does not characterise the closure clause.
    `liveColoring_alone_does_not_segment` proves no such implication exists in the
    live setting either; the residual is `LiveSeamStableOn`, exactly.
  * ⟨TERMINAL⟩ `LiveSegmented` is **not** robust under enlarging `Op`. That is a
    property of the definition, not a gap: it quantifies over the runs of the `P`
    it is given. This is the whole reason the global certificate is kept.
  * ⟨PREMISE U-0092⟩ **Faithfulness of `P` is the modeller's.** Nothing here checks that a
    `RunModel`'s `step` is the protocol the deployment actually runs. A live
    certificate issued against an over-permissive `P` is weaker than it looks, and
    against an under-permissive `P` it is unsound for the real deployment. This is
    `Bounds.lean`'s "occupancy is only as sound as `step`", inherited verbatim.
  * ⟨TERMINAL⟩ **`crossings` can gap, but not on §3's two-branch clash.** The
    counts there still coincide (`workload_crossings_coincide`), and §1's
    `coReachable_exec` still explains why a block floor cannot accuse an
    unreachable pair. `CliqueLive.atMostTwo_live_global_crossing_gap` now gives
    the missing achievable separation on the sibling ceiling: one honest live
    strategy pays `0`, every global seam pays at least `1`, and a global seam
    paying exactly `1` is exhibited. The force comes from global fiber stability
    closing three same-coloured legal generators into their illegal triple join.
  * ⟨DONE U-0093 — see `Uwueave.FiniteProductSearch`⟩ **Minimum live
    colourings on an explicit finite scope.**
    `synthesizeMinimumLiveSeamCapped` exhaustively searches the supplied
    proof-carrying finite carrier and palette; its result carries either a
    least valid strategy or exhaustive semantic refusal, and it refuses before
    enumeration when a work cap is exceeded. The Slot fixture admits that
    capped search and independently certifies live width `2`. This is
    deliberately bounded: it neither enumerates an arbitrary carrier nor
    invents an unbounded palette, and its objective is the number of colours
    used on the declared carrier, not `ForkGrade.liveCost`.
  * Classical logic: the properness ⇒ safety direction is excluded middle on
    `I (x ⊔ y)`, exactly as in `SeamColoring.separatesOn_of_properColoring`.
    `Classical.byContradiction` is Lean's, not an added axiom.

## Overlap with `Uwueave.LiveCost`

A sibling lane is building `Uwueave/LiveCost.lean` over abstract *paths*. This
file deliberately does not import it: `RunModel`, `Reachable` and `CoReachable`
here are defined locally over `Cost.run`, and if that file grows its own
reachability vocabulary the two should be merged onto one definition rather than
left to agree by coincidence. The merge point is §1 and nothing else.

Literature: Bailis et al., VLDB 2015 (I-confluence); Whittaker–Hellerstein, VLDB
2019 (segmentation); the co-reachability reading and the strategy-space diagnosis
are codex's third review.
-/
import Uwueave.SeamColoring

namespace Uwueave.LiveSegmented

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.SeamAlgebra Uwueave.SeamColoring
open Uwueave.Cost

universe u v w z t r p q k

/-! ## §1. The interface — a protocol, its runs, and co-reachability.

The minimum a protocol-relative judgement needs is: *which pairs of worlds can a
single execution fork into?* That is `CoReachable`, and it is the only thing
`LiveSegmented` asks of a `RunModel`. -/

/-- **A run model.** A world type `W`, an op alphabet, a local transition, and an
`observe` that reads off the replicated lattice state a world presents.

Codex's sketch writes `RunModel S Op`, eliding the world type; worlds and states
are kept apart here because the whole content of §3 is a protocol whose worlds
cannot reach a state the lattice contains. When `W = S` and `observe = id` the two
readings coincide, and `slotProtocol` below is of that shape. -/
structure RunModel (W : Type u) (Op : Type v) (S : Type w) where
  /-- The local transition: what one op does to one world. -/
  step : W → Op → W
  /-- The replicated state a world presents to the merge lattice. -/
  observe : W → S

/-- Running an op stream from a world. This is `Cost.run` on `P.step`, on purpose:
every `Cost` theorem about runs applies to a `RunModel` unchanged. -/
def RunModel.exec {W : Type u} {Op : Type v} {S : Type w}
    (P : RunModel W Op S) (base : W) (ops : List Op) : W :=
  Cost.run P.step base ops

@[simp] theorem RunModel.exec_nil {W : Type u} {Op : Type v} {S : Type w}
    (P : RunModel W Op S) (base : W) : P.exec base [] = base := rfl

theorem RunModel.exec_append {W : Type u} {Op : Type v} {S : Type w}
    (P : RunModel W Op S) (base : W) (ops₁ ops₂ : List Op) :
    P.exec base (ops₁ ++ ops₂) = P.exec (P.exec base ops₁) ops₂ :=
  Cost.run_append P.step base ops₁ ops₂

/-- **Reachability**: `x` is some run of the protocol away from `base`. -/
def Reachable {W : Type u} {Op : Type v} {S : Type w}
    (P : RunModel W Op S) (base x : W) : Prop :=
  ∃ ops : List Op, P.exec base ops = x

/-- **Co-reachability — the fork shape, and the whole of what the live judgement
needs.** Two worlds are co-reachable when *one* execution could have produced
both: they are runs from a common base. This is exactly the situation in which two
replicas can hold both states at once and be asked to merge them.

Note what is *not* required: no bound on the base, and no relation to a designated
genesis. Quantifying over every base is the conservative reading — a pair is live
as soon as **some** world reaches both — so a `LiveSegmented` certificate never
excuses a merge on the grounds that a particular start state was assumed. -/
def CoReachable {W : Type u} {Op : Type v} {S : Type w}
    (P : RunModel W Op S) (base x y : W) : Prop :=
  Reachable P base x ∧ Reachable P base y

theorem reachable_refl {W : Type u} {Op : Type v} {S : Type w}
    (P : RunModel W Op S) (base : W) : Reachable P base base :=
  ⟨[], rfl⟩

theorem reachable_trans {W : Type u} {Op : Type v} {S : Type w}
    {P : RunModel W Op S} {a b c : W}
    (hab : Reachable P a b) (hbc : Reachable P b c) : Reachable P a c := by
  obtain ⟨ops₁, h₁⟩ := hab
  obtain ⟨ops₂, h₂⟩ := hbc
  exact ⟨ops₁ ++ ops₂, by rw [RunModel.exec_append, h₁, h₂]⟩

theorem coReachable_symm {W : Type u} {Op : Type v} {S : Type w}
    {P : RunModel W Op S} {base x y : W} (h : CoReachable P base x y) :
    CoReachable P base y x :=
  ⟨h.2, h.1⟩

theorem coReachable_self {W : Type u} {Op : Type v} {S : Type w}
    (P : RunModel W Op S) (base : W) : CoReachable P base base base :=
  ⟨reachable_refl P base, reachable_refl P base⟩

/-- **Any two runs from one base are co-reachable.** Trivial, and load-bearing:
it is why a `Cost`-style block floor can never accuse a non-live pair. Every clash
`Cost.ClashBlocks` carves out is between states on runs from a common start, so
the *floor* is live-sound already; the hole codex found is in the **strategy
space**, not the floor. -/
theorem coReachable_exec {W : Type u} {Op : Type v} {S : Type w}
    (P : RunModel W Op S) (base : W) (ops₁ ops₂ : List Op) :
    CoReachable P base (P.exec base ops₁) (P.exec base ops₂) :=
  ⟨⟨ops₁, rfl⟩, ⟨ops₂, rfl⟩⟩

/-- **The block calculus only ever accuses a live pair.** A `Cost.ClashBlocks`
carving names, at its head, the pair `(base, exec base b)` — and that pair is a
fork of one execution by construction. So `Cost`'s coordination floors are
already live-sound, and codex's second hole is not in them.

(Stated for a model whose worlds *are* its states, which is the shape `Cost`'s
`step : S → Op → S` assumes; `slotProtocol` is of that shape.) -/
theorem clashBlocks_head_coReachable {W : Type u} {Op : Type v} [MergeState W]
    {I : Invariant W} {P : RunModel W Op W} {base : W} {b : List Op}
    {bs : List (List Op)} (h : Cost.ClashBlocks I P.step base (b :: bs)) :
    CoReachable P base base (P.exec base b) ∧ Clashes I base (P.exec base b) := by
  have h' : I base ∧ I (Cost.run P.step base b) ∧ ¬ I (base ⊔ Cost.run P.step base b)
      ∧ Cost.ClashBlocks I P.step (Cost.run P.step base b) bs := h
  exact ⟨⟨reachable_refl P base, ⟨b, rfl⟩⟩, ⟨h'.1, h'.2.1, h'.2.2.1⟩⟩

/-! ## §2. The protocol-relative judgement. -/

/-- **Live segmented I-confluence** — codex's prescription, verbatim. The
lattice-global quantifier `∀ x y : S` is replaced by "over every pair of worlds a
single execution could fork into", and everything else is `SegmentedIConfluent`
unchanged: inside a fiber, merges preserve `I` **and** stay in the fiber.

This is the certificate a deployment budget should be optimised over, and it is
valid for the operational substrate `P` alone. -/
def LiveSegmented {W : Type u} {Op : Type v} {S : Type w} {Seg : Type z}
    [MergeState S] (P : RunModel W Op S) (σ : S → Seg) (I : Invariant S) : Prop :=
  ∀ base x y : W, CoReachable P base x y →
    σ (P.observe x) = σ (P.observe y) → I (P.observe x) → I (P.observe y) →
    I (P.observe x ⊔ P.observe y) ∧ σ (P.observe x ⊔ P.observe y) = σ (P.observe x)

/-- **Live I-confluence** — the same relativisation applied to `IConfluent`. A
protocol can make an invariant coordination-free without the invariant being
coordination-free: every clash it has may be unreachable. §6 needs this, because
`left_only_seam_iff` does not survive protocol-relativisation with the *global*
`IConfluent` on its right-hand side. -/
def LiveIConfluent {W : Type u} {Op : Type v} {S : Type w}
    [MergeState S] (P : RunModel W Op S) (I : Invariant S) : Prop :=
  ∀ base x y : W, CoReachable P base x y →
    I (P.observe x) → I (P.observe y) → I (P.observe x ⊔ P.observe y)

/-- **The global certificate is strictly stronger** — this direction is free, and
§3's witness #1 is the strictness. Read as a discipline: a `SegmentedIConfluent`
proof is a live certificate for *every* protocol at once, present and future, and
that is what buys its robustness under op-vocabulary growth. -/
theorem segmented_implies_liveSegmented {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} [MergeState S] {P : RunModel W Op S} {σ : S → Seg} {I : Invariant S}
    (h : SegmentedIConfluent σ I) : LiveSegmented P σ I :=
  fun _ x y _ hσ hx hy => h (P.observe x) (P.observe y) hσ hx hy

/-- **Global fiber stability closes three same-coloured legal states.** First
merge `x` with `y`; the global segmented judgement proves both legality and that
the join stays in their fiber. It can therefore be merged with same-coloured
`z`, proving the triple join legal and still in the original fiber.

This is stronger than pairwise proper colouring: the intermediate join need not
be a protocol world. `CliqueLive` uses exactly this global second application to
force a crossing on a scenario whose three live generators do not pairwise
clash. -/
theorem segmented_same_fiber_triple {S : Type w} {Seg : Type z} [MergeState S]
    {σ : S → Seg} {I : Invariant S} {x y z : S}
    (hseg : SegmentedIConfluent σ I) (hxy : σ x = σ y) (hxz : σ x = σ z)
    (hx : I x) (hy : I y) (hz : I z) :
    I ((x ⊔ y) ⊔ z) ∧ σ ((x ⊔ y) ⊔ z) = σ x := by
  obtain ⟨hIxy, hσxy⟩ := hseg x y hxy hx hy
  have hσxyz : σ (x ⊔ y) = σ z := hσxy.trans hxz
  obtain ⟨hIxyz, hσxyz'⟩ := hseg (x ⊔ y) z hσxyz hIxy hz
  exact ⟨hIxyz, hσxyz'.trans hσxy⟩

theorem iconfluent_implies_liveIConfluent {W : Type u} {Op : Type v} {S : Type w}
    [MergeState S] {P : RunModel W Op S} {I : Invariant S}
    (h : IConfluent I) : LiveIConfluent P I :=
  fun _ x y _ hx hy => h (P.observe x) (P.observe y) hx hy

/-- The live mirror of `Segmented.iconfluent_iff_trivially_segmented`: live
segmentation with one segment *is* live I-confluence. So the relativisation is
conservative in the same sense the segmentation refinement was. -/
theorem liveIConfluent_iff_trivially_liveSegmented {W : Type u} {Op : Type v}
    {S : Type w} [MergeState S] (P : RunModel W Op S) (I : Invariant S) :
    LiveIConfluent P I ↔ LiveSegmented P (fun _ => ()) I := by
  constructor
  · intro h base x y hco _ hx hy
    exact ⟨h base x y hco hx hy, rfl⟩
  · intro h base x y hco hx hy
    exact (h base x y hco rfl hx hy).1

/-- **A live clash constrains both judgements.** This is codex's required witness
shape #2 in general form: when the clashing pair really is a fork of one
execution, protocol-relativisation buys nothing at all, and the live optimum
inherits the constraint. -/
theorem live_clash_constrains_both {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} [MergeState S] {P : RunModel W Op S} {I : Invariant S}
    {base x y : W} (hco : CoReachable P base x y)
    (hc : Clashes I (P.observe x) (P.observe y)) :
    (∀ σ : S → Seg, LiveSegmented P σ I → σ (P.observe x) ≠ σ (P.observe y))
    ∧ (∀ σ : S → Seg, SegmentedIConfluent σ I → σ (P.observe x) ≠ σ (P.observe y)) :=
  ⟨fun _ hseg he => hc.2.2 (hseg base x y hco he hc.1 hc.2.1).1,
   fun _ hseg he => hc.2.2 (hseg _ _ he hc.1 hc.2.1).1⟩

/-- **The cost floor survives protocol-relativisation intact** — the live mirror
of `SeamColoring.clash_edge_forces_crossing`. If two runs from a common base end
on clashing states then *every live seam* charges at least one crossing between
them. Combined with `coReachable_exec` (every block-calculus clash is live), this
says the `Cost` floors are exactly as good under the live certificate as under the
global one: nothing that was charged stops being charged. -/
theorem live_clash_edge_forces_crossing {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} [MergeState S] [DecidableEq Seg] {P : RunModel W Op S}
    {σ : S → Seg} {I : Invariant S} {base : W} {ops₁ ops₂ : List Op}
    (hseg : LiveSegmented P σ I)
    (hclash : Clashes I (P.observe (P.exec base ops₁)) (P.observe (P.exec base ops₂))) :
    1 ≤ crossings (fun x => σ (P.observe x)) P.step base ops₁
        + crossings (fun x => σ (P.observe x)) P.step base ops₂ := by
  rcases Nat.eq_zero_or_pos (crossings (fun x => σ (P.observe x)) P.step base ops₁
      + crossings (fun x => σ (P.observe x)) P.step base ops₂) with h | h
  · exfalso
    have h1 : crossings (fun x => σ (P.observe x)) P.step base ops₁ = 0 := by omega
    have h2 : crossings (fun x => σ (P.observe x)) P.step base ops₂ = 0 := by omega
    have e1 := sigma_const_of_crossings_eq_zero h1
    have e2 := sigma_const_of_crossings_eq_zero h2
    exact hclash.2.2
      (hseg base (P.exec base ops₁) (P.exec base ops₂) (coReachable_exec P base ops₁ ops₂)
        (e1.trans e2.symm) hclash.1 hclash.2.1).1
  · exact h

/-! ## §3. The carrier — a uniqueness ceiling with a slot the protocol cannot claim.

Three slots, at most one of them claimed. The lattice is grow-only, so the clash
graph on legal states is a **triangle**: any two distinct single claims merge into
a double claim. The protocol, however, has operations for two of the three slots
only — the third is an administrative/legacy state that exists in the state type
and that no run produces. -/

/-- Three claimable slots, as three grow-only flags. -/
structure Slots where
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq, Repr

/-- The grow-only join: claims accumulate. -/
def Slots.join (x y : Slots) : Slots := ⟨x.a || y.a, x.b || y.b, x.c || y.c⟩

theorem Slots.join_comm (x y : Slots) : x.join y = y.join x := by
  show Slots.mk (x.a || y.a) (x.b || y.b) (x.c || y.c)
      = Slots.mk (y.a || x.a) (y.b || x.b) (y.c || x.c)
  rw [Bool.or_comm x.a y.a, Bool.or_comm x.b y.b, Bool.or_comm x.c y.c]

theorem Slots.join_assoc (x y z : Slots) : (x.join y).join z = x.join (y.join z) := by
  show Slots.mk ((x.a || y.a) || z.a) ((x.b || y.b) || z.b) ((x.c || y.c) || z.c)
      = Slots.mk (x.a || (y.a || z.a)) (x.b || (y.b || z.b)) (x.c || (y.c || z.c))
  rw [Bool.or_assoc, Bool.or_assoc, Bool.or_assoc]

theorem Slots.join_idem (x : Slots) : x.join x = x := by
  show Slots.mk (x.a || x.a) (x.b || x.b) (x.c || x.c) = x
  rw [Bool.or_self, Bool.or_self, Bool.or_self]

instance : MergeState Slots where
  merge := Slots.join
  merge_comm := Slots.join_comm
  merge_assoc := Slots.join_assoc
  merge_idem := Slots.join_idem

/-- The uniqueness ceiling, as a `Bool` so every instance below is `decide`-able. -/
def atMostOneB (s : Slots) : Bool :=
  !(s.a && s.b) && !(s.a && s.c) && !(s.b && s.c)

/-- **At most one slot is claimed** — `Catalog.gset_atMostOne_not_iconfluent`'s
shape over three candidates. -/
def atMostOne : Invariant Slots := fun s => atMostOneB s = true

instance : DecidablePred atMostOne :=
  fun s => inferInstanceAs (Decidable (atMostOneB s = true))

/-- Nothing claimed. -/
def sO : Slots := ⟨false, false, false⟩
/-- Slot A claimed — the protocol has an op for this. -/
def sA : Slots := ⟨true, false, false⟩
/-- Slot B claimed — the protocol has an op for this. -/
def sB : Slots := ⟨false, true, false⟩
/-- Slot C claimed — **no op of the protocol produces this**, and no run can leave
or enter it, because every step preserves the `c` flag. -/
def sC : Slots := ⟨false, false, true⟩

/-- The four legal states, enumerated. -/
theorem legal_cases (s : Slots) (h : atMostOne s) :
    s = sO ∨ s = sA ∨ s = sB ∨ s = sC := by
  obtain ⟨a, b, c⟩ := s
  revert h
  cases a <;> cases b <;> cases c <;> decide

/-- **The clash graph on legal states is a triangle** — every two distinct claims
merge into an illegal double claim, and the empty state clashes with nothing. -/
theorem slots_clash_graph :
    Clashes atMostOne sA sB ∧ Clashes atMostOne sA sC ∧ Clashes atMostOne sB sC
    ∧ ¬ Clashes atMostOne sO sA ∧ ¬ Clashes atMostOne sO sB
    ∧ ¬ Clashes atMostOne sO sC := by decide

/-- The protocol's op alphabet: it can claim slot A or slot B. There is no
`claimC`. -/
inductive ClaimOp
  | claimA
  | claimB
  deriving DecidableEq, Repr

/-- The local transition. Note that `c` is untouched by both ops — that single
fact is the whole of §3's unreachability. -/
def claimStep (s : Slots) : ClaimOp → Slots
  | .claimA => { s with a := true }
  | .claimB => { s with b := true }

/-- **The deployed protocol.** Worlds are states (`observe = id`), so this is a
run model of exactly the shape codex's `RunModel S Op` sketch assumes. -/
def slotProtocol : RunModel Slots ClaimOp Slots where
  step := claimStep
  observe := fun s => s

theorem claimStep_preserves_c (s : Slots) (o : ClaimOp) : (claimStep s o).c = s.c := by
  cases o <;> rfl

/-- No run touches the `c` flag. -/
theorem exec_preserves_c (base : Slots) (ops : List ClaimOp) :
    (slotProtocol.exec base ops).c = base.c := by
  induction ops generalizing base with
  | nil => rfl
  | cons o ops ih =>
      show (slotProtocol.exec (claimStep base o) ops).c = base.c
      rw [ih (claimStep base o), claimStep_preserves_c]

/-- **Co-reachable worlds agree on the `c` flag.** This is the operational fact
the whole separation rests on: the protocol cannot fork an execution into a
`c`-claimed world and a `c`-free one, because it can do neither of setting nor
clearing `c`. -/
theorem coReachable_sameC {base x y : Slots}
    (h : CoReachable slotProtocol base x y) : x.c = y.c := by
  obtain ⟨⟨ops₁, h₁⟩, ⟨ops₂, h₂⟩⟩ := h
  rw [← h₁, ← h₂, exec_preserves_c, exec_preserves_c]

/-- The two claimable slots really do fork one execution: `sO` reaches both. -/
theorem sA_sB_coReachable : CoReachable slotProtocol sO sA sB :=
  ⟨⟨[ClaimOp.claimA], rfl⟩, ⟨[ClaimOp.claimB], rfl⟩⟩

/-- ⚠ **…and slot C forks with nothing.** No world whatever reaches both `sA` and
`sC`; likewise `sB` and `sC`. The pairs are in the lattice and out of the
protocol. -/
theorem sA_sC_not_coReachable (base : Slots) :
    ¬ CoReachable slotProtocol base sA sC :=
  fun h => absurd (coReachable_sameC h) (by decide)

theorem sB_sC_not_coReachable (base : Slots) :
    ¬ CoReachable slotProtocol base sB sC :=
  fun h => absurd (coReachable_sameC h) (by decide)

/-- Every live question about this protocol reduces to a question about legal
states with a common `c` flag. (Sufficient, not necessary — it is weaker than
co-reachability and therefore proves more than is needed.) -/
theorem liveSegmented_of_sameC {Seg : Type z} {σ : Slots → Seg}
    (h : ∀ x y : Slots, atMostOne x → atMostOne y → x.c = y.c → σ x = σ y →
        atMostOne (x ⊔ y) ∧ σ (x ⊔ y) = σ x) :
    LiveSegmented slotProtocol σ atMostOne :=
  fun _ x y hco hσ hx hy => h x y hx hy (coReachable_sameC hco) hσ

/-! ### The two seams the separation is drawn with -/

/-- **The two-domain live seam**: "is slot B claimed?". It separates `sA` from
`sB` — the live clash — and puts `sC` in the same fiber as `sA`, which is
forbidden globally and invisible live. -/
def sigmaLive (s : Slots) : Fin 2 := if s.b = true then 1 else 0

/-- **The three-domain global seam**: one domain per claimable slot, with the
empty state riding along with slot A. -/
def sigmaGlobal (s : Slots) : Fin 3 :=
  if s.b = true then 1 else if s.c = true then 2 else 0

/-- A seam that is blind to the live clash and sees only the unreachable one —
the mirror image of `sigmaLive`, and the witness that a live certificate is not
free for the asking. -/
def sigmaBlind (s : Slots) : Fin 2 := if s.c = true then 1 else 0

theorem sigmaLive_liveSegmented : LiveSegmented slotProtocol sigmaLive atMostOne := by
  apply liveSegmented_of_sameC
  intro x y hx hy hc hσ
  rcases legal_cases x hx with rfl | rfl | rfl | rfl <;>
    rcases legal_cases y hy with rfl | rfl | rfl | rfl <;>
      revert hc hσ <;> decide

theorem sigmaGlobal_segmented : SegmentedIConfluent sigmaGlobal atMostOne := by
  intro x y hσ hx hy
  rcases legal_cases x hx with rfl | rfl | rfl | rfl <;>
    rcases legal_cases y hy with rfl | rfl | rfl | rfl <;>
      revert hσ <;> decide

/-! ### ⚠ Separation witness #1 — a lattice-only clash that constrains the global
judgement and not the live one.

This is the pair codex's argument is about: `sA` and `sC` are both legal, their
merge is illegal, so `SegmentedIConfluent` requires every seam to separate them —
and no execution of the protocol can hold both, so `LiveSegmented` does not. The
two-domain seam `sigmaLive` is the difference made concrete: live-valid,
globally refuted, and refuted *exactly* at this pair. -/

theorem witness_one_latticeOnly_clash :
    Clashes atMostOne sA sC
    ∧ (∀ base : Slots, ¬ CoReachable slotProtocol base sA sC)
    ∧ LiveSegmented slotProtocol sigmaLive atMostOne
    ∧ sigmaLive sA = sigmaLive sC
    ∧ ¬ SegmentedIConfluent sigmaLive atMostOne :=
  ⟨by decide, sA_sC_not_coReachable, sigmaLive_liveSegmented, by decide,
   fun h => not_segmented_of_monochromatic (by decide : Clashes atMostOne sA sC)
     (by decide : sigmaLive sA = sigmaLive sC) h⟩

/-- The same fact stated as a constraint on the *strategy space*, which is the
form codex's diagnosis takes: every global seam is required to separate a pair
that no live path can charge. -/
theorem latticeOnly_pair_constrains_every_global_seam {Seg : Type z}
    (σ : Slots → Seg) (h : SegmentedIConfluent σ atMostOne) : σ sA ≠ σ sC :=
  fun he => not_segmented_of_monochromatic (by decide : Clashes atMostOne sA sC) he h

/-! ### Separation witness #2 — a live clash that constrains both. -/

theorem witness_two_live_clash :
    Clashes atMostOne sA sB
    ∧ CoReachable slotProtocol sO sA sB
    ∧ sigmaBlind sA = sigmaBlind sB
    ∧ ¬ LiveSegmented slotProtocol sigmaBlind atMostOne
    ∧ ¬ SegmentedIConfluent sigmaBlind atMostOne := by
  have hc : Clashes atMostOne sA sB := by decide
  have hboth := live_clash_constrains_both (Seg := Fin 2) sA_sB_coReachable hc
  exact ⟨hc, sA_sB_coReachable, by decide,
    fun h => hboth.1 sigmaBlind h (by decide),
    fun h => hboth.2 sigmaBlind h (by decide)⟩

/-! ## §4. THE PRIZE — a protocol whose live optimum is strictly below its global one.

"Strategy" = a seam; "optimum" = the least number of coordination domains a valid
seam can partition the state space into, i.e. the least `n` admitting a seam into
`Fin n`. A deployment builds one coordination mechanism per domain, so this is a
quantity a budget is actually spent on.

The result: **live optimum 2, global optimum 3.** The third domain exists solely
to separate `sA` from `sC`, and §3 proves no execution of the protocol can produce
that pair. An unreachable clash was making the deployment pay. -/

/-- A seam into `n` coordination domains. -/
def LiveWidth {W : Type u} {Op : Type v} {S : Type w} [MergeState S]
    (P : RunModel W Op S) (I : Invariant S) (n : Nat) : Prop :=
  ∃ σ : S → Fin n, LiveSegmented P σ I

/-- The same, for the carrier-global certificate. -/
def GlobalWidth {S : Type w} [MergeState S] (I : Invariant S) (n : Nat) : Prop :=
  ∃ σ : S → Fin n, SegmentedIConfluent σ I

/-- `n` is the optimum of `F`: feasible, and no smaller width is. -/
def LeastSuch (F : Nat → Prop) (n : Nat) : Prop := F n ∧ ∀ m, F m → n ≤ m

/-- Renaming the domains injectively preserves a live certificate — a seam is its
fiber partition, and an injective recolouring keeps it. -/
theorem liveSegmented_map {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} {Seg' : Type t} [MergeState S] {P : RunModel W Op S}
    {σ : S → Seg} {I : Invariant S} (f : Seg → Seg')
    (hinj : ∀ p q : Seg, f p = f q → p = q) (h : LiveSegmented P σ I) :
    LiveSegmented P (fun s => f (σ s)) I := by
  intro base x y hco hσ hx hy
  have h' := h base x y hco (hinj _ _ hσ) hx hy
  exact ⟨h'.1, congrArg f h'.2⟩

theorem segmented_map {S : Type w} {Seg : Type z} {Seg' : Type t} [MergeState S]
    {σ : S → Seg} {I : Invariant S} (f : Seg → Seg')
    (hinj : ∀ p q : Seg, f p = f q → p = q) (h : SegmentedIConfluent σ I) :
    SegmentedIConfluent (fun s => f (σ s)) I := by
  intro x y hσ hx hy
  have h' := h x y (hinj _ _ hσ) hx hy
  exact ⟨h'.1, congrArg f h'.2⟩

/-- Widening the domain count, as an injection. -/
def finCastLE {m n : Nat} (h : m ≤ n) (i : Fin m) : Fin n :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

theorem finCastLE_inj {m n : Nat} (h : m ≤ n) (p q : Fin m)
    (he : finCastLE h p = finCastLE h q) : p = q := by
  have hv : (finCastLE h p).val = (finCastLE h q).val := congrArg Fin.val he
  exact Fin.eq_of_val_eq hv

theorem liveWidth_mono {W : Type u} {Op : Type v} {S : Type w} [MergeState S]
    {P : RunModel W Op S} {I : Invariant S} {m n : Nat} (hmn : m ≤ n)
    (h : LiveWidth P I m) : LiveWidth P I n := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨fun s => finCastLE hmn (σ s), liveSegmented_map _ (finCastLE_inj hmn) hσ⟩

theorem globalWidth_mono {S : Type w} [MergeState S] {I : Invariant S} {m n : Nat}
    (hmn : m ≤ n) (h : GlobalWidth I m) : GlobalWidth I n := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨fun s => finCastLE hmn (σ s), segmented_map _ (finCastLE_inj hmn) hσ⟩

/-- One coordination domain is not enough for the live judgement either — the live
clash `(sA, sB)` is a real edge, so the live optimum is not a degenerate `1`. -/
theorem no_live_seam_into_fin_one (σ : Slots → Fin 1) :
    ¬ LiveSegmented slotProtocol σ atMostOne := by
  intro h
  have hone : ∀ p q : Fin 1, p = q := by decide
  have hbad := (h sO sA sB sA_sB_coReachable (hone _ _) (by decide) (by decide)).1
  exact absurd hbad (by decide)

/-- ⚠ **Two coordination domains are not enough globally** — the triangle. Any
`Fin 2`-valued seam gives two of the three claims the same colour, and those two
merge illegally. Note that the pigeonhole is discharged by `decide` on `Fin 2`,
so nothing here is a hand-waved counting argument. -/
theorem no_global_seam_into_fin_two (σ : Slots → Fin 2) :
    ¬ SegmentedIConfluent σ atMostOne := by
  intro h
  have hAB : σ sA ≠ σ sB :=
    fun he => (by decide : ¬ atMostOne (sA ⊔ sB)) (h sA sB he (by decide) (by decide)).1
  have hAC : σ sA ≠ σ sC :=
    fun he => (by decide : ¬ atMostOne (sA ⊔ sC)) (h sA sC he (by decide) (by decide)).1
  have hBC : σ sB ≠ σ sC :=
    fun he => (by decide : ¬ atMostOne (sB ⊔ sC)) (h sB sC he (by decide) (by decide)).1
  have pigeon : ∀ p q r : Fin 2, p ≠ q → p ≠ r → q ≠ r → False := by decide
  exact pigeon _ _ _ hAB hAC hBC

theorem live_least_width : LeastSuch (LiveWidth slotProtocol atMostOne) 2 := by
  refine ⟨⟨sigmaLive, sigmaLive_liveSegmented⟩, ?_⟩
  intro m hm
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · obtain ⟨σ, hσ⟩ := liveWidth_mono (show m ≤ 1 by omega) hm
    exact absurd hσ (no_live_seam_into_fin_one σ)
  · exact hge

theorem global_least_width : LeastSuch (GlobalWidth atMostOne) 3 := by
  refine ⟨⟨sigmaGlobal, sigmaGlobal_segmented⟩, ?_⟩
  intro m hm
  rcases Nat.lt_or_ge m 3 with hlt | hge
  · obtain ⟨σ, hσ⟩ := globalWidth_mono (show m ≤ 2 by omega) hm
    exact absurd hσ (no_global_seam_into_fin_two σ)
  · exact hge

/-- ⚠⚠ **THE SECOND REACHABILITY HOLE, PRICED.** One protocol, one invariant, two
certificates, two optima: the live optimum is **2** and the global optimum is
**3**, and `2 < 3`.

Both halves are `LeastSuch`, so neither number is an upper bound that a cleverer
search might beat: the live seam is exhibited and one domain is refuted; the
global seam is exhibited and two domains are refuted. The gap is the cost of the
lattice-global quantifier, and §3's witness #1 names the pair it is spent on. -/
theorem live_optimum_strictly_below_global_optimum :
    LeastSuch (LiveWidth slotProtocol atMostOne) 2
    ∧ LeastSuch (GlobalWidth atMostOne) 3
    ∧ 2 < 3 :=
  ⟨live_least_width, global_least_width, by decide⟩

/-- **What the third domain is bought with.** The whole gap is one clash edge, and
that edge is a pair no execution of the protocol can hold at once. Read the
conjuncts as the audit trail: the pair clashes, no base forks into it, every
global seam must still separate it, and the two-domain live seam is valid
precisely because it does not. -/
theorem the_third_domain_is_charged_for_an_unreachable_pair :
    Clashes atMostOne sA sC
    ∧ (∀ base : Slots, ¬ CoReachable slotProtocol base sA sC)
    ∧ (∀ σ : Slots → Fin 3, SegmentedIConfluent σ atMostOne → σ sA ≠ σ sC)
    ∧ LiveSegmented slotProtocol sigmaLive atMostOne
    ∧ sigmaLive sA = sigmaLive sC :=
  ⟨by decide, sA_sC_not_coReachable,
   fun σ h => latticeOnly_pair_constrains_every_global_seam σ h,
   sigmaLive_liveSegmented, by decide⟩

/-- ⚠ **Where the gap is *not*: the crossing counts.** On the two-stream workload
that forks the live clash, the two-domain live seam and the three-domain global
seam charge the same `1` — and by `coReachable_exec` no `crossings` floor could
have separated them, because the states a block calculus accuses are always runs
from a common base and therefore live. Reported so that §4's number is not read as
a crossings result: the gap is in the number of coordination domains a deployment
must build, not in how often it crosses them. -/
theorem workload_crossings_coincide :
    crossings sigmaLive claimStep sO [ClaimOp.claimA] = 0
    ∧ crossings sigmaLive claimStep sO [ClaimOp.claimB] = 1
    ∧ jointCost sigmaLive claimStep sO [[ClaimOp.claimA], [ClaimOp.claimB]] = 1
    ∧ jointCost sigmaGlobal claimStep sO [[ClaimOp.claimA], [ClaimOp.claimB]] = 1 := by
  decide

/-! ## §5. The live colouring — which half of `segmented_iff_properColoring` survives.

`SeamColoring` characterises `SegmentedIConfluent`'s **safety** clause as a proper
colouring of the clash graph, and proves that its **closure** clause is exactly
what colouring cannot see. Relativised to a protocol, the same split holds — and
the colouring half comes out *better*: `segmented_iff_properColoring` needs a
covering pool `hV : ∀ s : S, s ∈ V`, and the live version needs nothing, because
the live vertex set is the quantifier's own domain rather than a list supplied
from outside. -/

/-- **The live clash graph.** Vertices are worlds; there is an edge when the two
worlds are co-reachable *and* their observations clash. Both conditions are
needed: co-reachability is what makes the pair a fork of one execution, the clash
is what makes the merge illegal. -/
def LiveClashes {W : Type u} {Op : Type v} {S : Type w} [MergeState S]
    (P : RunModel W Op S) (I : Invariant S) (base x y : W) : Prop :=
  CoReachable P base x y ∧ Clashes I (P.observe x) (P.observe y)

/-- A proper colouring of the live clash graph. -/
def LiveProperColoring {W : Type u} {Op : Type v} {S : Type w} {Seg : Type z}
    [MergeState S] (P : RunModel W Op S) (σ : S → Seg) (I : Invariant S) : Prop :=
  ∀ base x y : W, LiveClashes P I base x y → σ (P.observe x) ≠ σ (P.observe y)

/-- The safety clause, relativised: inside a fiber, merges of co-reachable legal
worlds are legal. -/
def LiveSeparates {W : Type u} {Op : Type v} {S : Type w} {Seg : Type z}
    [MergeState S] (P : RunModel W Op S) (σ : S → Seg) (I : Invariant S) : Prop :=
  ∀ base x y : W, CoReachable P base x y → I (P.observe x) → I (P.observe y) →
    σ (P.observe x) = σ (P.observe y) → I (P.observe x ⊔ P.observe y)

/-- The closure clause, relativised: fibers are merge-closed on co-reachable legal
worlds. `SeamAlgebra.SeamStableOn`'s protocol-relative form. -/
def LiveSeamStableOn {W : Type u} {Op : Type v} {S : Type w} {Seg : Type z}
    [MergeState S] (P : RunModel W Op S) (I : Invariant S) (σ : S → Seg) : Prop :=
  ∀ base x y : W, CoReachable P base x y → I (P.observe x) → I (P.observe y) →
    σ (P.observe x) = σ (P.observe y) → σ (P.observe x ⊔ P.observe y) = σ (P.observe x)

/-- Safety ⟹ properness, constructively. -/
theorem liveProperColoring_of_liveSeparates {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} [MergeState S] {P : RunModel W Op S} {σ : S → Seg} {I : Invariant S}
    (h : LiveSeparates P σ I) : LiveProperColoring P σ I :=
  fun base x y hlc hσ => hlc.2.2.2 (h base x y hlc.1 hlc.2.1 hlc.2.2.1 hσ)

/-- Properness ⟹ safety. ⚠ Classical, exactly as in
`SeamColoring.separatesOn_of_properColoring`. -/
theorem liveSeparates_of_liveProperColoring {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} [MergeState S] {P : RunModel W Op S} {σ : S → Seg} {I : Invariant S}
    (h : LiveProperColoring P σ I) : LiveSeparates P σ I :=
  fun base x y hco hx hy hσ =>
    Classical.byContradiction fun hbad => h base x y ⟨hco, hx, hy, hbad⟩ hσ

/-- **The live safety clause and the live colouring condition are the same
condition.** This is the exact analogue of
`SeamColoring.safetyClause_iff_properColoring` — and it carries **no covering-pool
hypothesis**, which the global statement cannot do without. -/
theorem liveSafetyClause_iff_liveProperColoring {W : Type u} {Op : Type v}
    {S : Type w} {Seg : Type z} [MergeState S] {P : RunModel W Op S} {σ : S → Seg}
    {I : Invariant S} : LiveSeparates P σ I ↔ LiveProperColoring P σ I :=
  ⟨liveProperColoring_of_liveSeparates, liveSeparates_of_liveProperColoring⟩

/-- **THE LIVE HEADLINE.** A live seam is a proper colouring of the *live* clash
graph, plus live fiber stability, and nothing else. Both conjuncts are
load-bearing: `liveColoring_alone_does_not_segment` refutes the colouring half
alone, and `sigmaBlind_liveSeamStable` refutes the stability half alone — witness
#2's seam is live-stable and still not a live seam. -/
theorem liveSegmented_iff_liveProperColoring {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} [MergeState S] {P : RunModel W Op S} {σ : S → Seg} {I : Invariant S} :
    LiveSegmented P σ I ↔ (LiveProperColoring P σ I ∧ LiveSeamStableOn P I σ) := by
  constructor
  · intro h
    exact ⟨liveProperColoring_of_liveSeparates
             (fun base x y hco hx hy hσ => (h base x y hco hσ hx hy).1),
           fun base x y hco hx hy hσ => (h base x y hco hσ hx hy).2⟩
  · intro ⟨hcol, hstab⟩ base x y hco hσ hx hy
    exact ⟨liveSeparates_of_liveProperColoring hcol base x y hco hx hy hσ,
           hstab base x y hco hx hy hσ⟩

/-- ⚠ **Stability alone is not enough either** — the other half of the headline's
load-bearing pair. Witness #2's seam is live-fiber-stable (a `c`-flag reading is a
merge homomorphism on co-reachable worlds, which all agree on `c`), and it is not
a live seam, because it fails to colour the one live edge. Together with
`liveColoring_alone_does_not_segment` this pins both conjuncts as necessary. -/
theorem sigmaBlind_liveSeamStable :
    LiveSeamStableOn slotProtocol atMostOne sigmaBlind
    ∧ ¬ LiveProperColoring slotProtocol sigmaBlind atMostOne := by
  refine ⟨?_, ?_⟩
  · intro _ x y hco hx hy hσ
    have hc := coReachable_sameC hco
    rcases legal_cases x hx with rfl | rfl | rfl | rfl <;>
      rcases legal_cases y hy with rfl | rfl | rfl | rfl <;>
        revert hc hσ <;> decide
  · intro h
    exact h sO sA sB ⟨sA_sB_coReachable, by decide⟩ (by decide)

/-- The direction that costs nothing: every live seam properly colours the live
clash graph. No classical logic, no finiteness. -/
theorem liveProperColoring_of_liveSegmented {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} [MergeState S] {P : RunModel W Op S} {σ : S → Seg} {I : Invariant S}
    (h : LiveSegmented P σ I) : LiveProperColoring P σ I :=
  (liveSegmented_iff_liveProperColoring.mp h).1

/-- Every global proper colouring over a pool that covers the observations is a
live proper colouring. (The converse is exactly what fails — witness #1.) -/
theorem liveProperColoring_of_properColoring {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} [MergeState S] {P : RunModel W Op S} {σ : S → Seg} {I : Invariant S}
    {V : List S} (hV : ∀ x : W, P.observe x ∈ V) (h : ProperColoring V σ I) :
    LiveProperColoring P σ I :=
  fun _ x y hlc => h (P.observe x) (hV x) (P.observe y) (hV y) hlc.2

/-- A conjunctive observation over grow-only flags — the shape
`SeamAlgebra.refinement_fails` is built from, here as a projection of `Slots`. -/
def tauBoth (s : Slots) : Bool := s.a && s.b

/-- ⚠ **The residual survives relativisation: a live proper colouring that is not
a live seam.** With the trivial invariant the live clash graph is edgeless, so
every projection colours it properly — and `tauBoth` is still not a live seam,
because `sA` and `sB` *are* co-reachable, agree on it, and their merge does not.

So the answer to "does `segmented_iff_properColoring`'s characterisation survive?"
is: **the safety half survives exactly and unconditionally; the closure half is
untouched and remains outside colouring's reach.** The live witness is strictly
better than the global one (`SeamColoring.coloring_alone_does_not_segment`) in one
respect: its refuting pair is realised by an actual fork of the protocol, not
merely present in the lattice. -/
theorem liveColoring_alone_does_not_segment :
    LiveProperColoring slotProtocol tauBoth (fun _ : Slots => True)
    ∧ ¬ LiveSegmented slotProtocol tauBoth (fun _ : Slots => True) := by
  refine ⟨fun _ _ _ hlc => absurd trivial hlc.2.2.2, ?_⟩
  intro h
  have hbad := (h sO sA sB sA_sB_coReachable (by decide) trivial trivial).2
  exact absurd hbad (by decide)

/-! ## §6. The `SeamAlgebra` laws under protocol-relativisation.

| law | verdict |
| --- | --- |
| `segmented_iff` (safety ∧ closure) | **survives** — `liveSegmented_iff` |
| colouring of the safety clause | **survives, and improves** — §5, no pool needed |
| product | **survives**, for the interleaving product run model (§6.1) |
| refinement | **fails**, as globally — and the live witness is stronger (§6.2) |
| `segmented_of_finer` (the repair) | **survives** with `LiveSeamStableOn` (§6.2) |
| `seam_substitute` | **survives, hypothesis weakens** to co-reachable pairs (§6.2) |
| `linked_segmented` | **survives** via the product model (§6.3) |
| `absorb_free_field` | **survives, hypothesis weakens** to `LiveIConfluent` (§6.4) |
| `left_only_seam_iff` | **needs relativising on BOTH sides** — with the global `IConfluent` on the right it FAILS (§6.4) |
| `seam_must_separate_*` | **survives for live clashes only** — the failure for lattice-only clashes IS witness #1 |
-/

/-- The two halves of the live judgement, named — the live `SeamAlgebra.segmented_iff`. -/
theorem liveSegmented_iff {W : Type u} {Op : Type v} {S : Type w} {Seg : Type z}
    [MergeState S] {P : RunModel W Op S} {σ : S → Seg} {I : Invariant S} :
    LiveSegmented P σ I ↔ (LiveSeparates P σ I ∧ LiveSeamStableOn P I σ) := by
  constructor
  · intro h
    exact ⟨fun base x y hco hx hy hσ => (h base x y hco hσ hx hy).1,
           fun base x y hco hx hy hσ => (h base x y hco hσ hx hy).2⟩
  · intro ⟨hsep, hstab⟩ base x y hco hσ hx hy
    exact ⟨hsep base x y hco hx hy hσ, hstab base x y hco hx hy hσ⟩

/-- **A live seam must separate every LIVE clash** — the live
`SeamAlgebra.seam_must_separate_*`. And this is the whole of what survives: for a
clash that is not live, `witness_one_latticeOnly_clash` is the counterexample. -/
theorem live_seam_must_separate_live_clash {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} [MergeState S] {P : RunModel W Op S} {σ : S → Seg} {I : Invariant S}
    (hseg : LiveSegmented P σ I) {base x y : W} (hco : CoReachable P base x y)
    (hc : Clashes I (P.observe x) (P.observe y)) :
    σ (P.observe x) ≠ σ (P.observe y) :=
  fun he => hc.2.2 (hseg base x y hco he hc.1 hc.2.1).1

/-! ### §6.1. The product law — survives, for the interleaving product. -/

/-- Left-injected ops of an interleaving. -/
def lefts {OpA : Type v} {OpB : Type t} : List (OpA ⊕ OpB) → List OpA
  | [] => []
  | .inl o :: ops => o :: lefts ops
  | .inr _ :: ops => lefts ops

/-- Right-injected ops of an interleaving. -/
def rights {OpA : Type v} {OpB : Type t} : List (OpA ⊕ OpB) → List OpB
  | [] => []
  | .inl _ :: ops => rights ops
  | .inr o :: ops => o :: rights ops

/-- **The interleaving product of two run models**: worlds are pairs, an op steps
exactly one side, and `observe` is componentwise. This is the protocol a two-field
document actually runs, and it is what makes the product law survive
relativisation — a run of the product projects to a run of each component. -/
def RunModel.prod {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r}
    (PA : RunModel WA OpA SA) (PB : RunModel WB OpB SB) :
    RunModel (WA × WB) (OpA ⊕ OpB) (SA × SB) where
  step := fun p o =>
    match o with
    | .inl a => (PA.step p.1 a, p.2)
    | .inr b => (p.1, PB.step p.2 b)
  observe := fun p => (PA.observe p.1, PB.observe p.2)

theorem prod_exec {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r}
    (PA : RunModel WA OpA SA) (PB : RunModel WB OpB SB)
    (p : WA × WB) (ops : List (OpA ⊕ OpB)) :
    (RunModel.prod PA PB).exec p ops
      = (PA.exec p.1 (lefts ops), PB.exec p.2 (rights ops)) := by
  induction ops generalizing p with
  | nil => rfl
  | cons o ops ih =>
      cases o with
      | inl a => exact ih (PA.step p.1 a, p.2)
      | inr b => exact ih (p.1, PB.step p.2 b)

theorem lefts_map_inl {OpA : Type v} {OpB : Type t} (ops : List OpA) :
    lefts (ops.map (Sum.inl : OpA → OpA ⊕ OpB)) = ops := by
  induction ops with
  | nil => rfl
  | cons o ops ih => show o :: lefts (ops.map Sum.inl) = o :: ops; rw [ih]

theorem rights_map_inl {OpA : Type v} {OpB : Type t} (ops : List OpA) :
    rights (ops.map (Sum.inl : OpA → OpA ⊕ OpB)) = ([] : List OpB) := by
  induction ops with
  | nil => rfl
  | cons _ ops ih => exact ih

theorem lefts_map_inr {OpA : Type v} {OpB : Type t} (ops : List OpB) :
    lefts (ops.map (Sum.inr : OpB → OpA ⊕ OpB)) = ([] : List OpA) := by
  induction ops with
  | nil => rfl
  | cons _ ops ih => exact ih

theorem rights_map_inr {OpA : Type v} {OpB : Type t} (ops : List OpB) :
    rights (ops.map (Sum.inr : OpB → OpA ⊕ OpB)) = ops := by
  induction ops with
  | nil => rfl
  | cons o ops ih => show o :: rights (ops.map Sum.inr) = o :: ops; rw [ih]

/-- Co-reachability in the product projects to the left component. -/
theorem coReachable_prod_left {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r}
    {PA : RunModel WA OpA SA} {PB : RunModel WB OpB SB} {base x y : WA × WB}
    (h : CoReachable (RunModel.prod PA PB) base x y) :
    CoReachable PA base.1 x.1 y.1 := by
  obtain ⟨⟨ops₁, h₁⟩, ⟨ops₂, h₂⟩⟩ := h
  refine ⟨⟨lefts ops₁, ?_⟩, ⟨lefts ops₂, ?_⟩⟩
  · rw [← h₁, prod_exec]
  · rw [← h₂, prod_exec]

/-- …and to the right component. -/
theorem coReachable_prod_right {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r}
    {PA : RunModel WA OpA SA} {PB : RunModel WB OpB SB} {base x y : WA × WB}
    (h : CoReachable (RunModel.prod PA PB) base x y) :
    CoReachable PB base.2 x.2 y.2 := by
  obtain ⟨⟨ops₁, h₁⟩, ⟨ops₂, h₂⟩⟩ := h
  refine ⟨⟨rights ops₁, ?_⟩, ⟨rights ops₂, ?_⟩⟩
  · rw [← h₁, prod_exec]
  · rw [← h₂, prod_exec]

/-- Planting a fixed right world: a left fork lifts to a product fork. This is the
ingredient `left_only_seam_iff`'s forward direction needs, and the reason the
interleaving product (rather than a synchronous one) is the right notion — a left
op must be able to leave the right component alone. -/
theorem coReachable_prod_of_left {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r}
    {PA : RunModel WA OpA SA} {PB : RunModel WB OpB SB} {baseA x y : WA}
    (h : CoReachable PA baseA x y) (b : WB) :
    CoReachable (RunModel.prod PA PB) (baseA, b) (x, b) (y, b) := by
  obtain ⟨⟨ops₁, h₁⟩, ⟨ops₂, h₂⟩⟩ := h
  refine ⟨⟨ops₁.map Sum.inl, ?_⟩, ⟨ops₂.map Sum.inl, ?_⟩⟩
  · rw [prod_exec, lefts_map_inl, rights_map_inl, h₁]; rfl
  · rw [prod_exec, lefts_map_inl, rights_map_inl, h₂]; rfl

theorem coReachable_prod_of_right {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r}
    {PA : RunModel WA OpA SA} {PB : RunModel WB OpB SB} {baseB x y : WB}
    (h : CoReachable PB baseB x y) (a : WA) :
    CoReachable (RunModel.prod PA PB) (a, baseB) (a, x) (a, y) := by
  obtain ⟨⟨ops₁, h₁⟩, ⟨ops₂, h₂⟩⟩ := h
  refine ⟨⟨ops₁.map Sum.inr, ?_⟩, ⟨ops₂.map Sum.inr, ?_⟩⟩
  · rw [prod_exec, lefts_map_inr, rights_map_inr, h₁]; rfl
  · rw [prod_exec, lefts_map_inr, rights_map_inr, h₂]; rfl

/-- **SURVIVES — the product law.** Two independently live-seamed components give
a live-seamed record over the pair seam, for the interleaving product protocol.
The proof is `SeamAlgebra.product_segmented`'s, with the co-reachability
projections doing the work the global version got for free. -/
theorem live_product_segmented {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r} {SegA : Type p} {SegB : Type q}
    [MergeState SA] [MergeState SB]
    {PA : RunModel WA OpA SA} {PB : RunModel WB OpB SB}
    {IA : Invariant SA} {IB : Invariant SB} {σA : SA → SegA} {σB : SB → SegB}
    (hA : LiveSegmented PA σA IA) (hB : LiveSegmented PB σB IB) :
    LiveSegmented (RunModel.prod PA PB) (fun p => (σA p.1, σB p.2))
      (fun p => IA p.1 ∧ IB p.2) := by
  intro base x y hco hσ hx hy
  have h1 : σA (PA.observe x.1) = σA (PA.observe y.1) := congrArg Prod.fst hσ
  have h2 : σB (PB.observe x.2) = σB (PB.observe y.2) := congrArg Prod.snd hσ
  have hA1 := hA base.1 x.1 y.1 (coReachable_prod_left hco) h1 hx.1 hy.1
  have hB1 := hB base.2 x.2 y.2 (coReachable_prod_right hco) h2 hx.2 hy.2
  refine ⟨⟨hA1.1, hB1.1⟩, ?_⟩
  show (σA (PA.observe x.1 ⊔ PA.observe y.1), σB (PB.observe x.2 ⊔ PB.observe y.2))
      = (σA (PA.observe x.1), σB (PB.observe x.2))
  rw [hA1.2, hB1.2]

/-! ### §6.2. Refinement — ⚠ still fails; substitution — survives, and weakens. -/

/-- **SURVIVES — the transporting half of refinement.** Coordinating more never
breaks live safety: same-fiber worlds of a finer projection are same-fiber worlds
of the coarser seam. -/
theorem live_refine_freeWithinSeam {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} {T : Type t} [MergeState S] {P : RunModel W Op S}
    {σ : S → Seg} {τ : S → T} {I : Invariant S}
    (hseg : LiveSegmented P σ I) (hfiner : Finer τ σ)
    {base x y : W} (hco : CoReachable P base x y)
    (hτ : τ (P.observe x) = τ (P.observe y))
    (hx : I (P.observe x)) (hy : I (P.observe y)) :
    I (P.observe x ⊔ P.observe y) :=
  (hseg base x y hco (hfiner _ _ hτ) hx hy).1

/-- **SURVIVES — the repair**, with the missing ingredient named exactly as
globally, only relativised: a finer projection is a live seam as soon as it is
itself live-fiber-stable. -/
theorem live_segmented_of_finer {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} {T : Type t} [MergeState S] {P : RunModel W Op S}
    {σ : S → Seg} {τ : S → T} {I : Invariant S}
    (hseg : LiveSegmented P σ I) (hfiner : Finer τ σ)
    (hstable : LiveSeamStableOn P I τ) : LiveSegmented P τ I :=
  fun base x y hco hτ hx hy =>
    ⟨(hseg base x y hco (hfiner _ _ hτ) hx hy).1, hstable base x y hco hx hy hτ⟩

/-- ⚠ **FAILS — refinement does not descend, live either.** The constant seam is a
live seam for the trivial invariant; `tauBoth` is finer than it; and `tauBoth` is
not a live seam. The invariant never breaks — it is the fiber that is left, which
is `SeamAlgebra.refinement_fails` exactly.

The live refutation is *stronger* than the global one: the refuting pair `(sA,
sB)` is a genuine fork of the protocol (`sA_sB_coReachable`), so this is not an
artefact of quantifying over states the deployment cannot occupy. A seam built
from a conjunctive observation over grow-only fields is bad under both
certificates. -/
theorem live_refinement_fails :
    LiveSegmented slotProtocol (fun _ : Slots => ()) (fun _ : Slots => True)
    ∧ Finer tauBoth (fun _ : Slots => ())
    ∧ ¬ LiveSegmented slotProtocol tauBoth (fun _ : Slots => True) :=
  ⟨fun _ _ _ _ _ _ _ => ⟨trivial, rfl⟩, fun _ _ _ => rfl,
   liveColoring_alone_does_not_segment.2⟩

/-- **SURVIVES, AND THE HYPOTHESIS WEAKENS — the seam-substitution engine.**
`SeamAlgebra.seam_substitute` asks that `τ` determine `σ` on *all* legal states;
the live version asks it only on co-reachable legal pairs. That is a strictly
easier obligation, and it is where a protocol-relative optimiser gets its extra
room: a substitution that a global checker rejects can be live-valid. -/
theorem live_seam_substitute {W : Type u} {Op : Type v} {S : Type w}
    {Seg : Type z} {T : Type t} [MergeState S] {P : RunModel W Op S}
    {σ : S → Seg} {τ : S → T} {I : Invariant S}
    (hseg : LiveSegmented P σ I)
    (hdet : ∀ base x y : W, CoReachable P base x y → I (P.observe x) → I (P.observe y) →
      τ (P.observe x) = τ (P.observe y) → σ (P.observe x) = σ (P.observe y))
    (hstable : LiveSeamStableOn P I τ) : LiveSegmented P τ I :=
  fun base x y hco hτ hx hy =>
    ⟨(hseg base x y hco (hdet base x y hco hx hy hτ) hx hy).1,
     hstable base x y hco hx hy hτ⟩

/-! ### §6.3. Seam merging — survives. -/

/-- **SURVIVES — the linked invariant over the pair seam.** -/
theorem live_linked_pair_segmented {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r} {SegA : Type p} {SegB : Type q}
    [MergeState SA] [MergeState SB]
    {PA : RunModel WA OpA SA} {PB : RunModel WB OpB SB}
    {IA : Invariant SA} {IB : Invariant SB} {σA : SA → SegA} {σB : SB → SegB}
    (g : SegA → SegB) (hA : LiveSegmented PA σA IA) (hB : LiveSegmented PB σB IB) :
    LiveSegmented (RunModel.prod PA PB) (fun p => (σA p.1, σB p.2))
      (LinkedInv IA IB σA σB g) := by
  intro base x y hco hσ hx hy
  have h1 : σA (PA.observe x.1) = σA (PA.observe y.1) := congrArg Prod.fst hσ
  have h2 : σB (PB.observe x.2) = σB (PB.observe y.2) := congrArg Prod.snd hσ
  have hA1 := hA base.1 x.1 y.1 (coReachable_prod_left hco) h1 hx.1 hy.1
  have hB1 := hB base.2 x.2 y.2 (coReachable_prod_right hco) h2 hx.2.1 hy.2.1
  refine ⟨⟨hA1.1, hB1.1, ?_⟩, ?_⟩
  · show σB (PB.observe x.2 ⊔ PB.observe y.2) = g (σA (PA.observe x.1 ⊔ PA.observe y.1))
    rw [hB1.2, hA1.2]
    exact hx.2.2
  · show (σA (PA.observe x.1 ⊔ PA.observe y.1), σB (PB.observe x.2 ⊔ PB.observe y.2))
        = (σA (PA.observe x.1), σB (PB.observe x.2))
    rw [hA1.2, hB1.2]

/-- **SURVIVES — the seam-merging theorem.** When well-formedness links the two
fields' seams, the document is live-segmented over field A's seam alone: two
coordination points collapse into one, protocol-relatively, by the same argument
that does it globally. -/
theorem live_linked_segmented {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r} {SegA : Type p} {SegB : Type q}
    [MergeState SA] [MergeState SB]
    {PA : RunModel WA OpA SA} {PB : RunModel WB OpB SB}
    {IA : Invariant SA} {IB : Invariant SB} {σA : SA → SegA} {σB : SB → SegB}
    (g : SegA → SegB) (hA : LiveSegmented PA σA IA) (hB : LiveSegmented PB σB IB) :
    LiveSegmented (RunModel.prod PA PB) (fun p => σA p.1)
      (LinkedInv IA IB σA σB g) := by
  refine live_seam_substitute (live_linked_pair_segmented g hA hB) ?_ ?_
  · intro _ x y _ hx hy hτ
    have e1 : σB (PB.observe x.2) = g (σA (PA.observe x.1)) := hx.2.2
    have e2 : σB (PB.observe y.2) = g (σA (PA.observe y.1)) := hy.2.2
    have e3 : σA (PA.observe x.1) = σA (PA.observe y.1) := hτ
    show (σA (PA.observe x.1), σB (PB.observe x.2))
        = (σA (PA.observe y.1), σB (PB.observe y.2))
    rw [e1, e2, e3]
  · intro base x y hco hx hy hτ
    show σA (PA.observe x.1 ⊔ PA.observe y.1) = σA (PA.observe x.1)
    exact (hA base.1 x.1 y.1 (coReachable_prod_left hco) hτ hx.1 hy.1).2

/-! ### §6.4. Absorption and the single-field characterisation.

`left_only_seam_iff` is the one law that does **not** survive as written. Its
right-hand side names `IConfluent IB` — a lattice-global judgement — inside a
statement whose left-hand side has been relativised, and the mixture is false. The
repair is to relativise both sides: `LiveIConfluent` is the honest right-hand
side, and §6.4's last theorem is the witness that the unrepaired form fails. -/

/-- A protocol for the same carrier that can claim slot A only. Its runs preserve
`b` and `c`, so *none* of the three clash edges is live: the invariant is
live-coordination-free without being coordination-free. -/
inductive ClaimAOp
  | claimA
  deriving DecidableEq, Repr

def claimAStep (s : Slots) : ClaimAOp → Slots
  | .claimA => { s with a := true }

def slotProtocolA : RunModel Slots ClaimAOp Slots where
  step := claimAStep
  observe := fun s => s

theorem execA_preserves_bc (base : Slots) (ops : List ClaimAOp) :
    (slotProtocolA.exec base ops).b = base.b ∧ (slotProtocolA.exec base ops).c = base.c := by
  induction ops generalizing base with
  | nil => exact ⟨rfl, rfl⟩
  | cons o ops ih =>
      show (slotProtocolA.exec (claimAStep base o) ops).b = base.b
        ∧ (slotProtocolA.exec (claimAStep base o) ops).c = base.c
      obtain ⟨h1, h2⟩ := ih (claimAStep base o)
      cases o
      exact ⟨h1, h2⟩

theorem coReachableA_sameBC {base x y : Slots}
    (h : CoReachable slotProtocolA base x y) : x.b = y.b ∧ x.c = y.c := by
  obtain ⟨⟨ops₁, h₁⟩, ⟨ops₂, h₂⟩⟩ := h
  obtain ⟨hb₁, hc₁⟩ := execA_preserves_bc base ops₁
  obtain ⟨hb₂, hc₂⟩ := execA_preserves_bc base ops₂
  exact ⟨by rw [← h₁, ← h₂, hb₁, hb₂], by rw [← h₁, ← h₂, hc₁, hc₂]⟩

/-- ⚠ **Live-coordination-free without being coordination-free.** The A-only
protocol never forks into any of the three clash pairs, so `atMostOne` is
`LiveIConfluent` for it — while remaining not `IConfluent` at all. This is the
strictness of `iconfluent_implies_liveIConfluent`, and it is what §6.4's last
theorem is built from. -/
theorem slotProtocolA_liveIConfluent : LiveIConfluent slotProtocolA atMostOne := by
  intro base x y hco hx hy
  obtain ⟨hb, hc⟩ := coReachableA_sameBC hco
  rcases legal_cases x hx with rfl | rfl | rfl | rfl <;>
    rcases legal_cases y hy with rfl | rfl | rfl | rfl <;>
      revert hb hc <;> decide

theorem atMostOne_not_iconfluent : ¬ IConfluent atMostOne := by
  intro h
  exact absurd (h sA sB (by decide) (by decide)) (by decide)

/-- **SURVIVES, AND THE HYPOTHESIS WEAKENS — free absorption.** A field that is
merely *live*-coordination-free rides the other field's seam for nothing. The
global law needs `IConfluent IB`; this needs only `LiveIConfluent PB IB`, which
§6.4 shows is strictly weaker. -/
theorem live_absorb_free_field {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r} {SegA : Type p}
    [MergeState SA] [MergeState SB]
    {PA : RunModel WA OpA SA} {PB : RunModel WB OpB SB}
    {IA : Invariant SA} {IB : Invariant SB} {σA : SA → SegA}
    (hA : LiveSegmented PA σA IA) (hB : LiveIConfluent PB IB) :
    LiveSegmented (RunModel.prod PA PB) (fun p => σA p.1)
      (fun p => IA p.1 ∧ IB p.2) := by
  intro base x y hco hσ hx hy
  have hA1 := hA base.1 x.1 y.1 (coReachable_prod_left hco) hσ hx.1 hy.1
  exact ⟨⟨hA1.1, hB base.2 x.2 y.2 (coReachable_prod_right hco) hx.2 hy.2⟩, hA1.2⟩

/-- **SURVIVES ONLY RELATIVISED — the single-field characterisation.** A seam that
reads only field A live-segments the unlinked conjunction **iff** it is a live
seam for field A *and field B is live-coordination-free*. Same shape as
`SeamAlgebra.left_only_seam_iff`, with `IConfluent` replaced by `LiveIConfluent`
on the right — and that replacement is not cosmetic: see
`live_left_only_seam_iff_needs_liveIConfluent`.

The inhabitance hypotheses are the same ones and are load-bearing for the same
reason; here they are *worlds* whose observations are legal, because the forward
direction must plant a legal value of the other field and then fork the protocol
around it. -/
theorem live_left_only_seam_iff {WA : Type u} {OpA : Type v} {SA : Type w}
    {WB : Type z} {OpB : Type t} {SB : Type r} {T : Type k}
    [MergeState SA] [MergeState SB]
    {PA : RunModel WA OpA SA} {PB : RunModel WB OpB SB}
    {IA : Invariant SA} {IB : Invariant SB} (τ : SA → T)
    {a₀ : WA} {b₀ : WB} (ha₀ : IA (PA.observe a₀)) (hb₀ : IB (PB.observe b₀)) :
    LiveSegmented (RunModel.prod PA PB) (fun p => τ p.1) (fun p => IA p.1 ∧ IB p.2)
      ↔ (LiveSegmented PA τ IA ∧ LiveIConfluent PB IB) := by
  constructor
  · intro h
    constructor
    · intro baseA x y hco hτ hx hy
      have hm := h (baseA, b₀) (x, b₀) (y, b₀) (coReachable_prod_of_left hco b₀)
        hτ ⟨hx, hb₀⟩ ⟨hy, hb₀⟩
      exact ⟨hm.1.1, hm.2⟩
    · intro baseB x y hco hx hy
      exact (h (a₀, baseB) (a₀, x) (a₀, y) (coReachable_prod_of_right hco a₀)
        rfl ⟨ha₀, hx⟩ ⟨ha₀, hy⟩).1.2
  · intro ⟨hA, hB⟩
    exact live_absorb_free_field hA hB

/-- ⚠ **…and the unrelativised form FAILS.** Take both components to be the slot
carrier under the A-only protocol, the left invariant trivial and the seam
constant. The left-hand side of `left_only_seam_iff` holds — because `atMostOne`
is live-coordination-free for that protocol — and `IConfluent atMostOne` is false.
So the global right-hand side cannot be concluded, and the law survives only with
`LiveIConfluent` in its place. -/
theorem live_left_only_seam_iff_needs_liveIConfluent :
    LiveSegmented (RunModel.prod slotProtocolA slotProtocolA)
        (fun p => (fun _ : Slots => ()) p.1)
        (fun p => (fun _ : Slots => True) p.1 ∧ atMostOne p.2)
    ∧ ¬ IConfluent atMostOne :=
  ⟨live_absorb_free_field
     (PA := slotProtocolA) (IA := fun _ : Slots => True) (σA := fun _ : Slots => ())
     (fun _ _ _ _ _ _ _ => ⟨trivial, rfl⟩) slotProtocolA_liveIConfluent,
   atMostOne_not_iconfluent⟩

end Uwueave.LiveSegmented
