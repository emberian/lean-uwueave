/-
# Uwueave.ForkGrade — the fork-aware quantity, and the zero that IS the modal zero.

`Bounds.lean` §4 found a disagreement and proved it rather than papering over it:
`zero_floor_does_not_imply_cfcs`. `Cost.pinStep` is inflationary, so
`clashBlocks_nil_of_inflationary` empties **every** clash decomposition of every
pin stream — the per-stream floor is identically zero — and yet **no**
implementation able to perform the two pins is CFCS. A quantity whose zero is
the modal "coordination is available" therefore did not exist in this tree.

**This file builds one, following an external reviewer's (codex's) diagnosis.**
His reading of the mismatch, which we adopt verbatim as the design constraint:

> The modal obstruction is: ∃ a common base and two DIVERGENT legal runs whose
> merge is illegal. The per-stream block floor asks: ∃ a legal state and a later
> COMPARABLE state on ONE stream whose merge is illegal. Inflationary execution
> kills the second while leaving the first intact.
> **Do not repair the linear quantity. Define a fork-aware quantity.**

## The object

A **`Scenario`** is a finite rooted execution: a root world and a finite list of
branch paths (§1). Its **worlds** are the root together with the target of every
execution edge; every world is reached from the root by a run of the scenario's
own ops, so *any two worlds are a legal partition pair* in the Bailis sense —
which is exactly the quantification `Necessity.MergeSafe` performs. The
**live clash graph** (§2) is `SeamColoring.Clashes` restricted to those worlds.

A **`LiveStrategy`** (§3) is codex's colouring, taken **protocol-relative**: a
proper colouring of the live clash graph over the scenario's worlds, plus fiber
stability over the same pool. That is exactly
`SeamColoring.SegmentedIConfluentOn` at the pool `sc.worlds step`, and §3 proves
the identification rather than asserting it. Cost is charged to **execution
edges whose endpoints change segment** (§4), and `liveCost_eq_edge_charges`
discharges that description against the sum of `Cost.crossings` the theorems
actually consume.

## The three theorems

**§5 — `liveScenario_optimum_eq_zero_iff_no_live_clash`.** The minimum over live
strategies of the edge-charged cost is `0` **iff** the scenario contains no live
clash. Forward: zero cost means every world is root-coloured, so two clashing
worlds would be monochromatic, contradicting properness. Reverse: with no live
clash the constant one-colour seam is a live strategy — properness holds because
there is no edge, stability because the seam is constant — and it pays nothing.
`liveFree_iff_no_live_clash` is the space-free core; the named theorem is the
`CoordEffect.optimum` form over an admissible space closed under the constant
strategy.

**⚠ Why protocol-relative.** codex flagged that the reverse direction fails if
strategies are global `SegmentedIConfluent` seams, because a clash *elsewhere in
the lattice* rejects the constant seam even when the scenario is clash-free.
§9 proves that dependency on this tree's own witness rather than restating it:
`const_seam_live_but_not_global` exhibits a scenario with no live clash whose
constant seam is a live strategy and is **not** a global seam, and
`const_segmented_iff_iconfluent` names the exact gap — globally, the constant
seam is admissible precisely when `IConfluent` holds, which is strictly stronger
than "this scenario has no live clash".

**§6 — `cfcs_iff_locallySafe_and_no_reachableClash`**, the theorem `Necessity`
was missing. `IsCFCS impl I ↔ LocallySafe impl I ∧ ¬ Nonempty (ReachableClash
impl I)`. Forward is `reachable_clash_refutes_cfcs`; the reverse uses local
safety to put both run endpoints in `I` and then *constructs* the reachable
clash an illegal merge would witness. Stated here, about `Necessity`'s
definitions, without editing that file.

**§7 — `cfcs_iff_locallySafe_and_all_finite_scenarios_zero`**, the composition,
which is the point. `IsCFCS impl I` holds **iff** the implementation is locally
safe and **every finite scenario it realizes from a legal root has live optimum
zero**. The modal judgement degenerates to a quantitative one — honestly, at the
fork-aware quantity, where `Bounds` §4 proved the per-stream one cannot.

## Non-claims, labelled

  * ⟨scope⟩ **Crossings are not meetings**, inherited whole from `Cost.lean` and
    `CoordEffect.lean`. Every `Nat` here is a seam change on an execution edge;
    nothing models attendance or coalescing.
  * ⟨scope⟩ **A shared prefix is charged once per branch.** `liveCost` sums
    `Cost.crossings` over the branch paths, so an edge two branches both traverse
    is counted twice. This is visible in `liveCost_eq_edge_charges`, which counts
    the edge *multiset*. It does not affect any theorem here: every statement is
    about the cost being zero or positive, and `List.countP` of a multiset is
    zero exactly when it is zero on the underlying set.
  * ⟨scope⟩ **Co-reachability is "both are worlds of this scenario".** The model
    is Bailis's two-partitions-then-join, in which every pair of states reachable
    from a common base may be synchronized; `worlds_runsTo` proves each world is
    so reachable under `Scenario.Realized`. A protocol with a happens-before
    constraint that forbids some sync is not modelled — that axis is
    `CausalReach`'s, and `Bounds` §7 records that no cost result in this tree
    takes it as a hypothesis.
  * ⟨scope⟩ `[DecidableEq Seg]` on every seam, inherited from `Cost.crossings`.
  * ⟨TERMINAL⟩ **A live-clash-free scenario need not admit a zero-cost global
    seam.** `global_triple_obstruction_cost_positive` is the generic floor:
    three legal scenario worlds with an illegal triple join force every global
    seam to pay at least `1`. `CliqueLive.atMostTwo_live_global_crossing_gap`
    instantiates it with the three-slot ceiling, alongside a live strategy at
    `0` and a global seam at exactly `1`. The earlier §9 pin scenario remains a
    useful weaker witness: its constant seam fails globally, but another global
    seam happens to pay zero.
  * ⟨UNDONE U-0047⟩ **Minimum colourings.** `SeamColoring`'s greedy colourer synthesises
    *a* proper colouring, never the minimum one; nothing here computes an optimal
    live strategy, only bounds the optimum.

## Relation to the sibling judgements

`LiveStrategy` remains definitionally `SeamColoring.SegmentedIConfluentOn` at a
scenario's worlds, and `liveCost` remains `SeamColoring.jointCost` over its
paths. This module now imports `LiveSegmented` for one genuinely global fact:
`segmented_same_fiber_triple`, whose second merge can leave the live world pool.
`LiveCost`'s abstract-path vocabulary remains independent.
-/
import Uwueave.Bounds
import Uwueave.SeamColoring
import Uwueave.LiveSegmented

namespace Uwueave.ForkGrade

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.SeamAlgebra
open Uwueave.Cost Uwueave.CoordEffect Uwueave.SeamColoring Uwueave.Bounds

universe u v w

/-! ## §1. Scenarios — a finite rooted execution, and the worlds it reaches

A scenario is the smallest object that can carry a *fork*: a root and a finite
list of branch paths. It deliberately carries no `step` — the transition is a
parameter of every operation below, exactly as in `Cost.lean`. -/

/-- **A finite rooted operational scenario.** One root world and a finite list of
branch paths of ops. Everything else — execution edges, worlds, the live clash
graph — is derived from these two fields against a transition, so "the scenario
contains paths to all relevant worlds" is definitional here rather than a
hypothesis anyone can forget. -/
structure Scenario (S : Type u) (Op : Type w) where
  /-- The common ancestor every branch starts from. -/
  root : S
  /-- The branch paths: one op stream per divergent run. -/
  paths : List (List Op)

namespace Scenario

variable {S : Type u} {Op : Type w}

/-- The world an execution edge lands in. An edge is a *state and the op applied
there*; its target is what the transition computes. -/
def edgeTarget (step : S → Op → S) (e : S × Op) : S := step e.1 e.2

/-- The execution edges along one branch path, in order. -/
def edgesAlong (step : S → Op → S) (s : S) : List Op → List (S × Op)
  | [] => []
  | o :: w => (s, o) :: edgesAlong step (step s o) w

/-- The execution edges of a whole list of branch paths, all measured from the
same root — which is what makes the branches *divergent* rather than
sequential. -/
def edgesOfPaths (step : S → Op → S) (s : S) : List (List Op) → List (S × Op)
  | [] => []
  | p :: ps => edgesAlong step s p ++ edgesOfPaths step s ps

/-- Execution edges across branch paths are the standard `flatMap` of the
single-path edge trace.  All branches retain the same root. -/
theorem edgesOfPaths_eq_flatMap (step : S → Op → S) (s : S)
    (ps : List (List Op)) :
    edgesOfPaths step s ps = ps.flatMap (edgesAlong step s) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [edgesOfPaths, List.flatMap_cons, ih]

theorem edgesOfPaths_empty_fixture :
    edgesOfPaths (fun s o : Nat => s + o) 0 [] = [] := rfl

theorem edgesOfPaths_singleton_fixture :
    edgesOfPaths (fun s o : Nat => s + o) 0 [[1, 2]] = [(0, 1), (1, 2)] := rfl

theorem edgesOfPaths_multi_fixture :
    edgesOfPaths (fun s o : Nat => s + o) 0 [[1, 2], [3], []] =
      [(0, 1), (1, 2), (0, 3)] := rfl

/-- **The scenario's execution edges.** Finite, by construction. -/
def execEdges (sc : Scenario S Op) (step : S → Op → S) : List (S × Op) :=
  edgesOfPaths step sc.root sc.paths

/-- **The worlds of the scenario**: the root, and the target of every execution
edge. Finite, by construction, and every one of them is occupied by a run of the
scenario's own ops (`worlds_runsTo`). -/
def worlds (sc : Scenario S Op) (step : S → Op → S) : List S :=
  sc.root :: (sc.execEdges step).map (edgeTarget step)

theorem root_mem_worlds (sc : Scenario S Op) (step : S → Op → S) :
    sc.root ∈ sc.worlds step :=
  List.mem_cons_self

/-- Every branch's endpoint is a world of the scenario. -/
theorem run_mem_trace (step : S → Op → S) :
    ∀ (s : S) (w : List Op),
      Cost.run step s w = s ∨
        Cost.run step s w ∈ (edgesAlong step s w).map (edgeTarget step) := by
  intro s w
  induction w generalizing s with
  | nil => exact Or.inl rfl
  | cons o w ih =>
      show Cost.run step (step s o) w = s ∨
        Cost.run step (step s o) w
          ∈ step s o :: (edgesAlong step (step s o) w).map (edgeTarget step)
      rcases ih (step s o) with hc | hc
      · exact Or.inr (by rw [hc]; exact List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ hc)

/-- A branch's edges are among the scenario's edges. -/
theorem mem_edgesOfPaths (step : S → Op → S) (s : S) :
    ∀ (ps : List (List Op)) (p : List Op), p ∈ ps →
      ∀ e ∈ edgesAlong step s p, e ∈ edgesOfPaths step s ps := by
  intro ps p hp e he
  rw [edgesOfPaths_eq_flatMap]
  exact List.mem_flatMap.mpr ⟨p, hp, he⟩

/-- …and so are a branch's worlds. -/
theorem mem_map_edgesOfPaths (step : S → Op → S) (s : S) :
    ∀ (ps : List (List Op)) (p : List Op), p ∈ ps →
      ∀ x ∈ (edgesAlong step s p).map (edgeTarget step),
        x ∈ (edgesOfPaths step s ps).map (edgeTarget step) := by
  intro ps p hp x hx
  rcases List.mem_map.mp hx with ⟨e, he, hex⟩
  exact List.mem_map.mpr ⟨e, mem_edgesOfPaths step s ps p hp e he, hex⟩

/-- **Every branch endpoint is a world.** -/
theorem run_mem_worlds (sc : Scenario S Op) (step : S → Op → S) :
    ∀ p ∈ sc.paths, Cost.run step sc.root p ∈ sc.worlds step := by
  intro p hp
  rcases run_mem_trace step sc.root p with h | h
  · rw [h]; exact root_mem_worlds sc step
  · exact List.mem_cons_of_mem _ (mem_map_edgesOfPaths step sc.root sc.paths p hp _ h)

/-! ### Realization — the implementation actually walks these edges -/

/-- **The scenario is realized by an implementation.** Every execution edge is a
local commit the implementation really makes, landing where the transition says.

This is `Bounds.Realizes` sharpened from endpoints to edges, and the sharpening
is load-bearing: `Bounds.Realizes` pins only where a stream *ends*, so it cannot
certify the intermediate worlds a scenario's clash graph is drawn on. -/
def Realized (sc : Scenario S Op) (impl : Necessity.Impl S Op)
    (step : S → Op → S) : Prop :=
  ∀ e ∈ sc.execEdges step, impl.tryApply e.2 e.1 = some (step e.1 e.2)

/-- Along one realized branch, every world is the endpoint of a successful local
run from the branch's start. -/
theorem trace_runsTo (impl : Necessity.Impl S Op) (step : S → Op → S) :
    ∀ (s : S) (p : List Op),
      (∀ e ∈ edgesAlong step s p, impl.tryApply e.2 e.1 = some (step e.1 e.2)) →
      ∀ x ∈ (edgesAlong step s p).map (edgeTarget step),
        ∃ ops : List Op, Necessity.RunsTo impl s x ops := by
  intro s p
  induction p generalizing s with
  | nil => intro _ x hx; cases hx
  | cons o w ih =>
      intro hedges x hx
      have hhead : impl.tryApply o s = some (step s o) :=
        hedges (s, o) List.mem_cons_self
      have htail : ∀ e ∈ edgesAlong step (step s o) w,
          impl.tryApply e.2 e.1 = some (step e.1 e.2) :=
        fun e he => hedges e (List.mem_cons_of_mem _ he)
      have hx' : x ∈ step s o :: (edgesAlong step (step s o) w).map (edgeTarget step) := hx
      rcases List.mem_cons.mp hx' with h | h
      · refine ⟨[o], ?_⟩
        show Necessity.run impl s [o] = some x
        rw [Necessity.run_cons_some impl s o [] hhead, h]
        rfl
      · obtain ⟨ops, hops⟩ := ih (step s o) htail x h
        refine ⟨o :: ops, ?_⟩
        show Necessity.run impl s (o :: ops) = some x
        rw [Necessity.run_cons_some impl s o ops hhead]
        exact hops

/-- The same, across all branches. -/
theorem paths_runsTo (impl : Necessity.Impl S Op) (step : S → Op → S) (s : S) :
    ∀ ps : List (List Op),
      (∀ e ∈ edgesOfPaths step s ps, impl.tryApply e.2 e.1 = some (step e.1 e.2)) →
      ∀ x ∈ (edgesOfPaths step s ps).map (edgeTarget step),
        ∃ ops : List Op, Necessity.RunsTo impl s x ops := by
  intro ps
  induction ps with
  | nil => intro _ x hx; cases hx
  | cons q ps ih =>
      intro hedges x hx
      have hsplit : x ∈ (edgesAlong step s q).map (edgeTarget step)
          ++ (edgesOfPaths step s ps).map (edgeTarget step) := by
        rw [← List.map_append]; exact hx
      have hleft : ∀ e ∈ edgesAlong step s q,
          impl.tryApply e.2 e.1 = some (step e.1 e.2) :=
        fun e he => hedges e (List.mem_append.mpr (Or.inl he))
      have hright : ∀ e ∈ edgesOfPaths step s ps,
          impl.tryApply e.2 e.1 = some (step e.1 e.2) :=
        fun e he => hedges e (List.mem_append.mpr (Or.inr he))
      rcases List.mem_append.mp hsplit with h | h
      · exact trace_runsTo impl step s q hleft x h
      · exact ih hright x h

/-- **Every world of a realized scenario is co-reachable from the root.** This is
what licenses reading any pair of worlds as a partition pair: each is the
endpoint of a successful local run from the common ancestor, which is exactly the
shape `Necessity.MergeSafe` quantifies over. -/
theorem worlds_runsTo {sc : Scenario S Op} {impl : Necessity.Impl S Op}
    {step : S → Op → S} (h : sc.Realized impl step) :
    ∀ x ∈ sc.worlds step, ∃ ops : List Op, Necessity.RunsTo impl sc.root x ops := by
  intro x hx
  rcases List.mem_cons.mp hx with hroot | hedge
  · exact ⟨[], by rw [hroot]; rfl⟩
  · exact paths_runsTo impl step sc.root sc.paths h x hedge

end Scenario

/-! ## §2. The live clash graph

`SeamColoring.Clashes` drawn on the scenario's worlds, and nowhere else. This is
the fork-aware refinement: a clash between two *branches* is visible here, while
`Cost.ClashBlocks` can only see a state against its own successor. -/

/-- **A live clash**: two co-reachable worlds of the scenario whose merge is
illegal. `Bounds.zero_floor_does_not_imply_cfcs`'s pin fork is one
(`pinFork_liveClash`); no clash decomposition of any pin stream is. -/
def LiveClash {S : Type u} {Op : Type w} [MergeState S] (I : Invariant S)
    (step : S → Op → S) (sc : Scenario S Op) : Prop :=
  ∃ x ∈ sc.worlds step, ∃ y ∈ sc.worlds step, Clashes I x y

instance instDecidableLiveClash {S : Type u} {Op : Type w} [MergeState S]
    (I : Invariant S) [DecidablePred I] (step : S → Op → S) (sc : Scenario S Op) :
    Decidable (LiveClash I step sc) := by
  unfold LiveClash; infer_instance

/-- **An I-confluent invariant has no live clash, in any scenario.** Its clash
graph is edgeless outright (`SeamColoring.iconfluent_iff_no_clash_edge`), so no
restriction of it has an edge. -/
theorem no_live_clash_of_iconfluent {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op} (h : IConfluent I) :
    ¬ LiveClash I step sc :=
  fun ⟨_, _, _, _, hc⟩ => hc.2.2 (h _ _ hc.1 hc.2.1)

/-- A live clash is a `Necessity.ReachableClash` for any implementation that
realizes the scenario from a legal root — the bridge §7 runs on. -/
theorem reachableClash_of_liveClash {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op}
    {impl : Necessity.Impl S Op} (hreal : sc.Realized impl step) (hroot : I sc.root)
    (h : LiveClash I step sc) : Nonempty (Necessity.ReachableClash impl I) := by
  obtain ⟨x, hx, y, hy, hc⟩ := h
  obtain ⟨opsx, hopsx⟩ := Scenario.worlds_runsTo hreal x hx
  obtain ⟨opsy, hopsy⟩ := Scenario.worlds_runsTo hreal y hy
  exact ⟨{ base := sc.root, x := x, y := y, opsx := opsx, opsy := opsy
           hbase := hroot, hx_run := hopsx, hy_run := hopsy
           hx := hc.1, hy := hc.2.1, hbad := hc.2.2 }⟩

/-! ## §3. Live strategies — codex's colouring, taken protocol-relative

A strategy is a proper colouring of the **live** clash graph plus fiber stability
**over the scenario's worlds**. Both halves are `SeamColoring`'s, at the pool
`sc.worlds step`; §3's identification theorem says the bundle is exactly
`SegmentedIConfluentOn` there, so nothing new is being asked of a seam — only
less, and precisely how much less is named. -/

/-- **A live strategy.** A seam that properly colours the scenario's live clash
graph and whose fibers are closed under legal merges of the scenario's worlds.

⚠ Deliberately **not** a global `SegmentedIConfluent` seam: §9 proves that
requiring the global judgement breaks the reverse half of §5, because a clash
elsewhere in the lattice rejects the constant seam over a clash-free scenario. -/
structure LiveStrategy {S : Type u} {Op : Type w} [MergeState S] (I : Invariant S)
    (step : S → Op → S) (sc : Scenario S Op) (Seg : Type v) where
  /-- The seam this strategy coordinates at. -/
  seam : S → Seg
  /-- No live clash edge is monochromatic — codex's colouring condition. -/
  proper : ProperColoring (sc.worlds step) seam I
  /-- Fibers of the scenario's worlds are closed under legal merges. -/
  stable : SeamStableOnPool (sc.worlds step) I seam

/-- **A live strategy IS segmented I-confluence over the scenario's worlds.**
`SeamColoring.segmentedOn_iff_properColoring` at the pool, so the bundle above
introduces no new judgement. -/
theorem LiveStrategy.segmentedOn {S : Type u} {Op : Type w} {Seg : Type v}
    [MergeState S] {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op}
    (τ : LiveStrategy I step sc Seg) :
    SegmentedIConfluentOn (sc.worlds step) τ.seam I :=
  segmentedOn_iff_properColoring.mpr ⟨τ.proper, τ.stable⟩

/-- …and conversely. -/
def LiveStrategy.ofSegmentedOn {S : Type u} {Op : Type w} {Seg : Type v}
    [MergeState S] {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op}
    {σ : S → Seg} (h : SegmentedIConfluentOn (sc.worlds step) σ I) :
    LiveStrategy I step sc Seg where
  seam := σ
  proper := (segmentedOn_iff_properColoring.mp h).1
  stable := (segmentedOn_iff_properColoring.mp h).2

/-- **Every global seam is a live strategy** — restriction to the scenario's pool
is free (`SeamColoring.segmentedOn_of_segmented`). The converse fails, and §9 is
the witness. -/
def LiveStrategy.ofSegmented {S : Type u} {Op : Type w} {Seg : Type v}
    [MergeState S] {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op}
    {σ : S → Seg} (h : SegmentedIConfluent σ I) : LiveStrategy I step sc Seg where
  seam := σ
  proper := properColoring_of_segmented h _
  stable := seamStableOnPool_of_seamStableOn (seamStableOn_of_segmented h)

/-! ## §4. The edge-charged cost

Cost is charged to execution edges whose endpoints sit in different segments.
`liveCost` is defined as `SeamColoring.jointCost` over the branch paths — so
every theorem of `Cost.lean` applies to it unchanged — and
`liveCost_eq_edge_charges` discharges the "charged to edges" description against
that definition rather than leaving it as prose. -/

/-- **The fork-aware quantity.** The coordination cost of a whole scenario under
one seam: the seam changes along every branch, summed. Definitionally
`SeamColoring.jointCost` over the branch paths. -/
def liveCost {S : Type u} {Op : Type w} {Seg : Type v} [DecidableEq Seg]
    (σ : S → Seg) (step : S → Op → S) (sc : Scenario S Op) : Nat :=
  jointCost σ step sc.root sc.paths

theorem jointCost_nil {S : Type u} {Op : Type w} {Seg : Type v} [DecidableEq Seg]
    (σ : S → Seg) (step : S → Op → S) (s : S) :
    jointCost σ step s ([] : List (List Op)) = 0 := rfl

theorem jointCost_cons {S : Type u} {Op : Type w} {Seg : Type v} [DecidableEq Seg]
    (σ : S → Seg) (step : S → Op → S) (s : S) (p : List Op) (ps : List (List Op)) :
    jointCost σ step s (p :: ps) = crossings σ step s p + jointCost σ step s ps := by
  simp [jointCost]

/-- The edge charge, as a count over the execution-edge multiset. -/
def edgeCharges {S : Type u} {Op : Type w} {Seg : Type v} [DecidableEq Seg]
    (σ : S → Seg) (step : S → Op → S) (sc : Scenario S Op) : Nat :=
  (sc.execEdges step).countP (fun e => !decide (σ (step e.1 e.2) = σ e.1))

private theorem countP_edgesAlong {S : Type u} {Op : Type w} {Seg : Type v}
    [DecidableEq Seg] (σ : S → Seg) (step : S → Op → S) :
    ∀ (s : S) (w : List Op),
      (Scenario.edgesAlong step s w).countP
          (fun e => !decide (σ (step e.1 e.2) = σ e.1))
        = crossings σ step s w := by
  intro s w
  induction w generalizing s with
  | nil => rfl
  | cons o w ih =>
      show ((s, o) :: Scenario.edgesAlong step (step s o) w).countP _
        = (if σ (step s o) = σ s then 0 else 1) + crossings σ step (step s o) w
      rw [List.countP_cons, ih (step s o)]
      by_cases hc : σ (step s o) = σ s
      · rw [if_pos hc]; simp [hc]
      · rw [if_neg hc]; simp [hc]; omega

private theorem countP_edgesOfPaths {S : Type u} {Op : Type w} {Seg : Type v}
    [DecidableEq Seg] (σ : S → Seg) (step : S → Op → S) (s : S) :
    ∀ ps : List (List Op),
      (Scenario.edgesOfPaths step s ps).countP
          (fun e => !decide (σ (step e.1 e.2) = σ e.1))
        = jointCost σ step s ps := by
  intro ps
  rw [Scenario.edgesOfPaths_eq_flatMap, List.countP_flatMap]
  congr 1
  apply List.map_congr_left
  intro p _
  exact countP_edgesAlong σ step s p

/-- **The cost really is charged to execution edges.** `liveCost` counts exactly
the execution edges whose two endpoints land in different segments — the
description the definition was chosen for, proved against it.

⟨scope⟩ the count is over the edge *multiset*, so an edge two branches both
traverse is charged twice. No statement below is affected: all of them concern
the cost being zero or positive. -/
theorem liveCost_eq_edge_charges {S : Type u} {Op : Type w} {Seg : Type v}
    [DecidableEq Seg] (σ : S → Seg) (step : S → Op → S) (sc : Scenario S Op) :
    liveCost σ step sc = edgeCharges σ step sc :=
  (countP_edgesOfPaths σ step sc.root sc.paths).symm

/-- The cost profile of a scenario over its live strategies — `CoordEffect`'s
`Profile`, so composition and `optimum` are the existing ones. -/
def liveProfile {S : Type u} {Op : Type w} {Seg : Type v} [MergeState S]
    [DecidableEq Seg] (I : Invariant S) (step : S → Op → S) (sc : Scenario S Op) :
    Profile (LiveStrategy I step sc Seg) :=
  fun τ => liveCost τ.seam step sc

@[simp] theorem liveProfile_apply {S : Type u} {Op : Type w} {Seg : Type v}
    [MergeState S] [DecidableEq Seg] {I : Invariant S} {step : S → Op → S}
    {sc : Scenario S Op} (τ : LiveStrategy I step sc Seg) :
    liveProfile I step sc τ = liveCost τ.seam step sc := rfl

/-- **The live optimum**: the minimum cost over a finite nonempty space of live
strategies. `CoordEffect.optimum`, so `optimum_achieved` applies — the number is
one a single admissible strategy actually pays. -/
def liveOptimum {S : Type u} {Op : Type w} {Seg : Type v} [MergeState S]
    [DecidableEq Seg] {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op}
    (A : Admissible (LiveStrategy I step sc Seg)) : Nat :=
  optimum A (liveProfile I step sc)

/-! ## §5. THE ZERO CHARACTERISATION

The theorem the file exists for: for a rooted scenario — whose worlds are, by
construction, exactly what its own paths reach — the minimum over live strategies
of the edge-charged cost is zero **iff** there is no live clash. -/

private theorem crossings_zero_colors_trace {S : Type u} {Op : Type w} {Seg : Type v}
    [DecidableEq Seg] (σ : S → Seg) (step : S → Op → S) :
    ∀ (s : S) (w : List Op), crossings σ step s w = 0 →
      ∀ x ∈ (Scenario.edgesAlong step s w).map (Scenario.edgeTarget step),
        σ x = σ s := by
  intro s w
  induction w generalizing s with
  | nil => intro _ x hx; cases hx
  | cons o w ih =>
      intro h x hx
      have h' : (if σ (step s o) = σ s then 0 else 1)
          + crossings σ step (step s o) w = 0 := h
      by_cases hc : σ (step s o) = σ s
      · rw [if_pos hc] at h'
        have hrest : crossings σ step (step s o) w = 0 := by omega
        have hx' : x ∈ step s o
            :: (Scenario.edgesAlong step (step s o) w).map (Scenario.edgeTarget step) := hx
        rcases List.mem_cons.mp hx' with he | he
        · rw [he]; exact hc
        · exact (ih (step s o) hrest x he).trans hc
      · rw [if_neg hc] at h'
        exact absurd h' (by omega)

private theorem jointCost_zero_colors {S : Type u} {Op : Type w} {Seg : Type v}
    [DecidableEq Seg] (σ : S → Seg) (step : S → Op → S) (s : S) :
    ∀ ps : List (List Op), jointCost σ step s ps = 0 →
      ∀ x ∈ (Scenario.edgesOfPaths step s ps).map (Scenario.edgeTarget step),
        σ x = σ s := by
  intro ps
  induction ps with
  | nil => intro _ x hx; cases hx
  | cons p ps ih =>
      intro h x hx
      rw [jointCost_cons] at h
      have h1 : crossings σ step s p = 0 := by omega
      have h2 : jointCost σ step s ps = 0 := by omega
      have hx' : x ∈ (Scenario.edgesAlong step s p).map (Scenario.edgeTarget step)
          ++ (Scenario.edgesOfPaths step s ps).map (Scenario.edgeTarget step) := by
        rw [← List.map_append]; exact hx
      rcases List.mem_append.mp hx' with he | he
      · exact crossings_zero_colors_trace σ step s p h1 x he
      · exact ih h2 x he

/-- **A free strategy paints the whole scenario the root's colour.** Zero cost
means no execution edge changes segment, so every world is in the root's fiber —
codex's "everything connected to the root is root-coloured". -/
theorem worlds_root_colored {S : Type u} {Op : Type w} {Seg : Type v} [MergeState S]
    [DecidableEq Seg] {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op}
    (τ : LiveStrategy I step sc Seg) (h0 : liveCost τ.seam step sc = 0) :
    ∀ x ∈ sc.worlds step, τ.seam x = τ.seam sc.root := by
  intro x hx
  rcases List.mem_cons.mp hx with hroot | hedge
  · rw [hroot]
  · exact jointCost_zero_colors τ.seam step sc.root sc.paths h0 x hedge

/-- **A global three-way obstruction forces a scenario crossing.** Suppose three
legal worlds occur in one scenario but their triple join is illegal. If a global
segmented seam paid zero, `worlds_root_colored` would put all three in the root's
fiber. Global fiber stability would then close the first pair and, crucially,
close that intermediate join with the third world, proving the forbidden triple
legal (`LiveSegmented.segmented_same_fiber_triple`). Therefore every global seam
pays at least one crossing on the scenario.

No pairwise clash hypothesis is used. The result is designed for precisely the
case where the live clash graph is empty but global closure sees one merge level
farther than the scenario's world pool. -/
theorem global_triple_obstruction_cost_positive
    {S : Type u} {Op : Type w} {Seg : Type v} [MergeState S] [DecidableEq Seg]
    {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op}
    {σ : S → Seg} {x y z : S}
    (hxw : x ∈ sc.worlds step) (hyw : y ∈ sc.worlds step)
    (hzw : z ∈ sc.worlds step) (hx : I x) (hy : I y) (hz : I z)
    (hbad : ¬ I ((x ⊔ y) ⊔ z)) (hseg : SegmentedIConfluent σ I) :
    1 ≤ liveCost σ step sc := by
  apply Nat.pos_of_ne_zero
  intro h0
  let τ : LiveStrategy I step sc Seg := LiveStrategy.ofSegmented hseg
  change liveCost τ.seam step sc = 0 at h0
  have hxr := worlds_root_colored τ h0 x hxw
  have hyr := worlds_root_colored τ h0 y hyw
  have hzr := worlds_root_colored τ h0 z hzw
  have hxy : σ x = σ y := hxr.trans hyr.symm
  have hxz : σ x = σ z := hxr.trans hzr.symm
  exact hbad
    (LiveSegmented.segmented_same_fiber_triple hseg hxy hxz hx hy hz).1

/-- **Forward.** A live strategy that pays nothing refutes every live clash: two
clashing worlds would both carry the root's colour, and properness forbids a
monochromatic edge. -/
theorem no_live_clash_of_free {S : Type u} {Op : Type w} {Seg : Type v} [MergeState S]
    [DecidableEq Seg] {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op}
    (τ : LiveStrategy I step sc Seg) (h0 : liveCost τ.seam step sc = 0) :
    ¬ LiveClash I step sc := by
  intro ⟨x, hx, y, hy, hc⟩
  exact τ.proper x hx y hy hc
    ((worlds_root_colored τ h0 x hx).trans (worlds_root_colored τ h0 y hy).symm)

private theorem crossings_const {S : Type u} {Op : Type w} {Seg : Type v}
    [DecidableEq Seg] (c₀ : Seg) (step : S → Op → S) :
    ∀ (s : S) (w : List Op), crossings (fun _ : S => c₀) step s w = 0 := by
  intro s w
  induction w generalizing s with
  | nil => rfl
  | cons o w ih =>
      show (if c₀ = c₀ then 0 else 1) + crossings (fun _ : S => c₀) step (step s o) w = 0
      rw [if_pos rfl, ih (step s o)]

private theorem jointCost_const {S : Type u} {Op : Type w} {Seg : Type v}
    [DecidableEq Seg] (c₀ : Seg) (step : S → Op → S) (s : S) :
    ∀ ps : List (List Op), jointCost (fun _ : S => c₀) step s ps = 0 := by
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [jointCost_cons, crossings_const c₀ step s p, ih]

/-- **The constant one-colour seam, as a live strategy.** Available exactly when
the scenario has no live clash: properness holds because there is no edge to be
monochromatic, stability because a constant seam cannot move. This is the seam
codex's reverse direction is built on — and §9 shows it is *not* available if
strategies are required to be globally valid. -/
def constLiveStrategy {S : Type u} {Op : Type w} {Seg : Type v} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op} (c₀ : Seg)
    (h : ¬ LiveClash I step sc) : LiveStrategy I step sc Seg where
  seam := fun _ => c₀
  proper := fun x hx y hy hc _ => h ⟨x, hx, y, hy, hc⟩
  stable := fun _ _ _ _ _ _ _ => rfl

/-- The constant strategy pays nothing, on every scenario. -/
theorem constLiveStrategy_free {S : Type u} {Op : Type w} {Seg : Type v} [MergeState S]
    [DecidableEq Seg] {I : Invariant S} {step : S → Op → S} {sc : Scenario S Op}
    (c₀ : Seg) (h : ¬ LiveClash I step sc) :
    liveCost (constLiveStrategy (I := I) (step := step) (sc := sc) c₀ h).seam step sc = 0 :=
  jointCost_const c₀ step sc.root sc.paths

/-- **THE ZERO CHARACTERISATION, space-free.** Some live strategy pays nothing —
equivalently, the minimum over live strategies is `0`, since costs are `Nat` —
**iff** the scenario contains no live clash.

Hypotheses, exactly: a segment type with decidable equality (inherited from
`Cost.crossings`) and one segment value `c₀` to build the constant seam from. No
reachability side condition, because a scenario's worlds are *defined* as what
its paths reach; no global seam validity, because strategies are
protocol-relative (§9 proves that is necessary, not a convenience). -/
theorem liveFree_iff_no_live_clash {S : Type u} {Op : Type w} {Seg : Type v}
    [MergeState S] [DecidableEq Seg] {I : Invariant S} {step : S → Op → S}
    {sc : Scenario S Op} (c₀ : Seg) :
    (∃ τ : LiveStrategy I step sc Seg, liveCost τ.seam step sc = 0)
      ↔ ¬ LiveClash I step sc := by
  constructor
  · intro ⟨τ, h0⟩
    exact no_live_clash_of_free τ h0
  · intro h
    exact ⟨constLiveStrategy c₀ h, constLiveStrategy_free c₀ h⟩

/-- **`liveScenario_optimum_eq_zero_iff_no_live_clash` — the named theorem.** For
a rooted scenario, the optimum over a space of live strategies is `0` **iff** the
scenario contains no live clash.

Hypotheses, exactly:

  * `[DecidableEq Seg]` — inherited from `Cost.crossings`;
  * `c₀ : Seg` — one segment value, the constant seam's colour;
  * `A` — a finite nonempty space of live strategies (`CoordEffect.Admissible`),
    which is what makes "the minimum" a number attained at a member
    (`optimum_achieved`) rather than an infimum with no witness;
  * `hconst` — the space contains the constant strategy *whenever that is a live
    strategy at all*. This is what the reverse direction needs and nothing more:
    the forward direction holds over every space.

Forward: the optimum is attained at some member, which then pays nothing, so
every world carries the root's colour and a clash edge would be monochromatic.
Reverse: with no live clash the constant seam is admissible and free, and the
optimum is below every member's cost. -/
theorem liveScenario_optimum_eq_zero_iff_no_live_clash {S : Type u} {Op : Type w}
    {Seg : Type v} [MergeState S] [DecidableEq Seg] {I : Invariant S}
    {step : S → Op → S} {sc : Scenario S Op} (c₀ : Seg)
    (A : Admissible (LiveStrategy I step sc Seg))
    (hconst : ∀ h : ¬ LiveClash I step sc, constLiveStrategy c₀ h ∈ A.toList) :
    liveOptimum A = 0 ↔ ¬ LiveClash I step sc := by
  constructor
  · intro h0
    obtain ⟨τ, _, hτ⟩ := optimum_achieved A (liveProfile I step sc)
    have hz : liveProfile I step sc τ = 0 := by rw [← hτ]; exact h0
    exact no_live_clash_of_free τ hz
  · intro h
    have hle : liveOptimum A ≤ liveProfile I step sc (constLiveStrategy c₀ h) :=
      optimum_le_of_mem (hconst h)
    have hz : liveProfile I step sc (constLiveStrategy c₀ h) = 0 :=
      constLiveStrategy_free c₀ h
    omega

/-- **The contrapositive, in the shape a floor is quoted in.** A live clash puts
the optimum at ≥ 1 over **every** space of live strategies, at every segment type
in every universe — the fork-aware analogue of
`CoordEffect.pin_composed_floor_universal`, now with a *matching* zero. -/
theorem one_le_liveOptimum_of_liveClash {S : Type u} {Op : Type w} {Seg : Type v}
    [MergeState S] [DecidableEq Seg] {I : Invariant S} {step : S → Op → S}
    {sc : Scenario S Op} (h : LiveClash I step sc)
    (A : Admissible (LiveStrategy I step sc Seg)) : 1 ≤ liveOptimum A :=
  le_optimum (fun τ _ => Nat.pos_of_ne_zero (fun h0 => no_live_clash_of_free τ h0 h))

/-- **`Bounds.fork_clash_charges_the_pair` re-derived from the live quantity** —
the k=2 seed, recovered as the two-branch instance. The original needs a *global*
`SegmentedIConfluent` seam; this derivation needs only the colouring over the two
branch endpoints, so the live quantity subsumes it strictly. -/
theorem fork_clash_charges_the_pair_via_scenario {S : Type u} {Op : Type w}
    {Seg : Type v} [MergeState S] [DecidableEq Seg] {I : Invariant S}
    {step : S → Op → S} {σ : S → Seg} {base : S} {opsx opsy : List Op}
    (hseg : SegmentedIConfluent σ I)
    (hx : I (Cost.run step base opsx)) (hy : I (Cost.run step base opsy))
    (hbad : ¬ I (Cost.run step base opsx ⊔ Cost.run step base opsy)) :
    0 < crossings σ step base opsx + crossings σ step base opsy := by
  let sc : Scenario S Op := ⟨base, [opsx, opsy]⟩
  let τ : LiveStrategy I step sc Seg := LiveStrategy.ofSegmented hseg
  have hclash : LiveClash I step sc :=
    ⟨Cost.run step base opsx, sc.run_mem_worlds step opsx List.mem_cons_self,
     Cost.run step base opsy,
     sc.run_mem_worlds step opsy (List.mem_cons_of_mem _ List.mem_cons_self),
     ⟨hx, hy, hbad⟩⟩
  have hpos : liveCost τ.seam step sc ≠ 0 := fun h0 => no_live_clash_of_free τ h0 hclash
  have hval : liveCost τ.seam step sc
      = crossings σ step base opsx + (crossings σ step base opsy + 0) := by
    show jointCost σ step base [opsx, opsy] = _
    rw [jointCost_cons, jointCost_cons, jointCost_nil]
  omega

/-! ## §6. The theorem `Necessity` was missing

`Necessity.lean` proves `reachable_clash_refutes_cfcs` and
`iconfluent_implies_cfcs`, but never states what CFCS *is* in terms of its own
two witnesses. It is exactly local safety plus the absence of a reachable clash —
and the reverse direction is the useful half, because it turns "no witness of
this shape exists" into a positive CFCS verdict.

Stated here, about `Necessity`'s definitions; that file is not edited. -/

/-- **`cfcs_iff_locallySafe_and_no_reachableClash`.** An implementation is CFCS
for `I` **iff** every successful local commit preserves `I` and no reachable
clash exists.

Forward: local safety is the first conjunct of `IsCFCS`, and
`Necessity.reachable_clash_refutes_cfcs` rules the second out. Reverse: local
safety puts the endpoints of any two successful runs from an `I`-base in `I`
(`Necessity.RunsTo.preserves`), so an illegal merge would *construct* a
`Necessity.ReachableClash` — the constructor's other fields are exactly the data
in hand. ⚠ Classical: turning "no clash" into "the merge is legal" is excluded
middle on `I (x ⊔ y)`, on the same footing as
`Confluence.escalation_witness` and `SeamColoring.separatesOn_of_properColoring`. -/
theorem cfcs_iff_locallySafe_and_no_reachableClash {S : Type u} {Op : Type w}
    [MergeState S] (impl : Necessity.Impl S Op) (I : Invariant S) :
    Necessity.IsCFCS impl I
      ↔ Necessity.LocallySafe impl I ∧ ¬ Nonempty (Necessity.ReachableClash impl I) := by
  constructor
  · intro h
    exact ⟨h.1, fun ⟨c⟩ => Necessity.reachable_clash_refutes_cfcs c h⟩
  · intro ⟨hloc, hno⟩
    refine ⟨hloc, ?_⟩
    intro base x y opsx opsy hb hx hy
    refine Classical.byContradiction fun hbad => hno ⟨?_⟩
    exact { base := base, x := x, y := y, opsx := opsx, opsy := opsy
            hbase := hb, hx_run := hx, hy_run := hy
            hx := hx.preserves hloc hb, hy := hy.preserves hloc hb, hbad := hbad }

/-! ## §7. THE COMPOSITION — the modal judgement as a live optimum

`Bounds` §4 proved the per-stream floor's zero is not the modal zero. This is the
statement that the fork-aware quantity's zero **is**. -/

/-- The total transition an implementation induces: where it commits, that state;
where it aborts, stay put. This is `Bounds.totalImpl` read backwards — it turns a
*partial* implementation into a `Cost`-shaped `step` without assuming anything
about it, so a reachable clash can be replayed as a scenario with no `Realizes`
hypothesis to discharge. -/
def stepOf {S : Type u} {Op : Type w} (impl : Necessity.Impl S Op) : S → Op → S :=
  fun s o => (impl.tryApply o s).getD s

/-- A successful run lands where `stepOf` says. -/
theorem run_stepOf_eq {S : Type u} {Op : Type w} {impl : Necessity.Impl S Op}
    {s x : S} {ops : List Op} (h : Necessity.RunsTo impl s x ops) :
    Cost.run (stepOf impl) s ops = x := by
  induction ops generalizing s with
  | nil => exact Option.some.inj h
  | cons o w ih =>
      have hrun : Necessity.run impl s (o :: w) = some x := h
      match htry : impl.tryApply o s with
      | none =>
          rw [Necessity.run_cons_none impl s o w htry] at hrun
          exact absurd hrun (by simp)
      | some s' =>
          have hstep : stepOf impl s o = s' := by simp [stepOf, htry]
          have h' : Necessity.RunsTo impl s' x w := by
            rw [Necessity.run_cons_some impl s o w htry] at hrun
            exact hrun
          show Cost.run (stepOf impl) (stepOf impl s o) w = x
          rw [hstep]; exact ih h'

/-- Every edge a successful run walks is a commit `stepOf` reproduces. -/
theorem realized_edgesAlong_of_runsTo {S : Type u} {Op : Type w}
    {impl : Necessity.Impl S Op} {s x : S} {ops : List Op}
    (h : Necessity.RunsTo impl s x ops) :
    ∀ e ∈ Scenario.edgesAlong (stepOf impl) s ops,
      impl.tryApply e.2 e.1 = some (stepOf impl e.1 e.2) := by
  induction ops generalizing s with
  | nil => intro e he; cases he
  | cons o w ih =>
      intro e he
      have hrun : Necessity.run impl s (o :: w) = some x := h
      match htry : impl.tryApply o s with
      | none =>
          rw [Necessity.run_cons_none impl s o w htry] at hrun
          exact absurd hrun (by simp)
      | some s' =>
          have hstep : stepOf impl s o = s' := by simp [stepOf, htry]
          have h' : Necessity.RunsTo impl s' x w := by
            rw [Necessity.run_cons_some impl s o w htry] at hrun
            exact hrun
          have he' : e ∈ (s, o) :: Scenario.edgesAlong (stepOf impl) (stepOf impl s o) w := he
          rcases List.mem_cons.mp he' with hh | ht
          · rw [hh]; show impl.tryApply o s = some (stepOf impl s o)
            rw [hstep]; exact htry
          · rw [hstep] at ht; exact ih h' e ht

/-- **A reachable clash is a two-branch scenario.** The canonical replay: root at
the clash's base, one branch per run, over the transition the implementation
itself induces. No `Realizes` hypothesis is needed — `stepOf` is built from
`impl`. -/
def scenarioOfClash {S : Type u} {Op : Type w} [MergeState S] {I : Invariant S}
    {impl : Necessity.Impl S Op} (c : Necessity.ReachableClash impl I) :
    Scenario S Op :=
  ⟨c.base, [c.opsx, c.opsy]⟩

theorem scenarioOfClash_realized {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {impl : Necessity.Impl S Op}
    (c : Necessity.ReachableClash impl I) :
    (scenarioOfClash c).Realized impl (stepOf impl) := by
  intro e he
  have he' : e ∈ Scenario.edgesAlong (stepOf impl) c.base c.opsx
      ++ (Scenario.edgesAlong (stepOf impl) c.base c.opsy ++ []) := he
  rcases List.mem_append.mp he' with h | h
  · exact realized_edgesAlong_of_runsTo c.hx_run e h
  · rcases List.mem_append.mp h with h' | h'
    · exact realized_edgesAlong_of_runsTo c.hy_run e h'
    · cases h'

theorem scenarioOfClash_liveClash {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {impl : Necessity.Impl S Op}
    (c : Necessity.ReachableClash impl I) :
    LiveClash I (stepOf impl) (scenarioOfClash c) := by
  refine ⟨c.x, ?_, c.y, ?_, ⟨c.hx, c.hy, c.hbad⟩⟩
  · have h := (scenarioOfClash c).run_mem_worlds (stepOf impl) c.opsx List.mem_cons_self
    have he : Cost.run (stepOf impl) (scenarioOfClash c).root c.opsx = c.x :=
      run_stepOf_eq c.hx_run
    rw [he] at h; exact h
  · have h := (scenarioOfClash c).run_mem_worlds (stepOf impl) c.opsy
      (List.mem_cons_of_mem _ List.mem_cons_self)
    have he : Cost.run (stepOf impl) (scenarioOfClash c).root c.opsy = c.y :=
      run_stepOf_eq c.hy_run
    rw [he] at h; exact h

/-- **THE COMPOSITION — the honest quantitative degeneration of the modal
judgement.** An implementation is coordination-free convergent safe for `I`
**iff** it is locally safe and **every finite scenario it realizes from a legal
root has live optimum zero**.

This is what `Bounds.zero_floor_does_not_imply_cfcs` proved the per-stream floor
cannot do. The mechanism it named is the mechanism repaired: `Cost.ClashBlocks`
is a sequential clash and cannot see a fork, while a `Scenario`'s worlds are
pairwise co-reachable by construction, so a fork *is* an edge of its live clash
graph.

The right-hand side is stated as "some live strategy pays nothing", which by
`liveScenario_optimum_eq_zero_iff_no_live_clash` is the optimum being zero;
`c₀ : Seg` is the constant seam's colour and `[DecidableEq Seg]` is inherited
from `Cost.crossings`. Neither direction needs a global seam.

Forward: a live clash in a realized scenario from a legal root *is* a reachable
clash (`reachableClash_of_liveClash`), which merge safety forbids. Reverse: a
reachable clash replays as a two-branch scenario over `stepOf impl`
(`scenarioOfClash`), whose live clash the hypothesis denies; §6 then converts
"no reachable clash" into CFCS. -/
theorem cfcs_iff_locallySafe_and_all_finite_scenarios_zero {S : Type u} {Op : Type w}
    {Seg : Type v} [MergeState S] [DecidableEq Seg] (impl : Necessity.Impl S Op)
    (I : Invariant S) (c₀ : Seg) :
    Necessity.IsCFCS impl I
      ↔ Necessity.LocallySafe impl I
          ∧ ∀ (step : S → Op → S) (sc : Scenario S Op),
              I sc.root → sc.Realized impl step →
                ∃ τ : LiveStrategy I step sc Seg, liveCost τ.seam step sc = 0 := by
  constructor
  · intro hcfcs
    refine ⟨hcfcs.1, fun step sc hroot hreal => (liveFree_iff_no_live_clash c₀).mpr ?_⟩
    intro hclash
    obtain ⟨c⟩ := reachableClash_of_liveClash hreal hroot hclash
    exact Necessity.reachable_clash_refutes_cfcs c hcfcs
  · intro ⟨hloc, hall⟩
    refine (cfcs_iff_locallySafe_and_no_reachableClash impl I).mpr ⟨hloc, ?_⟩
    intro ⟨c⟩
    obtain ⟨τ, h0⟩ := hall (stepOf impl) (scenarioOfClash c) c.hbase
      (scenarioOfClash_realized c)
    exact no_live_clash_of_free τ h0 (scenarioOfClash_liveClash c)

/-! ## §8. Non-vacuity — the pin fork is positive, the grow-only fork is zero

The two instances the repair must separate, on **the same carrier and the same
transition**. `Bounds.zero_floor_does_not_imply_cfcs`'s pin fork must cost;
a grow-only invariant over the same lattice must not. -/

/-- **The pin fork as a scenario** — `Bounds.pinClash`'s two runs, rooted at the
empty pin set. This is precisely the workload whose per-stream floor is zero
under `Cost.clashBlocks_nil_of_inflationary`. -/
def pinForkScenario : Scenario PinSet Bool := ⟨emptyPin, [[true], [false]]⟩

theorem pinForkScenario_worlds :
    pinForkScenario.worlds pinStep
      = [emptyPin, pinStep emptyPin true, pinStep emptyPin false] := rfl

/-- **The pin fork has a live clash** — the edge the per-stream measure cannot
see. Both branch endpoints are legal and their merge pins two nodes. -/
theorem pinFork_liveClash : LiveClash pinInv pinStep pinForkScenario :=
  ⟨pinStep emptyPin true, List.mem_cons_of_mem _ List.mem_cons_self,
   pinStep emptyPin false,
   List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
   ⟨pinInv_pinOne true, pinInv_pinOne false, pin_join_bad⟩⟩

/-- **⚠ NON-VACUITY, THE POSITIVE HALF.** Every live strategy for the pin fork
pays at least one, at every segment type in every universe. The workload whose
`Cost` floor is identically zero has a fork-aware optimum of at least one — the
disagreement `Bounds` §4 found, resolved in the direction the modal verdict
demands. -/
theorem pinFork_cost_positive {Seg : Type v} [DecidableEq Seg]
    (τ : LiveStrategy pinInv pinStep pinForkScenario Seg) :
    1 ≤ liveCost τ.seam pinStep pinForkScenario :=
  Nat.pos_of_ne_zero (fun h0 => no_live_clash_of_free τ h0 pinFork_liveClash)

/-- The same as a floor on the optimum, over every space. -/
theorem pinFork_liveOptimum_positive {Seg : Type v} [DecidableEq Seg]
    (A : Admissible (LiveStrategy pinInv pinStep pinForkScenario Seg)) :
    1 ≤ liveOptimum A :=
  one_le_liveOptimum_of_liveClash pinFork_liveClash A

/-- The seam "is `true` pinned?", as a live strategy for the pin fork — valid
globally (`Cost.seamTrue_segmented`), hence live. -/
def pinLiveTrue : LiveStrategy pinInv pinStep pinForkScenario Bool :=
  LiveStrategy.ofSegmented seamTrue_segmented

/-- The mirror seam, likewise. -/
def pinLiveFalse : LiveStrategy pinInv pinStep pinForkScenario Bool :=
  LiveStrategy.ofSegmented seamFalse_segmented

/-- The two-strategy space `CoordEffect.pinSpace` induces on the fork. -/
def pinForkSpace : Admissible (LiveStrategy pinInv pinStep pinForkScenario Bool) :=
  ⟨pinLiveTrue, [pinLiveFalse]⟩

theorem pinLiveTrue_cost : liveCost pinLiveTrue.seam pinStep pinForkScenario = 1 := by
  show liveCost (fun s : PinSet => s true) pinStep pinForkScenario = 1
  decide

/-- **Floor and achievement meet: the pin fork's live optimum is exactly one.**
Not slack in a bound — a number. The per-stream floor reports `0`
(`Bounds.zero_floor_does_not_imply_cfcs`, left conjunct) for the same workload. -/
theorem pinFork_liveOptimum_eq_one : liveOptimum pinForkSpace = 1 := by
  have hle : liveOptimum pinForkSpace ≤ liveProfile pinInv pinStep pinForkScenario pinLiveTrue :=
    optimum_le_of_mem pinForkSpace.head_mem
  have hval : liveProfile pinInv pinStep pinForkScenario pinLiveTrue = 1 := pinLiveTrue_cost
  have hge := pinFork_liveOptimum_positive pinForkSpace
  omega

/-! ### The grow-only half -/

/-- A grow-only invariant on the same carrier: node `true` is pinned. This is
`Catalog.gset_mem_iconfluent`'s membership invariant, which *is* I-confluent —
the CALM-shaped side of the line `Cost` §5 calibrates against. -/
def growInv : Invariant PinSet := fun s => s true = true

instance instDecidableGrowInv : DecidablePred growInv := fun s => by
  unfold growInv; infer_instance

theorem growInv_iconfluent : IConfluent growInv := gset_mem_iconfluent true

/-- **The grow-only fork**: same carrier, same transition, same two-branch shape,
rooted at a state where `true` is already pinned. One branch pins `false`, the
other re-pins `true`. -/
def growScenario : Scenario PinSet Bool :=
  ⟨pinStep emptyPin true, [[false], [true]]⟩

theorem growScenario_worlds :
    growScenario.worlds pinStep
      = [pinStep emptyPin true,
         pinStep (pinStep emptyPin true) false,
         pinStep (pinStep emptyPin true) true] := rfl

/-- The root is legal, and so is every world — this is a real fork, not an empty
one. -/
theorem growScenario_worlds_legal : ∀ x ∈ growScenario.worlds pinStep, growInv x := by
  decide

/-- **⚠ NON-VACUITY, THE ZERO HALF.** The grow-only fork has no live clash — its
two divergent branches merge legally — so by the characterisation its live
optimum is zero, achieved by the constant seam. Same carrier, same transition,
same fork shape as `pinForkScenario`: what separates them is the invariant, which
is what a coordination grade is supposed to measure. -/
theorem grow_no_live_clash : ¬ LiveClash growInv pinStep growScenario :=
  no_live_clash_of_iconfluent growInv_iconfluent

/-- The zero, as a live strategy that pays it. -/
theorem grow_liveFree :
    ∃ τ : LiveStrategy growInv pinStep growScenario Nat,
      liveCost τ.seam pinStep growScenario = 0 :=
  (liveFree_iff_no_live_clash 0).mpr grow_no_live_clash

/-- The grow-only space: the constant seam, which is a live strategy here. -/
def growSpace : Admissible (LiveStrategy growInv pinStep growScenario Nat) :=
  ⟨constLiveStrategy 0 grow_no_live_clash, []⟩

/-- …and its optimum is zero, through the named theorem, with `hconst`
discharged. -/
theorem grow_liveOptimum_eq_zero : liveOptimum growSpace = 0 :=
  (liveScenario_optimum_eq_zero_iff_no_live_clash 0 growSpace
    (fun _ => growSpace.head_mem)).mpr grow_no_live_clash

/-- **The two instances, side by side.** One transition, one carrier, two
invariants, two verdicts — and the numbers are exact, not bounds. -/
theorem fork_grade_separates_the_two_invariants :
    liveOptimum pinForkSpace = 1 ∧ liveOptimum growSpace = 0 :=
  ⟨pinFork_liveOptimum_eq_one, grow_liveOptimum_eq_zero⟩

/-! ## §9. ⚠ Why the strategies are protocol-relative — the dependency, proved

codex flagged that the reverse half of §5 fails if a strategy is required to be a
**global** `SegmentedIConfluent` seam, because a clash elsewhere in the lattice
rejects the constant seam over a scenario that has none. That is not restated
here; it is discharged on this tree's own witness. -/

/-- Globally, the constant seam is admissible **exactly** when the invariant is
I-confluent — `Segmented.iconfluent_iff_trivially_segmented` at an arbitrary
colour. So a global strategy space contains no constant seam unless the whole
lattice is free, which is strictly stronger than "this scenario is free". -/
theorem const_segmented_iff_iconfluent {S : Type u} {Seg : Type v} [MergeState S]
    (I : Invariant S) (c₀ : Seg) :
    SegmentedIConfluent (fun _ : S => c₀) I ↔ IConfluent I := by
  constructor
  · intro h x y hx hy; exact (h x y rfl hx hy).1
  · intro h x y _ hx hy; exact ⟨h x y hx hy, rfl⟩

/-- A single-branch pin scenario: pin `true` from nothing. Its two worlds are
comparable, so their merge is legal and there is no live clash — while the
lattice as a whole still has one. -/
def pinSingleScenario : Scenario PinSet Bool := ⟨emptyPin, [[true]]⟩

theorem pinSingle_no_live_clash : ¬ LiveClash pinInv pinStep pinSingleScenario := by
  decide

/-- ⚠ **THE DEPENDENCY, PROVED.** A scenario with **no live clash** whose
constant seam is a live strategy paying zero (first conjunct) and is **not** a
global seam (second conjunct), because the pin lattice has a clash the scenario
never reaches (third conjunct).

So requiring global `SegmentedIConfluent` would delete the term the reverse half
of `liveFree_iff_no_live_clash` is built from, over a scenario the modal verdict
calls free. That is why `LiveStrategy` is pool-relative — a design forced by this
witness, not a convenience.

This pin instance does **not** separate the global optimum: the global seam
`Cost.seamFalse_segmented` also pays zero
(`Cost.pinTrue_free_under_seamFalse`). The formerly open general question is now
refuted by `global_triple_obstruction_cost_positive`, instantiated concretely as
`CliqueLive.atMostTwo_live_global_crossing_gap`; this theorem remains about the
constant-seam dependency it was designed to isolate. -/
theorem const_seam_live_but_not_global :
    (∃ τ : LiveStrategy pinInv pinStep pinSingleScenario Nat,
        liveCost τ.seam pinStep pinSingleScenario = 0)
      ∧ ¬ SegmentedIConfluent (fun _ : PinSet => (0 : Nat)) pinInv
      ∧ ¬ IConfluent pinInv :=
  ⟨(liveFree_iff_no_live_clash 0).mpr pinSingle_no_live_clash,
   fun h => Necessity.reachable_clash_not_iconfluent pinClash
     ((const_segmented_iff_iconfluent pinInv 0).mp h),
   Necessity.reachable_clash_not_iconfluent pinClash⟩

/-! ## §10. `CoordinationGrade` — the record, because one number is not available

codex's last point: "one coordination number" is not a thing the language can
carry, and the grade should be a record — a modal verdict, a **profile** (never a
`Nat`, per `CoordEffect`'s refutation of the scalar grade), the **live scope** the
verdict is about, and the **zero bridge** tying the two together. Here it is,
populated for both worked invariants. -/

/-- The modal verdict of a scenario: coordination is available, or it is not. -/
inductive ModalVerdict where
  /-- Some live strategy runs the whole scenario without coordinating. -/
  | free : ModalVerdict
  /-- Every live strategy must coordinate at least once. -/
  | forced : ModalVerdict
deriving DecidableEq, Repr

/-- **A coordination grade.** Four fields, none of them collapsible to the
others:

  * `verdict` — the modal judgement;
  * `profile` — the cost as a function of the strategy (`CoordEffect.Profile`),
    **not** a number: `CoordEffect.pin_opt_compose_strict` refuted the scalar;
  * `scope` — the worlds the verdict is about, so "free" is never read wider
    than the scenario it was computed on;
  * `zero_bridge` — the verdict is `free` exactly when the profile has a zero,
    which is `liveScenario_optimum_eq_zero_iff_no_live_clash` carried in the
    record rather than left for the reader to reconstruct. -/
structure CoordinationGrade {S : Type u} {Op : Type w} (Seg : Type v) [MergeState S]
    [DecidableEq Seg] (I : Invariant S) (step : S → Op → S) (sc : Scenario S Op) where
  /-- The modal judgement for this scenario. -/
  verdict : ModalVerdict
  /-- The cost profile over live strategies — never a scalar. -/
  profile : Profile (LiveStrategy I step sc Seg)
  /-- The worlds this verdict is about. -/
  scope : List S
  /-- The profile is the edge-charged cost. -/
  profile_is_liveCost : ∀ τ : LiveStrategy I step sc Seg, profile τ = liveCost τ.seam step sc
  /-- The scope is the scenario's worlds. -/
  scope_is_worlds : scope = sc.worlds step
  /-- `free` exactly when some live strategy pays nothing. -/
  zero_bridge : verdict = ModalVerdict.free
    ↔ ∃ τ : LiveStrategy I step sc Seg, profile τ = 0

/-- **The grade of a scenario**, computed. The verdict is decided by the live
clash graph; the bridge is the §5 characterisation. -/
def gradeOf {S : Type u} {Op : Type w} (Seg : Type v) [MergeState S] [DecidableEq Seg]
    (c₀ : Seg) (I : Invariant S) [DecidablePred I] (step : S → Op → S)
    (sc : Scenario S Op) : CoordinationGrade Seg I step sc where
  verdict := if LiveClash I step sc then ModalVerdict.forced else ModalVerdict.free
  profile := liveProfile I step sc
  scope := sc.worlds step
  profile_is_liveCost := fun _ => rfl
  scope_is_worlds := rfl
  zero_bridge := by
    by_cases h : LiveClash I step sc
    · rw [if_pos h]
      constructor
      · intro hv; exact ModalVerdict.noConfusion hv
      · intro hex; exact absurd h ((liveFree_iff_no_live_clash c₀).mp hex)
    · rw [if_neg h]
      exact ⟨fun _ => (liveFree_iff_no_live_clash c₀).mpr h, fun _ => rfl⟩

/-- The pin fork's grade. -/
def pinForkGrade : CoordinationGrade Nat pinInv pinStep pinForkScenario :=
  gradeOf Nat 0 pinInv pinStep pinForkScenario

/-- The grow-only fork's grade. -/
def growGrade : CoordinationGrade Nat growInv pinStep growScenario :=
  gradeOf Nat 0 growInv pinStep growScenario

/-- **The pin fork grades `forced`** — read off the bridge, not off the `if`, so
the verdict is justified by the characterisation rather than by a decision
procedure. -/
theorem pinForkGrade_verdict : pinForkGrade.verdict = ModalVerdict.forced := by
  cases hv : pinForkGrade.verdict with
  | forced => rfl
  | free =>
      obtain ⟨τ, h0⟩ := pinForkGrade.zero_bridge.mp hv
      exact absurd pinFork_liveClash
        (no_live_clash_of_free τ ((pinForkGrade.profile_is_liveCost τ).symm.trans h0))

/-- **The grow-only fork grades `free`**, likewise through the bridge. -/
theorem growGrade_verdict : growGrade.verdict = ModalVerdict.free := by
  refine growGrade.zero_bridge.mpr ⟨constLiveStrategy 0 grow_no_live_clash, ?_⟩
  rw [growGrade.profile_is_liveCost]
  exact constLiveStrategy_free 0 grow_no_live_clash

/-- **The grade separates the two invariants on one carrier and one transition** —
the deliverable, as a term: verdicts differ, and so do the optima the profiles
minimize to. -/
theorem grade_separates :
    pinForkGrade.verdict = ModalVerdict.forced
      ∧ growGrade.verdict = ModalVerdict.free
      ∧ liveOptimum pinForkSpace = 1
      ∧ liveOptimum growSpace = 0 :=
  ⟨pinForkGrade_verdict, growGrade_verdict,
   pinFork_liveOptimum_eq_one, grow_liveOptimum_eq_zero⟩

/-! ## §11. The readings, side by side -/

/-- **The disagreement, resolved.** `Bounds.zero_floor_does_not_imply_cfcs`'s
workload: per-stream floor identically zero (left), live optimum exactly one
(right). Same pin, same transition, same fork. -/
theorem the_disagreement_resolved :
    (∀ (s : PinSet) (bs : List (List Bool)),
        Cost.ClashBlocks pinInv pinStep s bs → bs = [])
      ∧ liveOptimum pinForkSpace = 1 :=
  ⟨zero_floor_does_not_imply_cfcs.1, pinFork_liveOptimum_eq_one⟩

/-- **The modal judgement, quantitatively.** CFCS is local safety plus a zero
live optimum on every realized finite scenario. -/
example {S Op : Type} [MergeState S] (impl : Necessity.Impl S Op) (I : Invariant S) :
    Necessity.IsCFCS impl I
      ↔ Necessity.LocallySafe impl I
          ∧ ∀ (step : S → Op → S) (sc : Scenario S Op),
              I sc.root → sc.Realized impl step →
                ∃ τ : LiveStrategy I step sc Nat, liveCost τ.seam step sc = 0 :=
  cfcs_iff_locallySafe_and_all_finite_scenarios_zero impl I 0

/-- **The missing `Necessity` theorem**, at that file's own refutable witness:
the insert-or-abort implementation is locally safe, so its CFCS failure is
entirely the reachable clash. -/
example : ¬ (Necessity.LocallySafe Necessity.bitAtMostOneImpl Necessity.AtMostOneBit
      ∧ ¬ Nonempty (Necessity.ReachableClash Necessity.bitAtMostOneImpl
            Necessity.AtMostOneBit)) := by
  intro h
  exact Necessity.atMostOneBit_impl_not_cfcs
    ((cfcs_iff_locallySafe_and_no_reachableClash
      Necessity.bitAtMostOneImpl Necessity.AtMostOneBit).mpr h)

end Uwueave.ForkGrade
