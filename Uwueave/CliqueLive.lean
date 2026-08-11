/-
# Uwueave.CliqueLive — the clique number of the LIVE clash graph.

Three modules of wave 16 hold three pieces of one graph story, and none of them
can state it, because each is missing the other two's vocabulary.

  * `MenuTotality.lean` draws the **global** clash graph and proves what a clique
    in it costs: `clique_forces_colors` (a `k`-clique forces `k` segment values)
    and `clique_forces_joint_crossings` (`k` streams from a common start with
    pairwise-clashing endpoints pay `k-1` crossings jointly). Both are stated
    against `Segmented.SegmentedIConfluent` — the **lattice-global** certificate.
  * `LiveSegmented.lean` draws the **live** clash graph — `LiveClashes`, which is
    `Clashes` plus `CoReachable` — and proves that relativising to a protocol
    lowers the width: `live_optimum_strictly_below_global_optimum`, 2 against 3,
    both `LeastSuch`. Its two width refutations are hand-rolled pigeonholes.
  * `ForkGrade.lean` draws the same graph on a **scenario**'s worlds and prices a
    session: `liveScenario_optimum_eq_zero_iff_no_live_clash`, and its
    contrapositive `one_le_liveOptimum_of_liveClash` — a floor of exactly `1`,
    because the only obstruction it counts is a single edge.

The story none of them can state: **the clique number of the live clash graph is
one invariant that determines both quantities** — how many coordination domains a
deployment must build, and how many crossings a session pays. §1 transports the
colour bound, §2 the crossing bound, §3 says when the two numbers coincide, §4
runs the transport on the slot carrier and exhibits the hypothesis that carries
it, §5 answers the objection that a seam is more than a colouring, §6 answers
what a checker must report, §7 collects the chain.

## What is new here, in one line each

  * `live_clique_forces_live_width` — a `k`-clique of **co-reachable** worlds
    forces `LiveWidth ≥ k`. Cleaner than the global bound it transports: no
    covering pool, because the live vertex set is the quantifier's own domain.
  * `liveClique_of_stream_clique` — `k` streams from one base whose endpoints
    pairwise clash **are** a live clique, with no co-reachability side condition
    to discharge. This is the branch structure `clique_forces_joint_crossings`
    assumed and `Scenario` makes definitional.
  * `live_clique_forces_scenario_floor` — a scenario whose branch endpoints form
    a `k`-clique has `liveOptimum ≥ k-1`, over **every** space of live
    strategies. `ForkGrade.one_le_liveOptimum_of_liveClash` is `k = 2`.
  * `clique_forces_joint_crossings_on` — the crossing floor needs only the
    **colouring** clause on a pool, never fiber stability and never a global
    seam. That is what lets the floor be charged to a `LiveStrategy`.
  * `least_liveWidth_of_clique_and_seam` — a `k`-clique plus a `k`-domain seam
    **certify** the optimum. `LiveSegmented`'s two pigeonholes
    (`no_live_seam_into_fin_one`, `no_global_seam_into_fin_two`) are corollaries:
    `the_pigeonholes_were_clique_bounds`.
  * `no_live_triangle` — the slot carrier has **no** live 3-clique, so the live
    clique number is 2 where the global one is 3; and `no_three_stream_clique` is
    the operational form: the three-stream workload the global triangle would
    price cannot be run. §4.1 adds the third op back and both numbers return to 3
    (`the_third_op_restores_the_third_domain`), so the bound is not capped at 2
    by construction and the transport hypothesis is priced rather than asserted.
  * `triple_clash_forces_triangle` — a three-way obstruction with pairwise-legal
    joins forces a genuine **triangle** among the three pairwise joins. This is
    §5's answer to "a seam is a colouring *plus stability*, so surely width can
    exceed the chromatic number": the first constraint stability adds beyond
    colouring is itself clique-visible. §5.1 realises it on a carrier —
    "at most two of three slots", where **no two** of the three single claims
    clash (`atMostTwo_generators_do_not_clash`) and the optimum is nevertheless
    exactly 3 (`atMostTwo_least_width`), the whole number coming from a
    three-way obstruction read off the pairwise joins.
  * `atMostTwo_live_global_crossing_gap` — the crossing separation the earlier
    slot workload could not provide. Three one-op branches are pairwise legal,
    so an honest constant live strategy pays `0`; every global seam pays at
    least `1`, because zero would put all generators in one fiber and global
    stability would derive legality of their illegal triple join. A global seam
    paying exactly `1` proves the floor is attainable.
  * `the_two_floors_are_incomparable` — the clique floor and the block floor each
    report `0` on the workload where the other reports a positive number, so a
    checker must run both.

## The width/clique verdict, at the resolution it is actually proved

Write ω for the clique number of the clash graph, χ for its chromatic number, and
`Width` for the least `n` admitting a *seam* into `Fin n`.

  * **`Width ≥ ω` is proved here, in both flavours** — `live_clique_forces_live_width`
    and `clique_forces_global_width`. Unconditional, no finiteness, no perfection.
  * **`Width = ω` is NOT claimed in general, and this file does not claim it.**
    Two independent gaps sit between them, and they are different gaps:
      1. `χ ≥ ω` can be strict — the classical witness is `C₅` (ω = 2, χ = 3).
         ⟨UNDONE⟩ No clash graph realising `C₅` is exhibited here, so this file
         does not even settle whether the gap is *reachable* in this setting; it
         is cited as graph theory, not proved as a fact about clash graphs.
      2. `Width ≥ χ` can be strict for a reason that is **not** graph theory: a
         seam is a proper colouring *and* fiber-stable
         (`LiveSegmented.liveSegmented_iff_liveProperColoring`), so every colour
         class must be closed under the joins of its own members. §5 shows the
         first non-trivial instance of that constraint is clique-visible anyway
         (`triple_clash_forces_triangle`, realised on a carrier in §5.1);
         ⟨UNDONE⟩ the general `k`-wise case is
         argued in §5's docstring and not proved, and no numeric separation of
         `Width` from `χ` is exhibited.
  * **What replaces the general theorem** is a certificate: `Width = k` is
    *witnessed* by a `k`-clique and a `k`-domain seam together
    (`least_liveWidth_of_clique_and_seam`). On the slot carrier both witnesses
    exist at both certificates — live 2/2, global 3/3 — so equality holds *there*,
    and §4 proves it there rather than asserting it everywhere. A checker can
    always try to produce the pair; it just cannot be promised one.

⚠ The honest reason the two numbers agree on this carrier is that its clash graph
is a **union of complete graphs** (globally: one triangle plus an isolated `sO`;
live: one edge plus two isolated vertices), and unions of cliques are perfect. The
general theorem `width_eq_clique_of_cliqueUnion` is **not** in this file: perfection
delivers `χ = ω`, and gap (2) above — stability — is left over. Naming the missing
theorem is not the same as having it.

## Non-claims

  * ⟨scope⟩ Everything here is `Cost.crossings` currency and inherits
    `Cost.lean`'s "crossings are not meetings" whole.
  * ⟨scope⟩ `LiveWidth` is protocol-relative and inherits `LiveSegmented`'s
    ⟨UNDONE⟩ "faithfulness of `P` is the modeller's": a live clique bound issued
    against an under-permissive `RunModel` is unsound for the real deployment.
  * ⟨UNDONE⟩ No clique is *synthesised*. Every bound below consumes a clique
    somebody exhibits; finding the maximum one is the same search
    `SeamColoring.lean` leaves open for minimum colourings.
  * ⟨UNDONE⟩ `no_live_triangle` is proved for the slot carrier by exhausting its
    four legal states. Nothing here computes a live clique number in general.

This file edits none of the three modules; it imports them and relates them by
theorem.
-/
import Uwueave.MenuTotality
import Uwueave.LiveSegmented
import Uwueave.ForkGrade

namespace Uwueave.CliqueLive

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.SeamColoring Uwueave.CoordEffect

universe u v w z

/-! ## §1. The live clique, and the width it forces.

`MenuTotality.Clique` is a list of states, pairwise clashing. Its live form is a
list of **worlds**, pairwise live-clashing — `LiveSegmented.LiveClashes`, which
is `Clashes` on the observations *and* co-reachability from a common base. The
second conjunct is the entire content: it is what a protocol can refute. -/

/-- **A live clique.** A list of worlds that pairwise live-clash from a common
base: every pair is co-reachable from `base` and its observations clash. This is
`MenuTotality.Clique` with `SeamColoring.Clashes` replaced by
`LiveSegmented.LiveClashes`. -/
def LiveClique {W : Type u} {Op : Type v} {S : Type w} [MergeState S]
    (P : LiveSegmented.RunModel W Op S) (I : Invariant S) (base : W) (K : List W) : Prop :=
  K.Pairwise (LiveSegmented.LiveClashes P I base)

/-- **A live clique is a global clique on the observations** — dropping the
co-reachability conjunct is free. So the live clique number never exceeds the
global one, which is the numeric half of `segmented_implies_liveSegmented`. -/
theorem clique_of_liveClique {W : Type u} {Op : Type v} {S : Type w} [MergeState S]
    {P : LiveSegmented.RunModel W Op S} {I : Invariant S} {base : W} {K : List W}
    (hK : LiveClique P I base K) : MenuTotality.Clique I (K.map P.observe) := by
  show List.Pairwise (Clashes I) (K.map P.observe)
  rw [List.pairwise_map]
  exact hK.imp (fun h => h.2)

/-- Combining a pairwise fact with a membership-quantified one. Lean core has
`List.Pairwise` and no mathlib is available, so the `∧`-introduction is done
here by induction. -/
private theorem pairwise_and_of_mem {α : Type u} {R Q : α → α → Prop} :
    ∀ {l : List α}, List.Pairwise R l → (∀ a ∈ l, ∀ b ∈ l, Q a b) →
      List.Pairwise (fun a b => Q a b ∧ R a b) l := by
  intro l
  induction l with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons a l ih =>
      intro hp hq
      have hc := List.pairwise_cons.mp hp
      refine List.Pairwise.cons (fun b hb => ⟨?_, hc.1 b hb⟩) (ih hc.2 ?_)
      · exact hq a List.mem_cons_self b (List.mem_cons_of_mem a hb)
      · exact fun x hx y hy =>
          hq x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)

/-- **…and the converse needs exactly co-reachability.** A global clique whose
worlds are pairwise co-reachable from one base is a live clique. §4 exhibits the
carrier where the hypothesis fails and the conclusion with it. -/
theorem liveClique_of_clique {W : Type u} {Op : Type v} {S : Type w} [MergeState S]
    {P : LiveSegmented.RunModel W Op S} {I : Invariant S} {base : W} {K : List W}
    (hco : ∀ x ∈ K, ∀ y ∈ K, LiveSegmented.CoReachable P base x y)
    (hK : MenuTotality.Clique I (K.map P.observe)) : LiveClique P I base K := by
  have hK' : List.Pairwise (fun a b => Clashes I (P.observe a) (P.observe b)) K := by
    have h : List.Pairwise (Clashes I) (K.map P.observe) := hK
    rw [List.pairwise_map] at h
    exact h
  exact pairwise_and_of_mem hK' hco

/-- **A live seam is injective on a live clique.** The live transport of
`MenuTotality.clique_colors_nodup`: every live edge is separated, so the colours
along a live clique are pairwise distinct — `k` worlds, `k` fibers. -/
theorem liveClique_colors_nodup {W : Type u} {Op : Type v} {S : Type w} {Seg : Type z}
    [MergeState S] {P : LiveSegmented.RunModel W Op S} {I : Invariant S} {σ : S → Seg}
    {base : W} {K : List W} (hseg : LiveSegmented.LiveSegmented P σ I)
    (hK : LiveClique P I base K) : (K.map (fun x => σ (P.observe x))).Nodup := by
  show List.Pairwise (· ≠ ·) (K.map (fun x => σ (P.observe x)))
  rw [List.pairwise_map]
  exact hK.imp (fun hab hEq => hab.2.2.2 (hseg base _ _ hab.1 hEq hab.2.1 hab.2.2.1).1)

/-- **THE LIVE LOWER BOUND ON COLOURS.** If a live `k`-clique's colours all lie
in a list `C`, then `k ≤ C.length`. The live transport of
`MenuTotality.clique_forces_colors`, and it is cleaner in exactly the way §5 of
`LiveSegmented` predicted: the global statement needs a covering pool, and the
live one does not, because the live vertex set *is* the quantifier's domain. -/
theorem live_clique_forces_colors {W : Type u} {Op : Type v} {S : Type w} {Seg : Type z}
    [MergeState S] [DecidableEq Seg] {P : LiveSegmented.RunModel W Op S}
    {I : Invariant S} {σ : S → Seg} {base : W} {K : List W} {C : List Seg}
    (hseg : LiveSegmented.LiveSegmented P σ I) (hK : LiveClique P I base K)
    (hC : ∀ x ∈ K, σ (P.observe x) ∈ C) : K.length ≤ C.length := by
  have hsub : ∀ c ∈ K.map (fun x => σ (P.observe x)), c ∈ C := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    exact hC x hx
  have h := MenuTotality.nodup_length_le_of_subset (K.map (fun x => σ (P.observe x))) C
    (liveClique_colors_nodup hseg hK) hsub
  rw [List.length_map] at h
  exact h

/-- Pigeonhole into `Fin n`: a repeat-free list of coordination domains is no
longer than the number of domains. `Fin.val` is injective and lands in
`List.range n`, so this is `MenuTotality.nodup_length_le_of_subset` at `Nat`. -/
theorem nodup_fin_length_le {n : Nat} (l : List (Fin n)) (h : l.Nodup) : l.length ≤ n := by
  have hnd : (l.map Fin.val).Nodup := by
    show List.Pairwise (· ≠ ·) (l.map Fin.val)
    rw [List.pairwise_map]
    exact h.imp (fun hne hval => hne (Fin.eq_of_val_eq hval))
  have hsub : ∀ a ∈ l.map Fin.val, a ∈ List.range n := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact List.mem_range.mpr i.isLt
  have h2 := MenuTotality.nodup_length_le_of_subset (l.map Fin.val) (List.range n) hnd hsub
  rw [List.length_map, List.length_range] at h2
  exact h2

/-- **⚑ CHASE 1 — a live `k`-clique forces `k` coordination domains.** If `k`
worlds pairwise live-clash from a common base, no seam into fewer than `k`
domains is a live seam. The number is read off the **live** clash graph, before
any search, and it bounds the quantity `LiveSegmented` §4 optimises. -/
theorem live_clique_forces_live_width {W : Type u} {Op : Type v} {S : Type w}
    [MergeState S] {P : LiveSegmented.RunModel W Op S} {I : Invariant S} {base : W}
    {K : List W} {n : Nat} (hK : LiveClique P I base K)
    (h : LiveSegmented.LiveWidth P I n) : K.length ≤ n := by
  obtain ⟨σ, hσ⟩ := h
  have hnd := nodup_fin_length_le _ (liveClique_colors_nodup hσ hK)
  rw [List.length_map] at hnd
  exact hnd

/-- The global mirror, for the transport row: a `k`-clique forces `k` domains
under the carrier-global certificate. `MenuTotality.clique_forces_colors` phrased
against `GlobalWidth` rather than against a supplied list of colours. -/
theorem clique_forces_global_width {S : Type w} [MergeState S] {I : Invariant S}
    {K : List S} {n : Nat} (hK : MenuTotality.Clique I K)
    (h : LiveSegmented.GlobalWidth I n) : K.length ≤ n := by
  obtain ⟨σ, hσ⟩ := h
  have hnd := nodup_fin_length_le _ (MenuTotality.clique_colors_nodup hσ hK)
  rw [List.length_map] at hnd
  exact hnd

/-- **The live width is never above the global one.** Immediate from
`LiveSegmented.segmented_implies_liveSegmented`, and stated because §4 needs both
sides of the pair `live clique ≤ global clique`, `live width ≤ global width` to
say the two drops are the same drop. -/
theorem liveWidth_of_globalWidth {W : Type u} {Op : Type v} {S : Type w} [MergeState S]
    (P : LiveSegmented.RunModel W Op S) {I : Invariant S} {n : Nat}
    (h : LiveSegmented.GlobalWidth I n) : LiveSegmented.LiveWidth P I n := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, LiveSegmented.segmented_implies_liveSegmented hσ⟩

/-! ## §2. Streams — a fork is a live clique for free, and what it costs.

`MenuTotality.clique_forces_joint_crossings` charges `k-1` crossings to `k`
streams from a common start whose endpoints pairwise clash. Two things were left
implicit there and are made explicit here.

  * The streams' endpoints are *automatically* co-reachable
    (`LiveSegmented.coReachable_exec`), so a stream clique is a live clique with
    nothing to discharge — `liveClique_of_stream_clique`. That is the branch
    structure a `ForkGrade.Scenario` has by construction.
  * The proof never uses fiber stability and never uses the seam off the
    endpoints: it uses `hseg` exactly once, to refute a monochromatic clash edge.
    So the floor holds for a **proper colouring on a pool** —
    `clique_forces_joint_crossings_on` — which is precisely what a
    `ForkGrade.LiveStrategy` carries. -/

/-- **`k` streams from one base are a live clique as soon as their endpoints
pairwise clash.** No co-reachability hypothesis appears: it is discharged by
`LiveSegmented.coReachable_exec`, for every pair at once. -/
theorem liveClique_of_stream_clique {W : Type u} {Op : Type v} {S : Type w} [MergeState S]
    {P : LiveSegmented.RunModel W Op S} {I : Invariant S} (base : W) (ws : List (List Op))
    (hK : MenuTotality.Clique I ((ws.map (P.exec base)).map P.observe)) :
    LiveClique P I base (ws.map (P.exec base)) := by
  have h : List.Pairwise (Clashes I) ((ws.map (P.exec base)).map P.observe) := hK
  rw [List.map_map, List.pairwise_map] at h
  show List.Pairwise (LiveSegmented.LiveClashes P I base) (ws.map (P.exec base))
  rw [List.pairwise_map]
  exact h.imp (fun {a} {b} hc => ⟨LiveSegmented.coReachable_exec P base a b, hc⟩)

/-- **THE CROSSING FLOOR NEEDS ONLY THE COLOURING CLAUSE, ON A POOL.**
`MenuTotality.clique_forces_joint_crossings` with `SegmentedIConfluent σ I`
weakened to `ProperColoring V σ I` and a hypothesis that the endpoints lie in
`V`. Same conclusion, same induction; the seam's stability clause and its
behaviour off `V` are never consulted. This is what lets the floor be charged to
a protocol-relative strategy in the next theorem. -/
theorem clique_forces_joint_crossings_on {S : Type w} {Seg : Type z} {Op : Type v}
    [MergeState S] [DecidableEq Seg] {σ : S → Seg} {I : Invariant S} {V : List S}
    {step : S → Op → S} {s : S} (hcol : ProperColoring V σ I) :
    ∀ ws : List (List Op), (∀ p ∈ ws, Cost.run step s p ∈ V) →
      MenuTotality.Clique I (ws.map (Cost.run step s)) →
      ws.length ≤ jointCost σ step s ws + 1 := by
  intro ws
  induction ws with
  | nil => intro _ _; exact Nat.zero_le _
  | cons w ws ih =>
      intro hmem hK
      have hK' : List.Pairwise (Clashes I) (Cost.run step s w :: ws.map (Cost.run step s)) := hK
      have hcons := List.pairwise_cons.mp hK'
      have hj : jointCost σ step s (w :: ws)
          = Cost.crossings σ step s w + jointCost σ step s ws :=
        ForkGrade.jointCost_cons σ step s w ws
      by_cases hz : Cost.crossings σ step s w = 0
      · have hall : ∀ v ∈ ws, 1 ≤ Cost.crossings σ step s v := by
          intro v hv
          rcases Nat.eq_zero_or_pos (Cost.crossings σ step s v) with h0 | hp
          · exfalso
            have e1 := Cost.sigma_const_of_crossings_eq_zero hz
            have e2 := Cost.sigma_const_of_crossings_eq_zero h0
            have hc : Clashes I (Cost.run step s w) (Cost.run step s v) :=
              hcons.1 _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
            exact hcol _ (hmem w List.mem_cons_self) _
              (hmem v (List.mem_cons_of_mem w hv)) hc (e1.trans e2.symm)
          · exact hp
        have h2 := MenuTotality.length_le_jointCost_of_all_pos ws hall
        show ws.length + 1 ≤ jointCost σ step s (w :: ws) + 1
        omega
      · have h2 := ih (fun p hp => hmem p (List.mem_cons_of_mem w hp)) hcons.2
        have h1 : 1 ≤ Cost.crossings σ step s w := Nat.pos_of_ne_zero hz
        show ws.length + 1 ≤ jointCost σ step s (w :: ws) + 1
        omega

/-- **⚑ CHASE 2 — a scenario whose branch endpoints form a `k`-clique pays
`k-1`.** The floor holds over **every** space of live strategies, at every
segment type, in every universe — the live transport of
`MenuTotality.clique_joint_floor`, with the global seam replaced by a
`ForkGrade.LiveStrategy` and the co-reachability side condition gone: a
scenario's branch endpoints are worlds of the scenario by construction
(`ForkGrade.Scenario.run_mem_worlds`), which is the pool `LiveStrategy.proper`
colours. -/
theorem live_clique_forces_scenario_floor {S : Type w} {Op : Type v} {Seg : Type z}
    [MergeState S] [DecidableEq Seg] {I : Invariant S} {step : S → Op → S}
    {sc : ForkGrade.Scenario S Op}
    (hK : MenuTotality.Clique I (sc.paths.map (Cost.run step sc.root)))
    (A : Admissible (ForkGrade.LiveStrategy I step sc Seg)) :
    sc.paths.length - 1 ≤ ForkGrade.liveOptimum A := by
  refine le_optimum (fun τ _ => ?_)
  have h := clique_forces_joint_crossings_on τ.proper sc.paths
    (fun p hp => sc.run_mem_worlds step p hp) hK
  have he : ForkGrade.liveProfile I step sc τ
      = jointCost τ.seam step sc.root sc.paths := rfl
  rw [he]
  omega

/-- **A clique of two or more branch endpoints is a `ForkGrade.LiveClash`.** So
every scenario `live_clique_forces_scenario_floor` charges is also charged by
`ForkGrade.one_le_liveOptimum_of_liveClash` — and at `sc.paths = [p, q]` the two
numbers are the same `1`, which is the tree's floor read as the clique floor at
`k = 2`. Above two branches the clique floor is `sc.paths.length - 1` and the
tree's stays `1`. -/
theorem two_stream_clique_is_a_live_clash {S : Type w} {Op : Type v} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {sc : ForkGrade.Scenario S Op}
    {p q : List Op} {rest : List (List Op)} (hpaths : sc.paths = p :: q :: rest)
    (hK : MenuTotality.Clique I (sc.paths.map (Cost.run step sc.root))) :
    ForkGrade.LiveClash I step sc := by
  have hK' : List.Pairwise (Clashes I) (sc.paths.map (Cost.run step sc.root)) := hK
  rw [hpaths, List.map_cons, List.map_cons] at hK'
  have hc : Clashes I (Cost.run step sc.root p) (Cost.run step sc.root q) :=
    (List.pairwise_cons.mp hK').1 _ List.mem_cons_self
  refine ⟨Cost.run step sc.root p, sc.run_mem_worlds step p (by rw [hpaths]; exact List.mem_cons_self),
    Cost.run step sc.root q, sc.run_mem_worlds step q ?_, hc⟩
  rw [hpaths]
  exact List.mem_cons_of_mem p List.mem_cons_self

/-! ## §3. When a clique certifies the optimum.

§1 gives `Width ≥ ω` and nothing more. The module docstring says why `Width = ω`
is not available in general. What *is* available, and is what a checker can
actually produce, is a **matching pair**: a `k`-clique and a `k`-domain seam
together pin the optimum exactly, with no perfection hypothesis and no search. -/

/-- **A `k`-clique plus a `k`-domain live seam certify the live optimum.** The
clique refutes every smaller width and the seam achieves `k`, so `k` is
`LeastSuch` — which is `LiveSegmented` §4's own notion of an optimum. -/
theorem least_liveWidth_of_clique_and_seam {W : Type u} {Op : Type v} {S : Type w}
    [MergeState S] {P : LiveSegmented.RunModel W Op S} {I : Invariant S} {base : W}
    {K : List W} {k : Nat} (hK : LiveClique P I base K) (hlen : K.length = k)
    (hseam : LiveSegmented.LiveWidth P I k) :
    LiveSegmented.LeastSuch (LiveSegmented.LiveWidth P I) k := by
  refine ⟨hseam, fun m hm => ?_⟩
  rw [← hlen]
  exact live_clique_forces_live_width hK hm

/-- The same certificate for the carrier-global optimum. -/
theorem least_globalWidth_of_clique_and_seam {S : Type w} [MergeState S]
    {I : Invariant S} {K : List S} {k : Nat} (hK : MenuTotality.Clique I K)
    (hlen : K.length = k) (hseam : LiveSegmented.GlobalWidth I k) :
    LiveSegmented.LeastSuch (LiveSegmented.GlobalWidth I) k := by
  refine ⟨hseam, fun m hm => ?_⟩
  rw [← hlen]
  exact clique_forces_global_width hK hm

/-! ## §4. The slot carrier — the transport, and the vertex the protocol cannot
reach.

`LiveSegmented` §3 is a three-slot uniqueness ceiling whose protocol can claim
two of the three slots. Its clash graph is a **triangle** globally and a single
**edge** live, because `sC` is co-reachable with nothing
(`LiveSegmented.sA_sC_not_coReachable`). This section says the widths drop
because the clique numbers drop, and that they drop by the same one. -/

/-- The live 2-clique: the two claimable slots, forked from the empty state. -/
theorem slot_live_clique_two :
    LiveClique LiveSegmented.slotProtocol LiveSegmented.atMostOne LiveSegmented.sO
      [LiveSegmented.sA, LiveSegmented.sB] := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
  intro b hb
  have hb' : b = LiveSegmented.sB := by simpa using hb
  subst hb'
  exact ⟨LiveSegmented.sA_sB_coReachable, by decide⟩

/-- The global 3-clique: `LiveSegmented.slots_clash_graph`'s triangle, as a
clique. -/
theorem slot_global_clique_three :
    MenuTotality.Clique LiveSegmented.atMostOne
      [LiveSegmented.sA, LiveSegmented.sB, LiveSegmented.sC] := by
  refine List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil))
  · intro b hb
    have hb' : b = LiveSegmented.sB ∨ b = LiveSegmented.sC := by simpa using hb
    rcases hb' with rfl | rfl <;> decide
  · intro b hb
    have hb' : b = LiveSegmented.sC := by simpa using hb
    subst hb'
    decide

/-- ⚠ **THERE IS NO LIVE TRIANGLE ON THE SLOT CARRIER.** Three worlds pairwise
co-reachable from any base and pairwise clashing do not exist: co-reachable
worlds agree on the `c` flag (`LiveSegmented.coReachable_sameC`), the legal
states with a given `c` flag are `{sO, sA, sB}` or `{sC}`, and `sO` clashes with
nothing. So the live clique number is **2** where the global one is **3**, and
the missing vertex is exactly the one `LiveSegmented`'s
`the_third_domain_is_charged_for_an_unreachable_pair` names. -/
theorem no_live_triangle (base x y z : LiveSegmented.Slots)
    (h : LiveClique LiveSegmented.slotProtocol LiveSegmented.atMostOne base [x, y, z]) :
    False := by
  have h' : List.Pairwise
      (LiveSegmented.LiveClashes LiveSegmented.slotProtocol LiveSegmented.atMostOne base)
      [x, y, z] := h
  have hhead := List.pairwise_cons.mp h'
  have hxy := hhead.1 y List.mem_cons_self
  have hxz := hhead.1 z (List.mem_cons_of_mem y List.mem_cons_self)
  have hyz := (List.pairwise_cons.mp hhead.2).1 z List.mem_cons_self
  have hcxy : x.c = y.c := LiveSegmented.coReachable_sameC hxy.1
  have hcxz : x.c = z.c := LiveSegmented.coReachable_sameC hxz.1
  have hclxy : Clashes LiveSegmented.atMostOne x y := hxy.2
  have hclxz : Clashes LiveSegmented.atMostOne x z := hxz.2
  have hclyz : Clashes LiveSegmented.atMostOne y z := hyz.2
  have hx : LiveSegmented.atMostOne x := hclxy.1
  have hy : LiveSegmented.atMostOne y := hclxy.2.1
  have hz : LiveSegmented.atMostOne z := hclxz.2.1
  rcases LiveSegmented.legal_cases x hx with rfl | rfl | rfl | rfl <;>
    rcases LiveSegmented.legal_cases y hy with rfl | rfl | rfl | rfl <;>
      rcases LiveSegmented.legal_cases z hz with rfl | rfl | rfl | rfl <;>
        revert hcxy hcxz hclxy hclxz hclyz <;> decide

/-- ⚠ **…so the three-stream workload the global triangle would price cannot be
run.** `MenuTotality.clique_forces_joint_crossings` charges `2` to three streams
with pairwise-clashing endpoints; over this protocol no three streams have them,
from any base. The global clique number is a floor on a workload the deployment
has no operation to produce — the `crossings` reading of
`the_third_domain_is_charged_for_an_unreachable_pair`. -/
theorem no_three_stream_clique (base : LiveSegmented.Slots)
    (w₁ w₂ w₃ : List LiveSegmented.ClaimOp) :
    ¬ MenuTotality.Clique LiveSegmented.atMostOne
        ([w₁, w₂, w₃].map (Cost.run LiveSegmented.claimStep base)) := by
  intro hK
  exact no_live_triangle base _ _ _
    (liveClique_of_stream_clique (P := LiveSegmented.slotProtocol) base [w₁, w₂, w₃] hK)

/-- **The two optima, re-derived from clique certificates.** `LiveSegmented`
proves these two numbers with two hand-rolled pigeonholes; here each is a
`k`-clique against a `k`-domain seam, and nothing else. -/
theorem slot_live_least_width :
    LiveSegmented.LeastSuch
      (LiveSegmented.LiveWidth LiveSegmented.slotProtocol LiveSegmented.atMostOne) 2 :=
  least_liveWidth_of_clique_and_seam slot_live_clique_two rfl
    ⟨LiveSegmented.sigmaLive, LiveSegmented.sigmaLive_liveSegmented⟩

theorem slot_global_least_width :
    LiveSegmented.LeastSuch (LiveSegmented.GlobalWidth LiveSegmented.atMostOne) 3 :=
  least_globalWidth_of_clique_and_seam slot_global_clique_three rfl
    ⟨LiveSegmented.sigmaGlobal, LiveSegmented.sigmaGlobal_segmented⟩

/-- **⚑ The two pigeonholes were clique bounds.**
`LiveSegmented.no_live_seam_into_fin_one` is an explicit argument about `Fin 1`
and `LiveSegmented.no_global_seam_into_fin_two` discharges a three-way
distinctness by `decide` on `Fin 2`. Both are instances of §1: a `k`-clique and a
seam into fewer than `k` domains cannot coexist. Proved here from the clique
bounds, not by citing those two theorems. -/
theorem the_pigeonholes_were_clique_bounds :
    (∀ σ : LiveSegmented.Slots → Fin 1,
        ¬ LiveSegmented.LiveSegmented LiveSegmented.slotProtocol σ LiveSegmented.atMostOne)
    ∧ (∀ σ : LiveSegmented.Slots → Fin 2,
        ¬ SegmentedIConfluent σ LiveSegmented.atMostOne) := by
  constructor
  · intro σ hσ
    have h := live_clique_forces_live_width slot_live_clique_two ⟨σ, hσ⟩
    simp at h
  · intro σ hσ
    have h := clique_forces_global_width slot_global_clique_three ⟨σ, hσ⟩
    simp at h

/-! ### §4.1 The missing operation is the missing domain

⚠ `no_live_triangle` must not be read as "live cliques never reach 3" — that
would make §1's bound useless above 2 and the transport row vacuous. It is a fact
about **this protocol's op vocabulary**, and the way to prove that is to add the
op back. Same carrier, same invariant, same four legal states; one more
operation, and the live clique number and the live optimum both return to 3.

This is `LiveSegmented`'s ⟨TERMINAL⟩ non-claim — "`LiveSegmented` is not robust
under enlarging `Op`" — as a number. -/

/-- The op alphabet that can claim **all three** slots. -/
inductive ClaimOp3
  | claimA
  | claimB
  | claimC
  deriving DecidableEq, Repr

/-- The local transition. Unlike `LiveSegmented.claimStep`, this one can set
`c` — which is the single fact §4 turned on. -/
def claim3Step (s : LiveSegmented.Slots) : ClaimOp3 → LiveSegmented.Slots
  | .claimA => { s with a := true }
  | .claimB => { s with b := true }
  | .claimC => { s with c := true }

/-- The enlarged protocol, on the same carrier and the same invariant. -/
def slotProtocol3 : LiveSegmented.RunModel LiveSegmented.Slots ClaimOp3 LiveSegmented.Slots where
  step := claim3Step
  observe := fun s => s

/-- **A live 3-clique exists** — so §1's bound is not capped at 2 by
construction, and `no_live_triangle` is a statement about the two-op protocol
rather than about live cliques. -/
theorem slot3_live_clique_three :
    LiveClique slotProtocol3 LiveSegmented.atMostOne LiveSegmented.sO
      [LiveSegmented.sA, LiveSegmented.sB, LiveSegmented.sC] := by
  have hab : LiveSegmented.CoReachable slotProtocol3 LiveSegmented.sO
      LiveSegmented.sA LiveSegmented.sB := ⟨⟨[ClaimOp3.claimA], rfl⟩, ⟨[ClaimOp3.claimB], rfl⟩⟩
  have hac : LiveSegmented.CoReachable slotProtocol3 LiveSegmented.sO
      LiveSegmented.sA LiveSegmented.sC := ⟨⟨[ClaimOp3.claimA], rfl⟩, ⟨[ClaimOp3.claimC], rfl⟩⟩
  have hbc : LiveSegmented.CoReachable slotProtocol3 LiveSegmented.sO
      LiveSegmented.sB LiveSegmented.sC := ⟨⟨[ClaimOp3.claimB], rfl⟩, ⟨[ClaimOp3.claimC], rfl⟩⟩
  refine List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil))
  · intro b hb
    have hb' : b = LiveSegmented.sB ∨ b = LiveSegmented.sC := by simpa using hb
    rcases hb' with rfl | rfl
    · exact ⟨hab, by decide⟩
    · exact ⟨hac, by decide⟩
  · intro b hb
    have hb' : b = LiveSegmented.sC := by simpa using hb
    subst hb'
    exact ⟨hbc, by decide⟩

/-- **⚑ The live optimum of the enlarged protocol is 3.** Certified by the live
3-clique against the three-domain global seam, which is live-valid for every
protocol at once (`LiveSegmented.segmented_implies_liveSegmented`). -/
theorem slot3_live_least_width :
    LiveSegmented.LeastSuch
      (LiveSegmented.LiveWidth slotProtocol3 LiveSegmented.atMostOne) 3 :=
  least_liveWidth_of_clique_and_seam slot3_live_clique_three rfl
    (liveWidth_of_globalWidth slotProtocol3
      ⟨LiveSegmented.sigmaGlobal, LiveSegmented.sigmaGlobal_segmented⟩)

/-- **⚑ CHASE 4 — the transport hypothesis, priced.** One carrier, one
invariant, two op vocabularies. Without `claimC` the live clash graph has no
triangle and the live optimum is 2; with it the triangle is live and the live
optimum is 3. The hypothesis `liveClique_of_clique` asks for — pairwise
co-reachability — is exactly what the third operation supplies, and the domain
`LiveSegmented.the_third_domain_is_charged_for_an_unreachable_pair` calls
unearned is earned the moment the pair becomes reachable. -/
theorem the_third_op_restores_the_third_domain :
    (∀ base x y z : LiveSegmented.Slots,
        ¬ LiveClique LiveSegmented.slotProtocol LiveSegmented.atMostOne base [x, y, z])
    ∧ LiveSegmented.LeastSuch
        (LiveSegmented.LiveWidth LiveSegmented.slotProtocol LiveSegmented.atMostOne) 2
    ∧ LiveClique slotProtocol3 LiveSegmented.atMostOne LiveSegmented.sO
        [LiveSegmented.sA, LiveSegmented.sB, LiveSegmented.sC]
    ∧ LiveSegmented.LeastSuch
        (LiveSegmented.LiveWidth slotProtocol3 LiveSegmented.atMostOne) 3 :=
  ⟨fun base x y z h => no_live_triangle base x y z h, slot_live_least_width,
   slot3_live_clique_three, slot3_live_least_width⟩

/-! ### The scenario, and the floor it pays

The two-branch scenario that forks the live clash. Its endpoints form the live
2-clique, so §2 charges it `1` — and the two-domain live seam pays exactly `1`,
so the floor is attained rather than merely quoted. -/

/-- The forking scenario: claim A on one branch, claim B on the other. -/
def slotScenario : ForkGrade.Scenario LiveSegmented.Slots LiveSegmented.ClaimOp where
  root := LiveSegmented.sO
  paths := [[LiveSegmented.ClaimOp.claimA], [LiveSegmented.ClaimOp.claimB]]

/-- The scenario's branch endpoints are the live 2-clique. -/
theorem slotScenario_endpoint_clique :
    MenuTotality.Clique LiveSegmented.atMostOne
      (slotScenario.paths.map (Cost.run LiveSegmented.claimStep slotScenario.root)) := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
  intro b hb
  have hb' : b = LiveSegmented.sB := by simpa [slotScenario] using hb
  subst hb'
  exact (by decide : Clashes LiveSegmented.atMostOne LiveSegmented.sA LiveSegmented.sB)

/-- The two-domain live seam, as a strategy for the scenario. It is **not** a
global seam (`LiveSegmented.witness_one_latticeOnly_clash`), so it is available
only because `ForkGrade.LiveStrategy` is pool-relative — the same relativisation
`LiveSegmented` §4 prices at one coordination domain. -/
def slotStrategy : ForkGrade.LiveStrategy LiveSegmented.atMostOne LiveSegmented.claimStep
    slotScenario (Fin 2) :=
  ForkGrade.LiveStrategy.ofSegmentedOn
    (σ := LiveSegmented.sigmaLive)
    (segmentedOn_iff_properColoring.mpr ⟨by decide, by decide⟩)

/-- The admissible space containing it. -/
def slotSpace : Admissible (ForkGrade.LiveStrategy LiveSegmented.atMostOne
    LiveSegmented.claimStep slotScenario (Fin 2)) where
  head := slotStrategy
  rest := []

/-- **⚑ Floor and achievement meet, at the live clique number.** The live
2-clique charges the scenario `2 - 1 = 1` under **every** live strategy, and the
two-domain seam pays exactly `1`. So `1` is not a bound on this session's
coordination count — it **is** the count, and the number it came from is the
clique number of the live clash graph. -/
theorem slotScenario_floor_is_one :
    slotScenario.paths.length - 1 ≤ ForkGrade.liveOptimum slotSpace
    ∧ ForkGrade.liveOptimum slotSpace = 1 :=
  ⟨live_clique_forces_scenario_floor slotScenario_endpoint_clique slotSpace, by decide⟩

/-! ## §5. Stability adds a constraint colouring cannot see — and cliques see it
anyway.

The objection to reading `Width` as a chromatic number is real and is the tree's
own: a seam is a proper colouring **plus** fiber stability
(`LiveSegmented.liveSegmented_iff_liveProperColoring`,
`SeamColoring.segmentedOn_iff_properColoring`), and
`LiveSegmented.liveColoring_alone_does_not_segment` proves the second conjunct is
not implied by the first. Stability says: two legal states in one fiber have
their join in that fiber, so **every colour class is closed under the joins of
its own members**. That is not a graph condition, and it can forbid a colouring
the graph permits — an independent set `{x, y, w}` whose members' joins leave it
cannot be monochromatic.

This section answers whether that hides a floor the clique number cannot see, for
the first case where it bites: three states with pairwise-legal joins whose triple
join is illegal. The answer is **no** — that configuration forces a genuine
triangle among the three pairwise joins, so the clique number already reports 3.

⟨UNDONE⟩ The same argument works for `k` states with all `(k-1)`-wise joins legal
and the `k`-wise join illegal: the `k` leave-one-out joins are pairwise distinct
(two equal ones would make the full join legal) and pairwise clash (their join is
the full join). That generalisation is **not proved here** — it needs joins over
sublists and the erase-two-indices bookkeeping — and no numeric separation of
`Width` from the chromatic number is exhibited either way. -/

private theorem merge_self_left {S : Type w} [MergeState S] (x y : S) :
    x ⊔ (x ⊔ y) = x ⊔ y := by
  rw [← merge_assoc, merge_idem]

private theorem merge_absorb_left {S : Type w} [MergeState S] (x y : S) :
    (x ⊔ y) ⊔ x = x ⊔ y := by
  rw [merge_comm (x ⊔ y) x, merge_self_left]

private theorem merge_absorb_right {S : Type w} [MergeState S] (x y : S) :
    (x ⊔ y) ⊔ y = x ⊔ y := by
  rw [merge_assoc, merge_idem]

private theorem join_xy_xz {S : Type w} [MergeState S] (x y z : S) :
    (x ⊔ y) ⊔ (x ⊔ z) = (x ⊔ y) ⊔ z := by
  rw [← merge_assoc, merge_absorb_left]

private theorem join_xy_yz {S : Type w} [MergeState S] (x y z : S) :
    (x ⊔ y) ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z := by
  rw [← merge_assoc, merge_absorb_right]

private theorem join_xz_yz {S : Type w} [MergeState S] (x y z : S) :
    (x ⊔ z) ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z := by
  rw [← merge_assoc, merge_assoc x z y, merge_comm z y, ← merge_assoc,
    merge_absorb_right]

/-- **⚑ A three-way obstruction is a triangle.** If `x`, `y`, `z` are legal, all
three pairwise joins are legal, and the triple join is not, then the three
pairwise joins pairwise clash — a 3-clique. Each pair of them joins to `x ⊔ y ⊔ z`
by commutativity, associativity and idempotence alone, and the clique's own
`MenuTotality.clique_nodup` then says the three are distinct.

Read as the answer to §5's question: the extra constraint fiber stability places
on a colour class — closure under its members' joins — cannot, in this case,
produce a coordination floor the clique number misses, because the very states
that witness the constraint are a clique. -/
theorem triple_clash_forces_triangle {S : Type w} [MergeState S] {I : Invariant S}
    {x y z : S} (hxy : I (x ⊔ y)) (hxz : I (x ⊔ z)) (hyz : I (y ⊔ z))
    (hbad : ¬ I ((x ⊔ y) ⊔ z)) :
    MenuTotality.Clique I [x ⊔ y, x ⊔ z, y ⊔ z] := by
  refine List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil))
  · intro b hb
    have hb' : b = x ⊔ z ∨ b = y ⊔ z := by simpa using hb
    rcases hb' with rfl | rfl
    · exact ⟨hxy, hxz, by rw [join_xy_xz]; exact hbad⟩
    · exact ⟨hxy, hyz, by rw [join_xy_yz]; exact hbad⟩
  · intro b hb
    have hb' : b = y ⊔ z := by simpa using hb
    subst hb'
    exact ⟨hxz, hyz, by rw [join_xz_yz]; exact hbad⟩

/-- **…hence three coordination domains, by §1.** The three-way obstruction is
charged to the width through the clique bound, with no appeal to stability in the
bound itself. -/
theorem triple_clash_forces_three_domains {S : Type w} [MergeState S] {I : Invariant S}
    {x y z : S} {n : Nat} (hxy : I (x ⊔ y)) (hxz : I (x ⊔ z)) (hyz : I (y ⊔ z))
    (hbad : ¬ I ((x ⊔ y) ⊔ z)) (h : LiveSegmented.GlobalWidth I n) : 3 ≤ n := by
  have hcl := clique_forces_global_width (triple_clash_forces_triangle hxy hxz hyz hbad) h
  simpa using hcl

/-! ### §5.1 The hypotheses are satisfiable — and the obstruction really is 3-wise

A floor nothing can satisfy is not a floor. The slot carrier's *sibling* ceiling
— **at most two** of the three slots — realises §5's hypotheses exactly: the three
single claims have pairwise-legal joins and an illegal triple join. -/

/-- At most two of the three slots are claimed. The uniqueness ceiling
`LiveSegmented.atMostOne` weakened by one. -/
def atMostTwoB (s : LiveSegmented.Slots) : Bool := !(s.a && s.b && s.c)

/-- …as an invariant on the same carrier. -/
def atMostTwo : Invariant LiveSegmented.Slots := fun s => atMostTwoB s = true

instance : DecidablePred atMostTwo :=
  fun s => inferInstanceAs (Decidable (atMostTwoB s = true))

/-- ⚠ **The three-way obstruction is invisible to the pairwise clash graph on
its own generators.** `sA`, `sB` and `sC` are legal, and **no two of them
clash** — every pairwise join is a legal two-slot state. Only the triple join is
illegal. -/
theorem atMostTwo_generators_do_not_clash :
    atMostTwo LiveSegmented.sA ∧ atMostTwo LiveSegmented.sB ∧ atMostTwo LiveSegmented.sC
    ∧ ¬ Clashes atMostTwo LiveSegmented.sA LiveSegmented.sB
    ∧ ¬ Clashes atMostTwo LiveSegmented.sA LiveSegmented.sC
    ∧ ¬ Clashes atMostTwo LiveSegmented.sB LiveSegmented.sC
    ∧ ¬ atMostTwo ((LiveSegmented.sA ⊔ LiveSegmented.sB) ⊔ LiveSegmented.sC) := by
  decide

/-- **⚑ …and the clique bound sees it anyway, one level up.** The three pairwise
joins form a triangle, so every seam for "at most two slots" needs three
coordination domains — a number no edge among `sA`, `sB`, `sC` could have
produced. This is `triple_clash_forces_triangle` on a carrier, and it is the
witness that §5's hypotheses are satisfiable rather than vacuously quantified. -/
theorem atMostTwo_triangle_of_the_triple_clash :
    MenuTotality.Clique atMostTwo
      [LiveSegmented.sA ⊔ LiveSegmented.sB, LiveSegmented.sA ⊔ LiveSegmented.sC,
       LiveSegmented.sB ⊔ LiveSegmented.sC] :=
  triple_clash_forces_triangle (I := atMostTwo) (by decide) (by decide) (by decide)
    (by decide)

/-- The three-domain seam for "at most two slots": claim `b` without `a` is its
own domain, claim `c` is another, everything else rides with the empty state. -/
def sigmaTwo (s : LiveSegmented.Slots) : Fin 3 :=
  if s.b && !s.a then 1 else if s.c then 2 else 0

theorem sigmaTwo_segmented : SegmentedIConfluent sigmaTwo atMostTwo := by
  intro x y hσ hx hy
  obtain ⟨xa, xb, xc⟩ := x
  obtain ⟨ya, yb, yc⟩ := y
  revert hσ hx hy
  cases xa <;> cases xb <;> cases xc <;> cases ya <;> cases yb <;> cases yc <;> decide

/-- **⚑ The optimum for "at most two slots" is three, and the certificate is a
clique of joins.** The floor is `triple_clash_forces_three_domains`; the
achievement is `sigmaTwo`. Neither half mentions an edge between the three
single claims, because there is none
(`atMostTwo_generators_do_not_clash`) — the whole number comes from a
three-way obstruction that the clique bound reads off the pairwise joins. -/
theorem atMostTwo_least_width :
    LiveSegmented.LeastSuch (LiveSegmented.GlobalWidth atMostTwo) 3 :=
  least_globalWidth_of_clique_and_seam atMostTwo_triangle_of_the_triple_clash rfl
    ⟨sigmaTwo, sigmaTwo_segmented⟩

/-! ### §5.2 The achievable crossing gap — live `0`, global exactly `1`

The three-way obstruction also closes the crossing question left open by
`LiveSegmented` and `ForkGrade`. Run three one-operation branches from the empty
state, one per slot. Every pair of scenario worlds merges legally under
`atMostTwo`, so there is no live clash and the constant live seam is valid at
cost zero. But a **global** seam at cost zero would paint all three branch
endpoints with the root's colour. Global fiber stability then closes `sA` with
`sB`, keeps their join in that fiber, and closes the result with `sC` — deriving
legality of the forbidden triple claim.

This is not merely a lower bound. `sigmaTwoOneCross` is globally segmented and
charges exactly the C branch, so the global optimum is attained at one. -/

/-- Three single-claim branches from the empty slot state. -/
def atMostTwoScenario :
    ForkGrade.Scenario LiveSegmented.Slots ClaimOp3 where
  root := LiveSegmented.sO
  paths := [[ClaimOp3.claimA], [ClaimOp3.claimB], [ClaimOp3.claimC]]

/-- The scenario contains exactly the empty state and the three generators. -/
theorem atMostTwoScenario_worlds :
    atMostTwoScenario.worlds claim3Step =
      [LiveSegmented.sO, LiveSegmented.sA, LiveSegmented.sB, LiveSegmented.sC] := rfl

/-- **Satisfiability of the live side.** Every two scenario worlds merge to a
state with at most two claims, so its live clash graph is empty. -/
theorem atMostTwoScenario_no_live_clash :
    ¬ ForkGrade.LiveClash atMostTwo claim3Step atMostTwoScenario := by
  decide

/-- The honest constant live strategy, over the same three colours available to
the global witness below. Its validity is carried by the no-live-clash proof. -/
def atMostTwoZeroStrategy :
    ForkGrade.LiveStrategy atMostTwo claim3Step atMostTwoScenario (Fin 3) :=
  ForkGrade.constLiveStrategy 0 atMostTwoScenario_no_live_clash

/-- The live strategy pays zero on all three branches. -/
theorem atMostTwoZeroStrategy_cost :
    ForkGrade.liveCost atMostTwoZeroStrategy.seam claim3Step atMostTwoScenario = 0 :=
  ForkGrade.constLiveStrategy_free 0 atMostTwoScenario_no_live_clash

/-- A global seam that keeps the empty, A, B, and AB states together, separates
C/AC, and gives BC the third colour. On the scenario it crosses only to C. -/
def sigmaTwoOneCross (s : LiveSegmented.Slots) : Fin 3 :=
  if s.c then if s.b && !s.a then 2 else 1 else 0

/-- The one-crossing seam is genuinely globally segmented; the achievement is
not obtained by weakening the certificate. -/
theorem sigmaTwoOneCross_segmented : SegmentedIConfluent sigmaTwoOneCross atMostTwo := by
  intro x y hσ hx hy
  obtain ⟨xa, xb, xc⟩ := x
  obtain ⟨ya, yb, yc⟩ := y
  revert hσ hx hy
  cases xa <;> cases xb <;> cases xc <;> cases ya <;> cases yb <;> cases yc <;> decide

/-- The global witness attains the floor: only the C branch changes fiber. -/
theorem sigmaTwoOneCross_cost :
    ForkGrade.liveCost sigmaTwoOneCross claim3Step atMostTwoScenario = 1 := by
  decide

/-- **Every global seam crosses.** Zero cost would root-colour `sA`, `sB`, and
`sC`; `ForkGrade.global_triple_obstruction_cost_positive` then uses global fiber
stability twice to derive legality of their illegal triple join. -/
theorem atMostTwo_every_global_seam_costs_one_or_more
    {Seg : Type z} [DecidableEq Seg] (σ : LiveSegmented.Slots → Seg)
    (hseg : SegmentedIConfluent σ atMostTwo) :
    1 ≤ ForkGrade.liveCost σ claim3Step atMostTwoScenario := by
  apply ForkGrade.global_triple_obstruction_cost_positive
    (I := atMostTwo) (step := claim3Step) (sc := atMostTwoScenario) (σ := σ)
    (x := LiveSegmented.sA) (y := LiveSegmented.sB) (z := LiveSegmented.sC)
  · rw [atMostTwoScenario_worlds]
    simp
  · rw [atMostTwoScenario_worlds]
    simp
  · rw [atMostTwoScenario_worlds]
    simp
  · decide
  · decide
  · decide
  · decide
  · exact hseg

/-- **The concrete live/global crossing separation.** On one scenario, in one
crossing currency and even with the same three-element segment codomain, a live
strategy achieves `0`; every globally valid seam costs at least `1`; and a
globally valid seam achieves `1`. Thus the optima differ exactly, not merely by
the absence of the constant seam. -/
theorem atMostTwo_live_global_crossing_gap :
    ForkGrade.liveCost atMostTwoZeroStrategy.seam claim3Step atMostTwoScenario = 0
    ∧ (∀ σ : LiveSegmented.Slots → Fin 3,
        SegmentedIConfluent σ atMostTwo →
          1 ≤ ForkGrade.liveCost σ claim3Step atMostTwoScenario)
    ∧ SegmentedIConfluent sigmaTwoOneCross atMostTwo
    ∧ ForkGrade.liveCost sigmaTwoOneCross claim3Step atMostTwoScenario = 1 :=
  ⟨atMostTwoZeroStrategy_cost, atMostTwo_every_global_seam_costs_one_or_more,
   sigmaTwoOneCross_segmented, sigmaTwoOneCross_cost⟩

/-! ## §6. Two incomparable floors — and therefore two things to report.

`MenuTotality.the_clique_floor_is_invisible_to_the_block_calculus` proves one
direction: on the replica family the block calculus reports `0` (adding elements
is an inflation, so `Cost.clashBlocks_nil_of_inflationary` empties every clash
decomposition) while the clique reports `k-1`.

The other direction is here, and it is not symmetric prose: the clique floor's
number is `ws.length - 1`, **one less than the number of concurrent streams**, so
on a workload of one stream it is `0` no matter how large a clique the carrier
has. `Cost`'s budget chain is such a workload — one stream, three successive
clash blocks, block floor `3`, and `3` is attained. Neither calculus dominates,
so a checker that runs one of them is not conservative; it is wrong. -/

/-- The clique floor's number for a single-stream workload. Nothing about the
carrier can raise it: `clique_forces_joint_crossings` bounds `ws.length` by
`jointCost + 1`, and a one-stream `ws` makes that `0 ≤ jointCost`.

⚠ The statement is `rfl` and carries no content by itself; it is named so that
the `0` in `the_two_floors_are_incomparable` is the clique calculus's own number
rather than a claim in prose. -/
theorem single_stream_clique_floor_is_zero {Op : Type v} (w : List Op) :
    ([w] : List (List Op)).length - 1 = 0 := rfl

/-- **⚑ The two floors are incomparable, and both are attained where they are
positive.**

  * First conjunct — `MenuTotality`'s replica family: **every** clash
    decomposition is empty (block floor `0`), and every valid seam pays at least
    `k-1` jointly (clique floor `k-1`).
  * Second conjunct — `Cost`'s budget chain: every valid seam pays at least `3`
    on the single stream `budgetW` (block floor `3`), the allocation-share seam
    pays exactly `3`, and the clique floor for a one-stream workload is `0`.

So each calculus reports `0` on the workload where the other reports a positive
number. A menu that quotes one of them quotes an undercount. -/
theorem the_two_floors_are_incomparable (k : Nat) :
    ((∀ bs : List (List Nat),
        Cost.ClashBlocks MenuTotality.atMostOne MenuTotality.addStep
          MenuTotality.emptySet bs → bs.length = 0)
      ∧ ∀ {Seg : Type} [DecidableEq Seg] (σ : GSet Nat → Seg),
          SegmentedIConfluent σ MenuTotality.atMostOne →
          k - 1 ≤ jointCost σ MenuTotality.addStep MenuTotality.emptySet
            (MenuTotality.replicaStreams k))
    ∧ ((∀ {Seg : Type} [DecidableEq Seg] (σ : QuotaState → Seg),
          SegmentedIConfluent σ (BudgetInv 10) →
          3 ≤ Cost.crossings σ (Cost.reallocStep 10) Cost.budgetStart Cost.budgetW)
      ∧ Cost.crossings (fun s : QuotaState => s.1 true) (Cost.reallocStep 10)
          Cost.budgetStart Cost.budgetW = 3
      ∧ ([Cost.budgetW] : List (List Nat)).length - 1 = 0) :=
  ⟨MenuTotality.the_clique_floor_is_invisible_to_the_block_calculus k,
   Cost.budget_cost_is_three.{0}.1, Cost.budget_cost_is_three.{0}.2, rfl⟩

/-! ## §7. The chain, collected.

`live clique → live width → live scenario floor`, on one carrier, with the global
column beside it and the transport hypothesis named. -/

/-- **⚑ THE ONE CHAIN.** Read the conjuncts in order:

  1. the live clash graph of the slot protocol has a 2-clique, `[sA, sB]`;
  2. and no 3-clique, from any base — `sC` forks with nothing;
  3. the global clash graph has a 3-clique, `[sA, sB, sC]`;
  4. so the live optimum is 2, certified by the clique against `sigmaLive`;
  5. and the global optimum is 3, certified by the clique against `sigmaGlobal`;
  6. and the two-branch session's floor is `2 - 1 = 1`, charged by the same live
     clique to every live strategy;
  7. and that `1` is paid, by the two-domain seam.

Every number in the chain is the live clique number, or one less than it. The
global column differs in exactly the vertex the protocol cannot reach, and
`no_three_stream_clique` says the workload the global column would have priced
does not exist. -/
theorem the_live_clique_number_determines_both :
    LiveClique LiveSegmented.slotProtocol LiveSegmented.atMostOne LiveSegmented.sO
        [LiveSegmented.sA, LiveSegmented.sB]
    ∧ (∀ base x y z : LiveSegmented.Slots,
        ¬ LiveClique LiveSegmented.slotProtocol LiveSegmented.atMostOne base [x, y, z])
    ∧ MenuTotality.Clique LiveSegmented.atMostOne
        [LiveSegmented.sA, LiveSegmented.sB, LiveSegmented.sC]
    ∧ LiveSegmented.LeastSuch
        (LiveSegmented.LiveWidth LiveSegmented.slotProtocol LiveSegmented.atMostOne) 2
    ∧ LiveSegmented.LeastSuch (LiveSegmented.GlobalWidth LiveSegmented.atMostOne) 3
    ∧ slotScenario.paths.length - 1 ≤ ForkGrade.liveOptimum slotSpace
    ∧ ForkGrade.liveOptimum slotSpace = 1 :=
  ⟨slot_live_clique_two, fun base x y z h => no_live_triangle base x y z h,
   slot_global_clique_three, slot_live_least_width, slot_global_least_width,
   slotScenario_floor_is_one.1, slotScenario_floor_is_one.2⟩

end Uwueave.CliqueLive
