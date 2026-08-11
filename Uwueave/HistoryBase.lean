/-
# Uwueave.HistoryBase — a base decision certified by the HISTORY, not by the states.

## The defect this file repairs

`MergeModel.lean` §9 defines `BaseDecision = selected | ambiguous | unavailable`
and a validity predicate whose whole design claim is that **`unavailable` must
refute the existence of any base**. `Histories.lean` then proved, three ways,
that `BaseDecision.Valid` is a condition on **states** and certifies nothing
about a **history**:

  * `dag_ancestry_is_not_run_reachable` — a DAG parent edge whose two states are
    not related by any local run, so the §4.1 bridge dies;
  * `state_validity_is_not_dag_ancestry` — `selected 3` is `Valid` for the pair
    `(3, 3)` while **no** common ancestor of those two versions carries `3`;
  * `dag_absence_does_not_license_unavailable` — a version graph with no common
    ancestor at all whose `unavailable` is nonetheless **invalid**, because that
    obligation is about states and a state always op-reaches itself.

`Histories.lean` could not repair it: `MergeModel.lean` was not its file, and
neither is it ours. The repair here is the one the greenfield rule asks for —
define the stronger notion **beside** the weaker one and relate them by theorem,
so that exactly what the state level fails to see is a proved statement rather
than a remark. Nothing in `MergeModel.lean`, `Histories.lean` or
`WorldFuture.lean` is edited.

## The four verdicts, up front

  * **§2–§3. `ValidInHistory` — a base decision certified by a version DAG.**
    Its `selected` demands a *lowest* common base (so at most one version is
    ever selectable, `selected_unique`); its `ambiguous` demands two distinct
    *maximal* ones (so `ambiguous_excludes_lowest` applies); its `unavailable`
    refutes the existence of a common ancestor **version**. It transports into
    `MergeModel.BaseDecision.Valid` under `RunRealized` (`selected_transports`,
    `ambiguous_transports`) and it excludes all three witnesses:

      - it survives where witness 1 kills the bridge — `ValidInHistory` never
        mentions `Reachable`, so it certifies the criss-cross pair that
        `ccHistory_not_runRealized` puts out of the state level's reach;
      - it refuses witness 2 outright: **no** version of the criss-cross is
        selectable for `mergeL`/`mergeR` (`no_version_is_selectable_here`),
        while `the_only_valid_state_decision` shows the state level's *unique*
        valid answer there is `selected 3` — a base no version carries;
      - it accepts witness 3's situation, which the state level is *prohibited*
        from accepting: `state_unavailable_refuted_by_a_run` proves the
        state-level `unavailable` obligation is defeated by any run relating the
        two replicas, and `state_unavailable_never_at_equal_states` is the
        equality case Histories exhibited.

    And the two notions are independent in the other direction too:
    `state_unavailable_fires_where_the_dag_hands_a_base` exhibits a pair whose
    versions have a **direct common parent** and whose states admit no common
    base at all.

  * **§4. A coherent history is rooted — and `unavailable` is a cross-history
    answer.** `coherent_reaches_from_root` is the graph half of
    `History.Coherent.sound`, and it drops all four of that theorem's semantic
    hypotheses (`LocallySafe`, `AncestralConfluentFrom`, `MergeClosedFrom`,
    `I ρ`). Its corollary: inside one coherent history, `ValidInHistory`'s
    `unavailable` is **never** satisfiable. The third case is not a case a
    merge-base procedure hits while walking a history; it is the answer to
    "these two versions are not from the same history", and `twoHistory` — the
    witness — is provably not coherent.

  * **§5. The closure condition, transported: a NO and a YES.** `MergeClosedFrom`
    is *not* a DAG condition: it quantifies over triples of states that need not
    appear in the history at all, and `runRealized_does_not_imply_mergeClosed`
    exhibits a two-node coherent history, every edge a genuine run, over a merge
    that is not closed. But the **soundness** it was introduced to buy *is*
    obtainable edge-locally: `coherent_sound_of_runRealized` proves every version
    of a run-realized coherent history legal from `LocallySafe` and a legal root
    alone — no merge law, no closure, no confluence hypothesis. The two
    conditions are logically independent, and `reset_mergeClosed` beside
    `resetHistory_not_runRealized` is the other direction (a "roll back on
    conflict" merge, closed from the root, whose merge node is not reachable from
    either parent).

  * **§7. The price of ambiguity, stated.** On the pair the criss-cross actually
    presents, `the_only_valid_state_decision` proves the state-level model has
    **exactly one** valid answer and it is `selected 3` — so `ambiguous` is
    unstateable there (`no_state_ambiguous_decision_here`), and the history level
    is the only index at which the honest answer is available. That matters
    because `decidedMerge`'s `ambiguous` branch **does not use a base**: routing
    the criss-cross to `ambiguous` lands on `3` under a ceiling of `4`, while the
    two legitimate base choices land on `5` and `4` (`Histories.base_accident_
    decides_the_invariant`). ⚠ And the sharpest form:
    `counter_decision_iconfluentIn` proves `MergeModel.IConfluentIn` **holds** for
    the counter's decision model — the model certifies the very merge whose
    history has an illegal node — because its `validContext` refuses, on
    reachability grounds, the merge that actually happens.

## §6. Merge bases in a world — what the DAG bought there

`WorldFuture.lean` names six components of codex's separation and drops two,
one of them "known merge bases", explicitly *for want of a history DAG*.
`Histories.lean` supplies one, so §6 defines `BasedWorld`: a version DAG whose
versions carry `WorldFuture.World`s. Three things follow, and the third is the
prize:

  * the dropped component becomes definable — `MergeBases B x y` is
    `Histories.BaseSelection B.dag x y`, and it is inhabited at a real pair
    (`wMergeBase`);
  * a delivery future indexed by history position, and the world-carrier
    analogue of `dag_ancestry_is_not_run_reachable`:
    `dag_ancestry_is_not_delivery` exhibits two DAG siblings with the **same
    materialized state** that no delivery future links in either direction,
    because their pools differ;
  * ⚠ **a repair of `no_sound_state_cert_accepts_openW`.** That theorem says no
    sound state-indexed exactness certificate may accept `openW` — not even the
    one a replica correctly verified at `wQuiesced`. Given a base to name, the
    same state-keyed certificate becomes sound: `the_base_scope_repairs_the_
    state_keyed_certificate` proves it sound scoped to the base it was computed
    against, and **unsound scoped to the history root**. The scope is a DAG fact,
    so it is checkable from the graph — and it is not a free pass.

## Non-claims

⟨TERMINAL⟩ = a theorem of this model; ⟨UNDONE⟩ = work wearing a caveat's clothes.

  * ⟨TERMINAL⟩ **`ValidInHistory` is not a procedure.** It is what a merge-base
    procedure's output must *prove*, exactly as `Histories.BaseSelection` is.
    Nothing here computes a base from a DAG; `Histories.lean`'s own ⟨UNDONE⟩ on
    that point stands unchanged.
  * ⟨TERMINAL⟩ **The transport needs `RunRealized`, and merges destroy it.**
    §2's two transport theorems carry a `RunRealized` hypothesis and
    `ccHistory_not_runRealized` says no merge-bearing history that leaves the
    op-reachable region has it. That is not a defect of the transport: it is the
    diagnosis. Where the bridge is unavailable the history-level notion still
    certifies, which is the whole point of defining it.
  * ⟨UNDONE⟩ **No convergence, still.** Nothing here says two replicas agree.
    `selected_unique` narrows the licence — the state level licenses the two
    bases `Histories.swap_never_converges` builds its eternal two-cycle from,
    and the history level licenses at most one of them
    (`the_two_cycle_needs_two_bases_the_history_licenses_one`) — but "at most one
    valid base" is not a proof that a run converges, and no such proof is here.
  * ⟨UNDONE⟩ **The version index buys scoping, not separating power.** §6's
    `VersionCert` is strictly a *name* for a world: `versionCertSound_of_
    worldCertSound` is one line and there is no theorem that a version index
    separates two worlds a `WorldFuture.WorldCert` cannot. What it buys is a
    **base to scope to**, which a bare world has no room for.
  * ⟨UNDONE⟩ **`Type 0` only**, inherited from `MergeModel.BaseDecision` and
    `Histories`. The version type, the state type and the world's value type are
    all `Type`.
  * ⟨UNDONE⟩ **Two witnesses, not a classification.** §7's pairing — ambiguity is
    expressible at the state level in the lock, where it costs nothing, and
    inexpressible in the counter, where it decides the invariant — is two
    histories. No theorem here says that is the general pattern.

Literature: as `Histories.lean` (Kaki et al., OOPSLA 2019; Sal 2026 §2; Bailis
et al., VLDB 2015) and `WorldFuture.lean` (Power–Koutris–Hellerstein,
arXiv:2502.00222; Brun et al., ITP 2021).
-/
import Uwueave.Histories
import Uwueave.WorldFuture

namespace Uwueave.HistoryBase

open Uwueave Uwueave.Ancestral Uwueave.Necessity Uwueave.Histories

/-! ## §0. Two graph lemmas and a budget generalization

Everything below needs to say "this version is a leaf" and "a replica can spend
its way from here to there", and neither is available at the generality the file
needs. `Histories.lean` proves the second only at budget `2`. -/

/-- **An ancestry path starts with an edge.** The working form of "this version
is a leaf": if nothing leaves `a`, nothing is downstream of it. -/
theorem ancestry_has_first_edge {V : Type} {D : VersionDag V} {a b : V}
    (h : Ancestry D a b) : ∃ c, D.parent a c = true := by
  induction h with
  | direct e => exact ⟨_, e⟩
  | extend _ _ ih => exact ih

/-- **A leaf reaches only itself.** -/
theorem reaches_of_leaf {V : Type} {D : VersionDag V} {a b : V}
    (hleaf : ∀ c, D.parent a c = false) (h : Reaches D a b) : a = b := by
  rcases h with rfl | ha
  · rfl
  · obtain ⟨c, hc⟩ := ancestry_has_first_edge ha
    exact Bool.noConfusion (hc.symm.trans (hleaf c))

/-- **What a replica can reach under budget `B`**, at every budget:
`Histories.spend2_run` with the `2` released. -/
theorem spend_run (B : Nat) : ∀ (ops : List Unit) (l x : Nat),
    run (spendOps B).impl l ops = some x → x = l ∨ (l ≤ x ∧ x ≤ B) := by
  intro ops
  induction ops with
  | nil => intro l x h; exact Or.inl (Option.some.inj h).symm
  | cons op ops ih =>
    intro l x h
    by_cases hl : l + 1 ≤ B
    · have htry : (spendOps B).impl.tryApply op l = some (l + 1) := by
        rw [spend_tryApply]; exact if_pos hl
      rw [run_cons_some _ _ _ _ htry] at h
      rcases ih (l + 1) x h with he | ⟨h1, h2⟩
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, h2⟩
    · have htry : (spendOps B).impl.tryApply op l = none := by
        rw [spend_tryApply]; exact if_neg hl
      rw [run_cons_none _ _ _ _ htry] at h
      exact absurd h (by simp)

/-- The same, in `Reachable` form. -/
theorem spend_reachable (B : Nat) {l x : Nat} (h : Reachable (spendOps B).impl l x) :
    x = l ∨ (l ≤ x ∧ x ≤ B) := by
  obtain ⟨ops, hr⟩ := h
  exact spend_run B ops l x hr

/-- Spending `n` units, when the budget allows. -/
theorem spend_reach_add (B : Nat) : ∀ (n l : Nat), l + n ≤ B →
    Reachable (spendOps B).impl l (l + n) := by
  intro n
  induction n with
  | zero => intro l _; exact Reachable.refl _ _
  | succ n ih =>
    intro l h
    have htry : (spendOps B).impl.tryApply () l = some (l + 1) := by
      rw [spend_tryApply]; exact if_pos (by omega)
    have hstep : Reachable (spendOps B).impl l (l + 1) := by
      refine ⟨[()], ?_⟩
      show run (spendOps B).impl l [()] = some (l + 1)
      rw [run_cons_some _ _ _ _ htry]
      rfl
    have hcomp := Reachable.trans hstep (ih (l + 1) (by omega))
    rw [show l + 1 + n = l + (n + 1) from by omega] at hcomp
    exact hcomp

/-- **The converse of `spend_reachable`**: everything between here and the budget
is reachable. -/
theorem spend_reach (B : Nat) {l x : Nat} (h1 : l ≤ x) (h2 : x ≤ B) :
    Reachable (spendOps B).impl l x := by
  have h := spend_reach_add B (x - l) l (by omega)
  rw [show l + (x - l) = x from by omega] at h
  exact h

/-- Spending never breaks the budget — `LocallySafe` at every `B`. -/
theorem spend_locally_safe (B : Nat) :
    LocallySafe (spendOps B).impl (fun n => n ≤ B) := by
  intro op s s' h _
  rw [spend_tryApply] at h
  by_cases hb : s + 1 ≤ B
  · rw [if_pos hb] at h
    have he : s + 1 = s' := Option.some.inj h
    rw [← he]; exact hb
  · rw [if_neg hb] at h
    exact absurd h (by simp)

/-! ## §1. What the state-level condition cannot see

Three general facts about `MergeModel.BaseDecision.Valid`, each of which is a
witness of `Histories.lean` promoted to a theorem about every carrier. They are
the reason a state-indexed base decision cannot certify a history, and they are
stated here before the repair so that the repair can be measured against them. -/

/-- ⚠ **The state-level `unavailable` obligation is refuted by any run relating
the two replicas.** `MergeModel`'s §9 says `unavailable` "must **refute** the
existence of any" base; at the state level that refutation is defeated by the
run `x ⟶ y` itself, because `x` is then a common ancestor of the pair.

`Histories.dag_absence_does_not_license_unavailable` is the instance of this at
`x = y`; here it is the general fact. -/
theorem state_unavailable_refuted_by_a_run {S Op : Type} {impl : Impl S Op} {x y : S}
    (h : Reachable impl x y) :
    ¬ (MergeModel.BaseDecision.unavailable (S := S)).Valid impl x y :=
  fun hu => hu ⟨x, Reachable.refl _ _, h⟩

/-- **…so it is never valid for two replicas holding the same state**, whatever
the implementation and whatever the version graph says. -/
theorem state_unavailable_never_at_equal_states {S Op : Type} (impl : Impl S Op) (s : S) :
    ¬ (MergeModel.BaseDecision.unavailable (S := S)).Valid impl s s :=
  state_unavailable_refuted_by_a_run (Reachable.refl _ _)

/-- ⚠ **State-level ambiguity cannot record two bases that agree as states.**
`BaseDecision.ambiguous` carries `b₁ ≠ b₂` *as states*, so two distinct maximal
common **versions** with a common state are inexpressible — and §7 shows that is
exactly the criss-cross's situation. -/
theorem state_ambiguous_invalid_of_equal_bases {S Op : Type} {impl : Impl S Op}
    {b₁ b₂ x y : S} (h : b₁ = b₂) :
    ¬ (MergeModel.BaseDecision.ambiguous b₁ b₂).Valid impl x y :=
  fun hv => hv.2.2 h

/-! ## §2. `ValidInHistory` — the decision, certified by the version DAG

The same three-valued shape, re-obligated over versions. Three differences from
`MergeModel.BaseDecision.Valid`, and each is one of the three witnesses:

  * `selected` demands a **lowest** common base, not merely a common ancestor,
    so `Histories.lowestCommonBase_unique` applies and at most one version is
    ever selectable for a pair;
  * `ambiguous` demands two **maximal** common bases, so
    `Histories.ambiguous_excludes_lowest` makes it a *proof* that no `selected`
    answer exists — the ⟨UNDONE⟩ `MergeModel` §9's own docstring records;
  * `unavailable` refutes the existence of a common ancestor **version**, which
    is the obligation §9 says it wants and the state level cannot carry. -/

/-- **A base decision certified by the history.** The decision ranges over
*versions*: `MergeModel.BaseDecision V`, the same type at a different index, so
nothing in `MergeModel.lean` moves. -/
def ValidInHistory {V S Op : Type} (H : History V S Op) (x y : V) :
    MergeModel.BaseDecision V → Prop
  | .selected b => LowestCommonBase H.dag x y b
  | .ambiguous b₁ b₂ =>
      MaximalCommonBase H.dag x y b₁ ∧ MaximalCommonBase H.dag x y b₂ ∧ b₁ ≠ b₂
  | .unavailable => ∀ b, ¬ CommonAncestor H.dag x y b

/-- **At most one version is selectable for a pair.** The state-level condition
has no such theorem — `Histories.lock_two_valid_bases` exhibits two states that
are both `Valid` as `selected` for one pair *and whose merges disagree*. -/
theorem selected_unique {V S Op : Type} {H : History V S Op} {x y b₁ b₂ : V}
    (h₁ : ValidInHistory H x y (.selected b₁))
    (h₂ : ValidInHistory H x y (.selected b₂)) : b₁ = b₂ :=
  lowestCommonBase_unique h₁ h₂

/-- **`ambiguous` refutes `selected`, and `unavailable` refutes both** — the
exclusivity `MergeModel.BaseDecision` names as its design and can only obtain at
the version level, since `Histories.ambiguous_excludes_lowest` is a theorem about
a DAG. -/
theorem validInHistory_exclusive {V S Op : Type} {H : History V S Op} {x y : V} :
    (∀ b₁ b₂ b, ValidInHistory H x y (.ambiguous b₁ b₂) →
        ¬ ValidInHistory H x y (.selected b))
      ∧ (∀ b, ValidInHistory H x y .unavailable →
        ¬ ValidInHistory H x y (.selected b)) :=
  ⟨fun _ _ b ha hs => ambiguous_excludes_lowest ha.1 ha.2.1 ha.2.2 ⟨b, hs⟩,
   fun _ hno hs => hno _ hs.1⟩

/-- **All three cases are inhabited** — a case nothing can satisfy is a case a
reader trusts for nothing. `selected` is the criss-cross's fork point (the lowest
common base of its two branches), `ambiguous` its two maximal bases, and
`unavailable` the edgeless graph, whose refutation is genuine
(`Histories.two_no_common`).

⚠ Note *where* each lives: the first two inside one coherent history, the third
only across two — §4 proves that is not an accident of these witnesses. -/
theorem validInHistory_all_three_inhabited :
    ValidInHistory ccHistory .left .right (.selected .root)
      ∧ ValidInHistory ccHistory .mergeL .mergeR (.ambiguous .left .right)
      ∧ ValidInHistory (twoHistory (S := Nat) (Op := Unit) 0) .x .y .unavailable :=
  ⟨cc_root_lowest, ⟨cc_left_maximal, cc_right_maximal, by decide⟩, two_no_common⟩

/-- The image of a history-level decision at the state level: read each version's
state off the history. -/
def stateDecision {V S Op : Type} (H : History V S Op) :
    MergeModel.BaseDecision V → MergeModel.BaseDecision S
  | .selected b => .selected (H.state b)
  | .ambiguous b₁ b₂ => .ambiguous (H.state b₁) (H.state b₂)
  | .unavailable => .unavailable

/-! ### §2.1 The transport — and its exact boundary

`selected` and `ambiguous` transport into `MergeModel.BaseDecision.Valid` under
`RunRealized`; `ambiguous` needs one extra hypothesis and `unavailable` does not
transport at all. All three facts are theorems, and the last two are the shape
of the defect. -/

/-- **A history-selected base is state-valid** — in a run-realized history.
`Histories.selected_valid` does the work; what is new is that the *premise* is
now a lowest common base rather than an arbitrary common ancestor, so the answer
being transported is unique. -/
theorem selected_transports {V S Op : Type} {H : History V S Op} {impl : Impl S Op}
    (hrr : RunRealized H impl) {x y b : V}
    (h : ValidInHistory H x y (.selected b)) :
    (stateDecision H (.selected b)).Valid impl (H.state x) (H.state y) :=
  selected_valid hrr h.1

/-- **A history-ambiguous pair is state-valid** — in a run-realized history, and
*only if the two bases carry distinct states*. That hypothesis is not
bookkeeping: the next theorem shows the image is invalid without it. -/
theorem ambiguous_transports {V S Op : Type} {H : History V S Op} {impl : Impl S Op}
    (hrr : RunRealized H impl) {x y b₁ b₂ : V}
    (h : ValidInHistory H x y (.ambiguous b₁ b₂)) (hne : H.state b₁ ≠ H.state b₂) :
    (stateDecision H (.ambiguous b₁ b₂)).Valid impl (H.state x) (H.state y) :=
  ambiguous_valid hrr h.1 h.2.1 hne

/-- ⚠ **…and it does not transport when the two bases agree as states.** Genuine
version-level ambiguity whose bases happen to carry one state is not merely hard
to see at the state level — its image is **invalid** there, so a state-indexed
procedure reporting it would be reporting an illegitimate decision. -/
theorem ambiguous_does_not_transport {V S Op : Type} {H : History V S Op}
    (impl : Impl S Op) {x y b₁ b₂ : V} (hst : H.state b₁ = H.state b₂) :
    ¬ (stateDecision H (.ambiguous b₁ b₂)).Valid impl (H.state x) (H.state y) :=
  fun h => h.2.2 hst

/-- ⚠ **`unavailable` never transports when the two replicas agree as states** —
and by `state_unavailable_refuted_by_a_run`, not when any run relates them
either. This is `Histories.dag_absence_does_not_license_unavailable` stated as a
property of the transport rather than of one witness: the third case is provably
*not* the image of anything. -/
theorem unavailable_does_not_transport {V S Op : Type} {H : History V S Op}
    (impl : Impl S Op) {x y : V} (hst : H.state x = H.state y) :
    ¬ (stateDecision H (MergeModel.BaseDecision.unavailable (S := V))).Valid impl
      (H.state x) (H.state y) := by
  intro h
  refine h ⟨H.state x, Reachable.refl _ _, ?_⟩
  rw [← hst]
  exact Reachable.refl _ _

/-! ## §3. The three witnesses, excluded

`Histories.lean` exhibited three. Each is answered here by a theorem about
`ValidInHistory` on the very same objects. -/

/-! ### §3.1 Witness 1 — the bridge dies, and `ValidInHistory` does not

`dag_ancestry_is_not_run_reachable` says a DAG parent edge need not be a run, so
`ccHistory` is not `RunRealized` and every §4.1 bridge theorem is unavailable
there. `ValidInHistory` never mentions `Reachable`, so it certifies the pair
anyway — which is the precise sense in which it is the notion that survives a
merge. -/

/-- ⚠ **The history-level decision certifies where the state-level bridge cannot
reach.** `ccHistory` is not run-realized — its first merge left the op-reachable
region — and the two merge versions are nonetheless a certified `ambiguous` pair
of the version DAG. -/
theorem validInHistory_survives_the_broken_bridge :
    ValidInHistory ccHistory .mergeL .mergeR (.ambiguous .left .right)
      ∧ ¬ RunRealized ccHistory (spendOps 2).impl :=
  ⟨⟨cc_left_maximal, cc_right_maximal, by decide⟩, ccHistory_not_runRealized⟩

/-! ### §3.2 Witness 2 — the phantom base

`state_validity_is_not_dag_ancestry` exhibits `selected 3` as `Valid` for the
pair `(3, 3)` while no common ancestor of `mergeL`/`mergeR` carries `3`. Two
theorems answer it: the history level refuses **every** `selected` answer there,
and the state level's *only* valid answer is the phantom. -/

/-- **No version of the criss-cross is selectable for the two merge versions.**
Immediately from `Histories.cc_no_lowest`: two maximal common bases exclude a
lowest one, and `ValidInHistory`'s `selected` demands a lowest one. -/
theorem no_version_is_selectable_here (b : Ver) :
    ¬ ValidInHistory ccHistory .mergeL .mergeR (.selected b) :=
  fun h => cc_no_lowest ⟨b, h⟩

/-- ⚠ **The state level's only valid answer for that pair is a phantom.** For the
two states the criss-cross actually presents — `3` and `3` — there is exactly one
valid `BaseDecision`, namely `selected 3`; `ambiguous` is excluded because a
base reaching `3` must *be* `3`, and `unavailable` because `3` reaches itself.

Set beside `Histories.state_validity_is_not_dag_ancestry` (no common ancestor
of `mergeL` and `mergeR` carries the state `3`) and `no_version_is_selectable_
here`: the unique answer the state-level model admits corresponds to **no version
of the history**, and the answer the history admits is not expressible at all. -/
theorem the_only_valid_state_decision (d : MergeModel.BaseDecision Nat) :
    d.Valid (spendOps 2).impl (ccState .mergeL) (ccState .mergeR)
      ↔ d = .selected (ccState .mergeL) := by
  constructor
  · intro h
    cases d with
    | selected l =>
      have hl : ccState .mergeL = l := by
        rcases spend_reachable 2 h.1 with he | ⟨_, h2⟩
        · exact he
        · exact absurd h2 (by decide)
      rw [hl]
    | ambiguous b₁ b₂ =>
      have h1 : ccState .mergeL = b₁ := by
        rcases spend_reachable 2 h.1.1 with he | ⟨_, h2⟩
        · exact he
        · exact absurd h2 (by decide)
      have h2 : ccState .mergeL = b₂ := by
        rcases spend_reachable 2 h.2.1.1 with he | ⟨_, h2⟩
        · exact he
        · exact absurd h2 (by decide)
      exact absurd (h1.symm.trans h2) h.2.2
    | unavailable =>
      exact absurd ⟨ccState .mergeL, Reachable.refl _ _, Reachable.refl _ _⟩ h
  · rintro rfl
    exact ⟨Reachable.refl _ _, Reachable.refl _ _⟩

/-- **The two conditions see past each other in both directions.** The state
level's unique valid answer names a base no common-ancestor version carries; the
history level's answer (`ambiguous left right`) has no valid state-level image,
since no `ambiguous` decision at all is valid for the pair `(3, 3)`. -/
theorem the_state_condition_sees_neither_direction :
    (∀ v, CommonAncestor ccDag .mergeL .mergeR v → ccState v ≠ 3)
      ∧ (MergeModel.BaseDecision.selected (3 : Nat)).Valid (spendOps 2).impl 3 3
      ∧ ValidInHistory ccHistory .mergeL .mergeR (.ambiguous .left .right)
      ∧ ∀ b₁ b₂ : Nat, ¬ (MergeModel.BaseDecision.ambiguous b₁ b₂).Valid
          (spendOps 2).impl (ccState .mergeL) (ccState .mergeR) := by
  refine ⟨state_validity_is_not_dag_ancestry.2, state_validity_is_not_dag_ancestry.1,
    ⟨cc_left_maximal, cc_right_maximal, by decide⟩, fun b₁ b₂ hv => ?_⟩
  have hd := (the_only_valid_state_decision _).mp hv
  simp at hd

/-! ### §3.3 Witness 3 — absence, in both directions

`dag_absence_does_not_license_unavailable` shows DAG absence does not give the
state-level refutation. The converse is new and is worse: the state-level
refutation fires on a pair whose versions have a **direct common parent**. -/

/-- **The history level accepts `unavailable` exactly where the state level is
prohibited from accepting it.** One object, both halves: the version graph has no
common ancestor of the two versions (so `ValidInHistory` is satisfied by a
genuine refutation), and the state-level obligation is refuted for the pair of
states they carry — by `state_unavailable_never_at_equal_states`, since a state
op-reaches itself. -/
theorem history_unavailable_where_the_state_level_must_refuse {S Op : Type}
    (impl : Impl S Op) (s : S) :
    ValidInHistory (twoHistory (S := S) (Op := Op) s) .x .y .unavailable
      ∧ ¬ (stateDecision (twoHistory (S := S) (Op := Op) s)
            (MergeModel.BaseDecision.unavailable (S := Two))).Valid impl
          ((twoHistory (S := S) (Op := Op) s).state .x)
          ((twoHistory (S := S) (Op := Op) s).state .y) :=
  ⟨two_no_common, state_unavailable_never_at_equal_states impl s⟩

/-- ⚠ **…and the state-level `unavailable` fires where the DAG hands over a
base.** `joinLeft` holds `5` and `joinRight` holds `4`; under budget `2` nothing
reaches either from below, so the state-level refutation succeeds — while
`mergeL` is a **direct parent of both versions**. A merge-base procedure
validated at the state level would report "no common base exists" for a pair
whose common base is one edge away.

Together with the previous theorem: the two obligations are logically
independent, neither implies the other, and only one of them is about the graph
`MergeModel` §9's docstring describes. -/
theorem state_unavailable_fires_where_the_dag_hands_a_base :
    (MergeModel.BaseDecision.unavailable (S := Nat)).Valid (spendOps 2).impl
        (ccState .joinLeft) (ccState .joinRight)
      ∧ CommonAncestor ccDag .joinLeft .joinRight .mergeL := by
  refine ⟨?_, ⟨Or.inr (Ancestry.direct (by decide)), Or.inr (Ancestry.direct (by decide))⟩⟩
  rintro ⟨b, h5, h4⟩
  have e5 : ccState .joinLeft = b := by
    rcases spend_reachable 2 h5 with he | ⟨_, h2⟩
    · exact he
    · exact absurd h2 (by decide)
  have e4 : ccState .joinRight = b := by
    rcases spend_reachable 2 h4 with he | ⟨_, h2⟩
    · exact he
    · exact absurd h2 (by decide)
  exact absurd (e5.trans e4.symm) (by decide)

/-! ### §3.4 The two-cycle needs two bases; the history licenses one

`Histories.swap_never_converges` builds an eternal two-cycle out of a base policy
`MergeModel.BaseDecision.Valid` fully licenses: for the pair (Alice, Bob) **both**
`selected Alice` and `selected Bob` are state-valid, and they disagree. The
history-level condition cannot license both — `selected_unique` — so the orbit's
licence is exactly what the state index fails to withhold. -/

/-- ⚠ **The eternal two-cycle needs two valid bases, and `ValidInHistory`
licenses at most one.** The first three conjuncts are `Histories.
lock_two_valid_bases` and `swap_never_converges`, quoted; the last is
`selected_unique`, which forbids the pair at the history level. ⟨UNDONE⟩ This
withdraws the *licence*; it is not a convergence proof. -/
theorem the_two_cycle_needs_two_bases_the_history_licenses_one :
    (MergeModel.BaseDecision.selected (⟨true, false⟩ : Lock)).Valid lockImpl
        ⟨true, false⟩ ⟨false, true⟩
      ∧ (MergeModel.BaseDecision.selected (⟨false, true⟩ : Lock)).Valid lockImpl
        ⟨true, false⟩ ⟨false, true⟩
      ∧ (∀ (n : Nat) (x y : Lock), x ≠ y →
          (iter swapRound n (x, y)).1 ≠ (iter swapRound n (x, y)).2)
      ∧ (∀ {V S Op : Type} (H : History V S Op) (x y b₁ b₂ : V),
          ValidInHistory H x y (.selected b₁) → ValidInHistory H x y (.selected b₂) →
            b₁ = b₂) :=
  ⟨lock_two_valid_bases.1, lock_two_valid_bases.2.1, swap_never_converges,
   fun _ _ _ _ _ h₁ h₂ => selected_unique h₁ h₂⟩

/-! ## §4. A coherent history is rooted — and `unavailable` is cross-history

`History.Coherent.sound` proves every version's state reachable from the root's
*state*, and needs four semantic hypotheses to do it. The **graph** half needs
none of them, and it was never stated. It is stated here, and it decides what
`MergeModel`'s third case is: not a case a procedure meets inside a history, but
the answer "these versions are not from the same history". -/

/-- **Every version of a coherent history is reached by its root, in the DAG.**
The graph half of `History.Coherent.sound`, with `LocallySafe`,
`AncestralConfluentFrom`, `MergeClosedFrom` and the root's legality all dropped:
`root_unique` says nothing but the root claims to be one, and every other origin
exhibits a parent of strictly smaller rank. -/
theorem coherent_reaches_from_root {V S Op : Type} {H : History V S Op}
    {M : AncestralMerge S} {impl : Impl S Op} (hco : H.Coherent M impl) :
    ∀ v, Reaches H.dag H.root v := by
  have step : ∀ v : V,
      (∀ w, H.dag.rank w < H.dag.rank v → Reaches H.dag H.root w) →
      Reaches H.dag H.root v := by
    intro v ih
    have hnode := hco.nodes v
    cases hor : H.origin v with
    | root =>
      have hv : v = H.root := hco.root_unique v hor
      subst hv
      exact Reaches.refl _ _
    | ran p =>
      simp only [OriginOK, hor] at hnode
      exact Reaches.trans (ih p (H.dag.rank_lt _ _ hnode.1))
        (Or.inr (Ancestry.direct hnode.1))
    | merged l x y =>
      simp only [OriginOK, hor] at hnode
      exact Reaches.trans (ih x (H.dag.rank_lt _ _ hnode.1))
        (Or.inr (Ancestry.direct hnode.1))
  have key : ∀ (n : Nat) (v : V), H.dag.rank v ≤ n → Reaches H.dag H.root v := by
    intro n
    induction n with
    | zero => intro v hv; exact step v (fun w hw => absurd hw (by omega))
    | succ n ih => intro v hv; exact step v (fun w hw => ih w (by omega))
  intro v
  exact key (H.dag.rank v) v (Nat.le_refl _)

/-- ⚠ **Inside one coherent history, `unavailable` is never valid.** The root is
a common ancestor of every pair, so the third case's obligation — a refutation of
*every* common ancestor version — is unsatisfiable.

So `MergeModel.BaseDecision.unavailable` is not the answer to "I looked and found
nothing"; within a history there is always something to find. It is the answer to
"these two versions are not from the same history", and the state level cannot
say that at all (`state_unavailable_never_at_equal_states`). -/
theorem coherent_never_unavailable {V S Op : Type} {H : History V S Op}
    {M : AncestralMerge S} {impl : Impl S Op} (hco : H.Coherent M impl) (x y : V) :
    ¬ ValidInHistory H x y .unavailable :=
  fun h => h H.root ⟨coherent_reaches_from_root hco x, coherent_reaches_from_root hco y⟩

/-- **…and the witness that satisfies `unavailable` is provably not one history.**
`twoHistory` has two versions both claiming to be roots, which `root_unique`
forbids. The third case's only inhabitant here is a graph that is not a coherent
history — which is what "cross-history" means. -/
theorem twoHistory_not_coherent {S Op : Type} (M : AncestralMerge S) (impl : Impl S Op)
    (s : S) : ¬ (twoHistory (S := S) (Op := Op) s).Coherent M impl := by
  intro h
  have hy : (Two.y : Two) = (twoHistory (S := S) (Op := Op) s).root := h.root_unique .y rfl
  exact absurd (show (Two.y : Two) = Two.x from hy) (by decide)

/-- The criss-cross is coherent, so its two merge versions are certified not to
admit `unavailable` — the non-vacuity of `coherent_never_unavailable` at a
history that exists. -/
theorem cc_never_unavailable (x y : Ver) :
    ¬ ValidInHistory ccHistory x y .unavailable :=
  coherent_never_unavailable ccHistory_coherent x y

/-! ## §5. The closure condition, transported — a NO and a YES

`Histories.lean` located the break at `MergeClosedFrom`: a merge result is not
op-reachable from the root, so the second merge is outside the theorem. Is
closure expressible on the DAG rather than on runs?

**No, as a condition.** `MergeClosedFrom M impl ρ` quantifies over *every* triple
of states reachable from `ρ`, and a history contains finitely many merges of
particular triples. `runRealized_does_not_imply_mergeClosed` makes that concrete:
a two-node history, its one edge a genuine run, over a merge that is not closed.

**Yes, for the soundness it was introduced to buy.** `RunRealized` is edge-local
— one obligation per edge of the history that exists — and
`coherent_sound_of_runRealized` proves it enough on its own: every version of a
run-realized coherent history is legal, from local safety and a legal root, with
no merge law, no closure and no confluence hypothesis at all. That is the
usability win: a history that records the operations on its edges is checkable
edge by edge.

The two conditions are **independent**, and both directions are witnessed. -/

/-- **Run-realized coherence gives root-reachability of every state**, with no
merge hypothesis: `coherent_reaches_from_root` in the graph, then
`Histories.reaches_reachable` to states. -/
theorem coherent_root_reachable_of_runRealized {V S Op : Type} {H : History V S Op}
    {M : AncestralMerge S} {impl : Impl S Op}
    (hco : H.Coherent M impl) (hrr : RunRealized H impl) (v : V) :
    Reachable impl (H.state H.root) (H.state v) :=
  reaches_reachable hrr (coherent_reaches_from_root hco v)

/-- ⚠ **The soundness of a coherent history, without a single merge
hypothesis.** Compare `History.Coherent.sound`, which needs
`AncestralConfluentFrom` *and* `MergeClosedFrom`: if every DAG edge is a local
run then the whole history is one big local run tree and merges are invisible to
the invariant. `LocallySafe` and a legal root are all that is left.

Read as the diagnosis it is: the two merge conditions are needed **exactly**
because a merge edge is not a run — which is `Histories.
dag_ancestry_is_not_run_reachable`, priced. -/
theorem coherent_sound_of_runRealized {V S Op : Type} {H : History V S Op}
    {M : AncestralMerge S} {impl : Impl S Op} {I : Invariant S}
    (hco : H.Coherent M impl) (hrr : RunRealized H impl)
    (hloc : LocallySafe impl I) (hroot : I (H.state H.root)) (v : V) :
    I (H.state v) := by
  obtain ⟨_, hops⟩ := coherent_root_reachable_of_runRealized hco hrr v
  exact hops.preserves hloc hroot

/-! ### §5.1 Direction one — run-realized, and not merge-closed -/

/-- Two versions, one edge. -/
inductive LinVer where
  /-- The root. -/
  | l0
  /-- One spend later. -/
  | l1
  deriving DecidableEq, Repr

/-- The single edge. -/
def linParent : LinVer → LinVer → Bool
  | .l0, .l1 => true
  | _, _ => false

/-- Depth. -/
def linRank : LinVer → Nat
  | .l0 => 0
  | .l1 => 1

/-- The linear version DAG. -/
def linDag : VersionDag LinVer where
  parent := linParent
  rank := linRank
  rank_lt := by intro p c; cases p <;> cases c <;> decide

/-- The states: one spend from zero. -/
def linState : LinVer → Nat
  | .l0 => 0
  | .l1 => 1

/-- The origins: a root and a local run. -/
def linOrigin : LinVer → Origin LinVer
  | .l0 => .root
  | .l1 => .ran .l0

/-- A history with **no merges at all**, over the counter MRDT. -/
def linHistory : History LinVer Nat Unit where
  dag := linDag
  state := linState
  origin := linOrigin
  root := .l0

theorem linOrigin_root_unique (v : LinVer) (h : linOrigin v = Origin.root) : v = .l0 := by
  cases v <;> simp_all [linOrigin]

theorem linHistory_coherent : linHistory.Coherent counterAM (spendOps 2).impl where
  root_unique := linOrigin_root_unique
  nodes := by
    intro v
    cases v
    · trivial
    · show linDag.parent .l0 .l1 = true ∧ Reachable (spendOps 2).impl 0 1
      exact ⟨by decide, spend2_reach_one⟩

theorem linHistory_runRealized : RunRealized linHistory (spendOps 2).impl := by
  intro p c hpc
  cases p <;> cases c <;>
    first
      | exact absurd hpc (by decide)
      | exact spend2_reach_one

/-- ⚠ **`RunRealized` does not imply `MergeClosedFrom`.** A coherent history whose
every edge is a genuine local run, over a merge whose closure is refuted
(`Histories.counter_not_mergeClosed`). Closure is a condition on the *merge over
all reachable triples*, not on the graph — a history that never merges cannot
witness it either way, and this one does not. -/
theorem runRealized_does_not_imply_mergeClosed :
    RunRealized linHistory (spendOps 2).impl
      ∧ linHistory.Coherent counterAM (spendOps 2).impl
      ∧ ¬ MergeClosedFrom counterAM (spendOps 2).impl (linHistory.state linHistory.root) :=
  ⟨linHistory_runRealized, linHistory_coherent, counter_not_mergeClosed⟩

/-! ### §5.2 Direction two — merge-closed, and not run-realized

A merge that **rolls back to the base** when both replicas moved: the numeric
analogue of `lockPriority` returning "nobody holds it". It fast-forwards past an
unmoved replica, so it is a genuine `AncestralMerge`, and its result is `0`
whenever there is a real conflict — a state no amount of spending reaches from a
replica that has already spent. -/

/-- **The roll-back merge**: fast-forward past an unmoved replica, otherwise
discard both and return to zero. -/
def resetMerge3 (l x y : Nat) : Nat :=
  if x = l then y else if y = l then x else 0

theorem resetMerge3_comm (l x y : Nat) : resetMerge3 l x y = resetMerge3 l y x := by
  unfold resetMerge3
  by_cases hx : x = l <;> by_cases hy : y = l <;> simp [hx, hy]

/-- The roll-back merge as an `AncestralMerge`. -/
def resetAM : AncestralMerge Nat where
  merge3 := resetMerge3
  comm := resetMerge3_comm
  fastforward l y := by
    show resetMerge3 l l y = y
    unfold resetMerge3
    rw [if_pos rfl]

/-- **The roll-back merge is closed from zero**: every branch returns a replica
the caller already had, or `0`. Contrast `Histories.counter_not_mergeClosed`. -/
theorem reset_mergeClosed : MergeClosedFrom resetAM (spendOps 5).impl 0 := by
  intro l x y _ hx hy
  show Reachable (spendOps 5).impl 0 (resetMerge3 l x y)
  unfold resetMerge3
  by_cases hxl : x = l
  · rw [if_pos hxl]; exact hy
  · rw [if_neg hxl]
    by_cases hyl : y = l
    · rw [if_pos hyl]; exact hx
    · rw [if_neg hyl]; exact Reachable.refl _ _

/-- …and it is confluent from zero for the ceiling of five, for the same reason:
every branch is an input or `0`. -/
theorem reset_ancestralConfluentFrom :
    AncestralConfluentFrom resetAM (spendOps 5).impl (fun n => n ≤ 5) 0 := by
  intro l x y _ _ _ _ hx hy
  show resetMerge3 l x y ≤ 5
  unfold resetMerge3
  by_cases hxl : x = l
  · rw [if_pos hxl]; exact hy
  · rw [if_neg hxl]
    by_cases hyl : y = l
    · rw [if_pos hyl]; exact hx
    · rw [if_neg hyl]; exact Nat.zero_le 5

/-- Four versions: a fork and a merge. -/
inductive RVer where
  /-- The fork point. -/
  | rRoot
  /-- One branch, three spends. -/
  | rP
  /-- The other branch, five spends. -/
  | rQ
  /-- The merge of the two branches — which rolls back. -/
  | rM
  deriving DecidableEq, Repr

/-- The fork-and-merge edges. -/
def rParent : RVer → RVer → Bool
  | .rRoot, .rP => true
  | .rRoot, .rQ => true
  | .rP, .rM => true
  | .rQ, .rM => true
  | _, _ => false

/-- Depth. -/
def rRank : RVer → Nat
  | .rRoot => 0
  | .rP => 1
  | .rQ => 1
  | .rM => 2

/-- The fork-and-merge DAG. -/
def rDag : VersionDag RVer where
  parent := rParent
  rank := rRank
  rank_lt := by intro p c; cases p <;> cases c <;> decide

/-- The states. `rM` is `resetMerge3 0 3 5 = 0`: both branches moved, so the
merge rolls back. -/
def rState : RVer → Nat
  | .rRoot => 0
  | .rP => 3
  | .rQ => 5
  | .rM => 0

/-- The origins. -/
def rOrigin : RVer → Origin RVer
  | .rRoot => .root
  | .rP => .ran .rRoot
  | .rQ => .ran .rRoot
  | .rM => .merged .rRoot .rP .rQ

/-- A fork-and-merge history over the roll-back merge. -/
def resetHistory : History RVer Nat Unit where
  dag := rDag
  state := rState
  origin := rOrigin
  root := .rRoot

theorem rOrigin_root_unique (v : RVer) (h : rOrigin v = Origin.root) : v = .rRoot := by
  cases v <;> simp_all [rOrigin]

theorem rRoot_common : CommonAncestor rDag .rP .rQ .rRoot :=
  ⟨Or.inr (Ancestry.direct (by decide)), Or.inr (Ancestry.direct (by decide))⟩

theorem resetHistory_coherent : resetHistory.Coherent resetAM (spendOps 5).impl where
  root_unique := rOrigin_root_unique
  nodes := by
    intro v
    cases v
    · trivial
    · show rDag.parent .rRoot .rP = true ∧ Reachable (spendOps 5).impl 0 3
      exact ⟨by decide, spend_reach 5 (by omega) (by omega)⟩
    · show rDag.parent .rRoot .rQ = true ∧ Reachable (spendOps 5).impl 0 5
      exact ⟨by decide, spend_reach 5 (by omega) (by omega)⟩
    · show rDag.parent .rP .rM = true ∧ rDag.parent .rQ .rM = true ∧
        CommonAncestor rDag .rP .rQ .rRoot ∧ (0 : Nat) = resetMerge3 0 3 5
      exact ⟨by decide, by decide, rRoot_common, by decide⟩

/-- ⚠ **`MergeClosedFrom` does not imply `RunRealized`.** The roll-back merge is
closed from the root, and the edge `rQ ⟶ rM` is not a run: `rQ` holds `5` and
the merge holds `0`, and spending never decreases. So the graph-side condition is
genuinely stronger on this history than the closure condition, in the direction
`Histories` §7.2 does not cover. -/
theorem resetHistory_not_runRealized : ¬ RunRealized resetHistory (spendOps 5).impl := by
  intro h
  have h50 : Reachable (spendOps 5).impl 5 0 := h .rQ .rM (by decide)
  rcases spend_reachable 5 h50 with he | ⟨h1, _⟩
  · exact absurd he (by decide)
  · exact absurd h1 (by decide)

/-- The roll-back history *is* sound, by `History.Coherent.sound` and the closure
condition — so §5.2's witness is not a broken history, only one whose edges are
not runs. -/
theorem resetHistory_sound :
    ∀ v, Reachable (spendOps 5).impl 0 (rState v) ∧ rState v ≤ 5 :=
  resetHistory_coherent.sound (spend_locally_safe 5)
    reset_ancestralConfluentFrom reset_mergeClosed (by decide)

/-- **The closure verdict, both directions and the repair.** Closure is *not* a
condition on the DAG — it is refuted by a history with no merges at all — but the
soundness it buys is obtainable edge-locally from `RunRealized`, and the two
conditions are independent. -/
theorem closure_is_not_a_dag_condition_but_soundness_is :
    (RunRealized linHistory (spendOps 2).impl
        ∧ ¬ MergeClosedFrom counterAM (spendOps 2).impl 0)
      ∧ (MergeClosedFrom resetAM (spendOps 5).impl 0
        ∧ ¬ RunRealized resetHistory (spendOps 5).impl)
      ∧ (∀ v, (fun n => n ≤ 2) (linState v)) :=
  ⟨⟨linHistory_runRealized, counter_not_mergeClosed⟩,
   ⟨reset_mergeClosed, resetHistory_not_runRealized⟩,
   fun v => coherent_sound_of_runRealized linHistory_coherent linHistory_runRealized
     (spend_locally_safe 2) (by decide) v⟩

/-! ## §6. Merge bases in a world

`WorldFuture.lean`'s boundary names two dropped components of codex's separation.
One is *known merge bases*, dropped because "a merge base is a fact about a
history DAG, and this file has no history". `Histories.lean` supplies one. This
section places worlds at the versions of a DAG and collects what that buys. -/

/-- **A world placed in a version history.** Not a `Histories.History`: `World α`
carries no `AncestralMerge` and no operation alphabet, so there is no `Origin`
obligation to discharge. What it carries is what `WorldFuture` needed and did not
have — a graph of versions to select a base from. -/
structure BasedWorld (α V : Type) where
  /-- The version graph the replica knows. -/
  dag : VersionDag V
  /-- The world each version stands in. -/
  world : V → WorldFuture.World α

/-- **The component `WorldFuture.World` dropped, restored.** `Histories.
BaseSelection` over the placed DAG: a certified lowest base, two certified
maximal ones, or a refutation. -/
abbrev MergeBases {α V : Type} (B : BasedWorld α V) (x y : V) : Type :=
  BaseSelection B.dag x y

/-- **The delivery future, indexed by history position.** -/
def DeliveryAt {α V : Type} (B : BasedWorld α V) (u v : V) : Prop :=
  WorldFuture.DeliveryFuture (B.world u) (B.world v)

/-- **The DAG edges are extension futures** — the world-carrier analogue of
`Histories.RunRealized`, and what makes a placement more than an arbitrary
labelling. -/
def ExtensionRealized {α V : Type} (B : BasedWorld α V) : Prop :=
  ∀ p c, B.dag.parent p c = true →
    WorldFuture.ExtensionFuture (B.world p) (B.world c)

/-! ### §6.1 A placement of `WorldFuture`'s three witnesses

`start` — nothing issued anywhere, so the replica is quiesced. It forks: on one
side nothing happens (`quiesced`), on the other `bob` issues `49` and it has not
arrived (`pending`). `delivered` is `pending` after the delivery.

`quiesced` and `pending` carry the **same materialized state** and different
pools: that is `WorldFuture.same_observation`, now sitting at two versions of one
history. -/

/-- Four versions. -/
inductive WVer where
  /-- Before anything was issued. -/
  | start
  /-- Nothing was issued: the replica is quiesced. -/
  | quiesced
  /-- `bob` issued `49`; it has not arrived. -/
  | pending
  /-- `bob`'s `49` delivered. -/
  | delivered
  deriving DecidableEq, Repr

/-- The fork, and the delivery step. -/
def wParent : WVer → WVer → Bool
  | .start, .quiesced => true
  | .start, .pending => true
  | .pending, .delivered => true
  | _, _ => false

/-- Depth. -/
def wRank : WVer → Nat
  | .start => 0
  | .quiesced => 1
  | .pending => 1
  | .delivered => 2

/-- The placed version DAG. -/
def wDag : VersionDag WVer where
  parent := wParent
  rank := wRank
  rank_lt := by intro p c; cases p <;> cases c <;> decide

/-- The worlds. `start` and `quiesced` both stand in `wQuiesced`: nothing is in
flight at either. -/
def wWorld : WVer → WorldFuture.World Holes.Val
  | .start => WorldFuture.wQuiesced
  | .quiesced => WorldFuture.wQuiesced
  | .pending => WorldFuture.wPending
  | .delivered => WorldFuture.wDelivered

/-- The placement. -/
def wBased : BasedWorld Holes.Val WVer where
  dag := wDag
  world := wWorld

theorem wExt_quiesced_refl :
    WorldFuture.ExtensionFuture WorldFuture.wQuiesced WorldFuture.wQuiesced :=
  ⟨Evidence.extensionFuture_refl _, leq_refl _,
   WorldFuture.wf_of_quiesced WorldFuture.quiesced_wQuiesced, Nat.le_refl _,
   fun _ h0 h1 => Bool.noConfusion (h0.symm.trans h1)⟩

/-- `bob` issuing `49` is an extension: the pool grows, the state does not. -/
theorem wExt_start_pending :
    WorldFuture.ExtensionFuture WorldFuture.wQuiesced WorldFuture.wPending :=
  ⟨Evidence.extensionFuture_refl _, Evidence.openW_extends_to_openForkW.1,
   WorldFuture.wf_wPending, Nat.le_refl _,
   fun _ h0 h1 => Bool.noConfusion (h0.symm.trans h1)⟩

/-- …and the delivery is an extension too. -/
theorem wExt_pending_delivered :
    WorldFuture.ExtensionFuture WorldFuture.wPending WorldFuture.wDelivered :=
  ⟨Evidence.openW_extends_to_openForkW, leq_refl _, WorldFuture.wf_wDelivered,
   Nat.le_refl _, fun _ h0 h1 => Bool.noConfusion (h0.symm.trans h1)⟩

/-- **The placement is extension-realized**: every edge of the DAG is a
legitimate world step. -/
theorem wBased_extensionRealized : ExtensionRealized wBased := by
  intro p c hpc
  cases p <;> cases c <;>
    first
      | exact absurd hpc (by decide)
      | exact wExt_quiesced_refl
      | exact wExt_start_pending
      | exact wExt_pending_delivered

/-! ### §6.2 The merge base of the two siblings -/

theorem wDag_quiesced_is_a_leaf (c : WVer) : wDag.parent .quiesced c = false := by
  cases c <;> decide

/-- The common ancestors of the two siblings are exactly the fork point. -/
theorem w_branch_commonAncestors (v : WVer)
    (h : CommonAncestor wDag .quiesced .pending v) : v = .start := by
  cases v
  · rfl
  · exact absurd (reaches_of_leaf wDag_quiesced_is_a_leaf h.2) (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)

/-- **The fork point is the lowest common base of the two siblings.** -/
theorem w_start_lowest : LowestCommonBase wDag .quiesced .pending .start := by
  refine ⟨⟨Or.inr (Ancestry.direct (by decide)), Or.inr (Ancestry.direct (by decide))⟩, ?_⟩
  intro c hc
  rcases w_branch_commonAncestors c hc with rfl
  exact Reaches.refl _ _

/-- **The dropped component, inhabited.** A certified merge base for a pair of
versions of a world history — the field `WorldFuture.World` could not carry. -/
def wMergeBase : MergeBases wBased .quiesced .pending :=
  .selected .start w_start_lowest

/-- ⚠ **DAG ancestry is not delivery.** The two siblings are both reached by the
fork point and **no delivery future links them in either direction**, because a
delivery future freezes the pool and their pools differ. This is
`Histories.dag_ancestry_is_not_run_reachable` at the world carrier: a graph edge
is not a step of the semantics, in either file.

Note what makes it sharp: the two versions carry the *same materialized state*
(`WorldFuture.same_observation`), so nothing a replica holds distinguishes them,
and the graph says they are siblings. -/
theorem dag_ancestry_is_not_delivery :
    Reaches wDag .start .quiesced ∧ Reaches wDag .start .pending
      ∧ WorldFuture.observe (wWorld .quiesced) = WorldFuture.observe (wWorld .pending)
      ∧ ¬ DeliveryAt wBased .quiesced .pending
      ∧ ¬ DeliveryAt wBased .pending .quiesced := by
  refine ⟨Or.inr (Ancestry.direct (by decide)), Or.inr (Ancestry.direct (by decide)),
    rfl, fun h => ?_, fun h => ?_⟩
  · exact absurd h.2.1.symm WorldFuture.frontier_and_epoch_do_not_separate.2.2.2.2
  · exact absurd h.2.1 WorldFuture.frontier_and_epoch_do_not_separate.2.2.2.2

/-! ### §6.3 ⚠ The base scope repairs the state-keyed certificate

`WorldFuture.no_sound_state_cert_accepts_openW` is the sharpest statement of the
reuse unsoundness: **every** sound state-indexed exactness certificate must
refuse `openW`, including the one a replica standing at `wQuiesced` correctly
verified. The repair `WorldFuture.lean` gives is to move the index to the world.

With a history there is a third option, and it is the one a merge-base procedure
already computes: let the certificate **name the base it was computed against**,
and scope its licence to that base's descendants. The scope is a DAG fact.

It is not a free pass: scoped to the history root the same certificate is unsound
again, because the root reaches the divergent version. -/

/-- A certificate indexed by a history position. -/
def VersionCert (V : Type) : Type := V → Prop

/-- **Sound, unscoped**: at every version it accepts, the rendered answer really
is delivery-stable. -/
def VersionCertSound {α V : Type} (B : BasedWorld α V) (C : VersionCert V) : Prop :=
  ∀ v, C v →
    Evidence.FreeTermination WorldFuture.DeliveryFuture WorldFuture.renderW (B.world v)

/-- **Sound against a named base**: the licence is claimed only for versions the
base reaches. This is what "the certificate names the base it was computed
against" buys, and the premise `Reaches B.dag b v` is checkable from the graph. -/
def BasedCertSound {α V : Type} (B : BasedWorld α V) (b : V) (C : VersionCert V) : Prop :=
  ∀ v, C v → Reaches B.dag b v →
    Evidence.FreeTermination WorldFuture.DeliveryFuture WorldFuture.renderW (B.world v)

/-- A world-indexed certificate names a version's world; the version index is a
name for it, no more. ⟨UNDONE⟩ There is no theorem here that the version index
separates worlds a `WorldFuture.WorldCert` cannot — it does not. -/
theorem versionCertSound_of_worldCertSound {α V : Type} (B : BasedWorld α V)
    {C : WorldFuture.WorldCert α} (h : WorldFuture.WorldCertSound C) :
    VersionCertSound B (fun v => C (B.world v)) :=
  fun v hv => h (B.world v) hv

/-- An unscoped licence is in particular a licence scoped to any base. -/
theorem basedCertSound_of_versionCertSound {α V : Type} {B : BasedWorld α V}
    {C : VersionCert V} (h : VersionCertSound B C) (b : V) : BasedCertSound B b C :=
  fun v hv _ => h v hv

/-- **Quiescence is a sound version-indexed certificate** — `WorldFuture.
quiescence_is_a_sound_certificate` placed, and unscoped: it needs no base,
because it reads the world. -/
theorem quiescence_is_a_sound_version_certificate {α V : Type} (B : BasedWorld α V) :
    VersionCertSound B (fun v => WorldFuture.Quiesced (B.world v)) :=
  versionCertSound_of_worldCertSound B WorldFuture.quiescence_is_a_sound_certificate

/-- **The certificate a replica at `wQuiesced` actually files**: keyed on the
materialized state it observed. It accepts `quiesced` — and `pending`, which
observes the same state and is not stable. -/
def stateKeyed : VersionCert WVer :=
  fun v => WorldFuture.observe (wWorld v) = Evidence.openW

/-- The state-keyed certificate accepts the version where the check was made… -/
theorem stateKeyed_accepts_quiesced : stateKeyed .quiesced := rfl

/-- …and the one where it is false. -/
theorem stateKeyed_accepts_pending : stateKeyed .pending := rfl

/-- ⚠ **Unscoped, the state-keyed certificate is unsound** — the placed form of
`WorldFuture.certificate_reuse_is_unsound`. -/
theorem stateKeyed_not_sound : ¬ VersionCertSound wBased stateKeyed :=
  fun h => WorldFuture.not_stable_at_wPending (h .pending stateKeyed_accepts_pending)

/-- ⚠ **…and sound against the base it was computed against.** `quiesced` is a
leaf of the version graph, so its descendant set is itself, and every version the
certificate accepts within that scope really is delivery-stable. -/
theorem stateKeyed_sound_at_its_base : BasedCertSound wBased .quiesced stateKeyed := by
  intro v _ hreach
  have hv : WVer.quiesced = v := reaches_of_leaf wDag_quiesced_is_a_leaf hreach
  subst hv
  exact WorldFuture.stable_at_wQuiesced

/-- ⚠ **The scope is not a free pass.** Scoped to the *history root* the same
certificate is unsound again: the root reaches `pending`. So "name your base" is
a real obligation with a real refutation, not a decoration — which base you name
decides whether the licence holds. -/
theorem stateKeyed_unsound_at_the_root : ¬ BasedCertSound wBased .start stateKeyed :=
  fun h => WorldFuture.not_stable_at_wPending
    (h .pending stateKeyed_accepts_pending (Or.inr (Ancestry.direct (by decide))))

/-- ⚠ **THE REPAIR.** `WorldFuture.no_sound_state_cert_accepts_openW` prohibits
every sound state-indexed certificate from accepting `openW`. A certificate that
names the base it was computed against accepts a version observing exactly that
state, and is sound — and is unsound if it names the wrong base.

The three conjuncts are the whole story: the prohibition, the acceptance, and
the two verdicts that make the scope load-bearing. -/
theorem the_base_scope_repairs_the_state_keyed_certificate :
    (∀ C : WorldFuture.StateCert Holes.Val, WorldFuture.StateCertSound C →
        ¬ C Evidence.openW)
      ∧ WorldFuture.observe (wWorld .quiesced) = Evidence.openW
      ∧ stateKeyed .quiesced
      ∧ BasedCertSound wBased .quiesced stateKeyed
      ∧ ¬ BasedCertSound wBased .start stateKeyed
      ∧ ¬ VersionCertSound wBased stateKeyed :=
  ⟨fun C hC => WorldFuture.no_sound_state_cert_accepts_openW C hC, rfl,
   stateKeyed_accepts_quiesced, stateKeyed_sound_at_its_base,
   stateKeyed_unsound_at_the_root, stateKeyed_not_sound⟩

/-! ## §7. The price of ambiguity

`Histories.base_accident_decides_the_invariant`: two maximal common bases, no
lowest one, results `5` and `4`, ceiling `4`. `MergeModel.decidedMerge`'s
`ambiguous` branch **does not use a base** — it hands the pair to the
conflict-resolution policy. §7 prices that design decision.

The price has two halves and they point the same way:

  * the ambiguous branch is *safe* on the criss-cross where both base choices are
    not (`ambiguity_is_the_safe_branch_here`);
  * and it is **unreachable** from the state level, because no `ambiguous`
    decision is valid for the pair of states the criss-cross presents
    (`no_state_ambiguous_decision_here`, from `the_only_valid_state_decision`).

⚠ The sharpest form is `counter_decision_iconfluentIn`: the base-decision model
is I-confluent-in for the counter — it certifies the merge — while a coherent
history over the same merge, implementation and invariant has an illegal node.
The model is safe because its `validContext` refuses, on reachability grounds,
the merge that actually happens. -/

/-- The two-way join as a conflict-resolution policy: what a replica does when it
has no base to merge against. -/
def joinResolve (x y : Nat) : Nat := Nat.max x y

/-- **No state-level `ambiguous` decision is valid for the criss-cross pair.**
Both bases would have to reach the state `3`, and under budget `2` only `3`
does — so they cannot be distinct. The version-level ambiguity is real
(`Histories.cc_left_maximal`, `cc_right_maximal`) and inexpressible. -/
theorem no_state_ambiguous_decision_here (b₁ b₂ : Nat) :
    ¬ (MergeModel.BaseDecision.ambiguous b₁ b₂).Valid (spendOps 2).impl
      (ccState .mergeL) (ccState .mergeR) := by
  intro hv
  have hd := (the_only_valid_state_decision _).mp hv
  simp at hd

/-- ⚠ **Ambiguity is the safe branch here, and only the history can select it.**
Against `left` the merge lands on `5` and against `right` on `4`, over a ceiling
of `4` — the two legitimate base choices `Histories.base_accident_decides_the_
invariant` exhibits. The `ambiguous` branch uses neither: it hands `(3, 3)` to
the policy, which returns `3`.

So `MergeModel` §9's refusal to merge against a base under ambiguity is not
conservatism, it is what keeps the invariant on this history — and
`no_state_ambiguous_decision_here` says the state-indexed model can never take
that branch for this pair. -/
theorem ambiguity_is_the_safe_branch_here :
    ValidInHistory ccHistory .mergeL .mergeR (.ambiguous .left .right)
      ∧ (MergeModel.decidedMerge counterAM joinResolve
          (.selected (ccState .left)) (ccState .mergeL) (ccState .mergeR)).state = 5
      ∧ (MergeModel.decidedMerge counterAM joinResolve
          (.selected (ccState .right)) (ccState .mergeL) (ccState .mergeR)).state = 4
      ∧ (MergeModel.decidedMerge counterAM joinResolve
          (.ambiguous (ccState .left) (ccState .right))
          (ccState .mergeL) (ccState .mergeR)).state = 3
      ∧ ¬ ((5 : Nat) ≤ 4) ∧ ((3 : Nat) ≤ 4)
      ∧ ∀ b₁ b₂ : Nat, ¬ (MergeModel.BaseDecision.ambiguous b₁ b₂).Valid
          (spendOps 2).impl (ccState .mergeL) (ccState .mergeR) :=
  ⟨⟨cc_left_maximal, cc_right_maximal, by decide⟩, by decide, by decide, by decide,
   by decide, by decide, no_state_ambiguous_decision_here⟩

/-- ⚠ **The base-decision model certifies what the history breaks.** Every
legitimate context, every pair of legal replicas: the merge result is under the
ceiling. The `selected` branch is safe because `validContext` demands both
replicas be *run-reachable from the base*, and the merge that breaks §5's history
— `mergeL`/`mergeR` against `left` — fails exactly that demand
(`Histories.dag_ancestry_is_not_run_reachable`). The `ambiguous` and
`unavailable` branches are safe because the policy never exceeds its inputs.

Set beside `Histories.repeated_merge_breaks_the_invariant`, this is the defect at
its sharpest: a merge model can be I-confluent-in *because* its validity
condition does not describe the merges a history performs. -/
theorem counter_decision_iconfluentIn :
    MergeModel.IConfluentIn
      (MergeModel.DecisionKey counterAM (spendOps 2).impl joinResolve)
      (fun n : Nat => n ≤ 4) := by
  intro c x y hv hobs hx hy
  cases c with
  | selected l =>
    have hl : l ≤ 4 := hobs l (by show l ∈ [l]; exact List.Mem.head _)
    have hrx := spend_reachable 2 hv.1
    have hry := spend_reachable 2 hv.2
    show counterMerge l x y ≤ 4
    unfold counterMerge
    rcases hrx with h | ⟨h1, h2⟩ <;> rcases hry with h' | ⟨h1', h2'⟩ <;> omega
  | ambiguous _ _ =>
    show joinResolve x y ≤ 4
    unfold joinResolve
    rw [Catalog.nat_max_def]
    split <;> assumption
  | unavailable =>
    show joinResolve x y ≤ 4
    unfold joinResolve
    rw [Catalog.nat_max_def]
    split <;> assumption

/-- **The certified set is not empty.** `counter_decision_iconfluentIn` would say
little if no context were ever legitimate. A `selected` context at a genuine
triple — the merge computes `3` from `0, 1, 2`, which is `ccHistory`'s first
round — and a valid `ambiguous` one, so both branches of that proof are
exercised. -/
theorem counter_decision_contexts_inhabited :
    (MergeModel.BaseDecision.selected (0 : Nat)).Valid (spendOps 2).impl 1 2
      ∧ (MergeModel.decidedMerge counterAM joinResolve (.selected 0) 1 2).state = 3
      ∧ (MergeModel.BaseDecision.ambiguous (0 : Nat) 1).Valid (spendOps 2).impl 2 2 :=
  ⟨⟨spend2_reach_one, spend2_reach_two⟩, by decide,
   ⟨⟨spend2_reach_two, spend2_reach_two⟩,
    ⟨spend_reach 2 (by omega) (by omega), spend_reach 2 (by omega) (by omega)⟩,
    by decide⟩⟩

/-- ⚠ **The model is safe and the history is not.** Same merge, same
implementation, same invariant: `MergeModel.IConfluentIn` holds, `ccHistory` is
coherent, its root is legal, and `joinLeft` holds `5`. -/
theorem the_model_certifies_what_the_history_breaks :
    MergeModel.IConfluentIn
        (MergeModel.DecisionKey counterAM (spendOps 2).impl joinResolve)
        (fun n : Nat => n ≤ 4)
      ∧ ccHistory.Coherent counterAM (spendOps 2).impl
      ∧ ccState .root ≤ 4
      ∧ ¬ (ccState .joinLeft ≤ 4) :=
  ⟨counter_decision_iconfluentIn, ccHistory_coherent, by decide, by decide⟩

/-- **Whether ambiguity is visible at the state level, and whether it is free,
come apart — in opposite directions, on two histories.** In the lock the two
maximal bases carry distinct states, so `MergeModel.BaseDecision.ambiguous` is
valid there (`Histories.lock_ambiguous_valid`) — and the base choice costs
nothing (`lock_join_base_insensitive`). In the counter no state-level `ambiguous`
decision is valid at all — and the base choice decides the invariant.

⟨UNDONE⟩ Two histories, not a classification: nothing here says visibility and
harmlessness are always anti-correlated. -/
theorem ambiguity_is_visible_where_it_is_free :
    (MergeModel.BaseDecision.ambiguous (lvState .alice) (lvState .bob)).Valid lockImpl
        (lvState .m1) (lvState .m2)
      ∧ lockAM.merge3 (lvState .alice) (lvState .m1) (lvState .m2)
        = lockAM.merge3 (lvState .bob) (lvState .m1) (lvState .m2)
      ∧ (∀ b₁ b₂ : Nat, ¬ (MergeModel.BaseDecision.ambiguous b₁ b₂).Valid
          (spendOps 2).impl (ccState .mergeL) (ccState .mergeR))
      ∧ counterAM.merge3 (ccState .left) (ccState .mergeL) (ccState .mergeR)
        ≠ counterAM.merge3 (ccState .right) (ccState .mergeL) (ccState .mergeR) :=
  ⟨lock_ambiguous_valid, lock_join_base_insensitive,
   no_state_ambiguous_decision_here, crisscross_diverges⟩

/-! ## §8. The contact zone, side by side -/

/-- **What became true when the three files touched.**

  * **The repair.** A base decision certified by the version DAG
    (`ValidInHistory`), transporting into `MergeModel.BaseDecision.Valid` under
    `RunRealized`, with at most one selectable base per pair.
  * **Witness 2, refused.** No version of the criss-cross is selectable for the
    pair the state level accepts a phantom base for.
  * **Witness 3, both directions.** The state-level `unavailable` obligation is
    refuted by any run relating the replicas; and it *fires* on a pair whose
    versions have a direct common parent.
  * **The third case, placed.** A coherent history is rooted, so `unavailable` is
    never valid inside one — it is a cross-history answer.
  * **Closure.** Not a DAG condition; the soundness it buys is edge-local.
  * **The price.** No state-level `ambiguous` decision is valid where ambiguity
    decides the invariant — and the decision model is I-confluent-in for the
    merge whose history breaks. -/
theorem the_contact_zone :
    (∀ {V S Op : Type} (H : History V S Op) (x y b₁ b₂ : V),
        ValidInHistory H x y (.selected b₁) → ValidInHistory H x y (.selected b₂) →
          b₁ = b₂)
      ∧ (∀ b : Ver, ¬ ValidInHistory ccHistory .mergeL .mergeR (.selected b))
      ∧ ((MergeModel.BaseDecision.selected (3 : Nat)).Valid (spendOps 2).impl 3 3
        ∧ ∀ v, CommonAncestor ccDag .mergeL .mergeR v → ccState v ≠ 3)
      ∧ ((MergeModel.BaseDecision.unavailable (S := Nat)).Valid (spendOps 2).impl
          (ccState .joinLeft) (ccState .joinRight)
        ∧ CommonAncestor ccDag .joinLeft .joinRight .mergeL)
      ∧ (∀ x y : Ver, ¬ ValidInHistory ccHistory x y .unavailable)
      ∧ ((RunRealized linHistory (spendOps 2).impl
            ∧ ¬ MergeClosedFrom counterAM (spendOps 2).impl 0)
        ∧ (MergeClosedFrom resetAM (spendOps 5).impl 0
            ∧ ¬ RunRealized resetHistory (spendOps 5).impl))
      ∧ (MergeModel.IConfluentIn
          (MergeModel.DecisionKey counterAM (spendOps 2).impl joinResolve)
          (fun n : Nat => n ≤ 4)
        ∧ ¬ (ccState .joinLeft ≤ 4))
      ∧ (BasedCertSound wBased .quiesced stateKeyed
        ∧ ¬ BasedCertSound wBased .start stateKeyed) :=
  ⟨fun _ _ _ _ _ h₁ h₂ => selected_unique h₁ h₂,
   no_version_is_selectable_here,
   ⟨state_validity_is_not_dag_ancestry.1, state_validity_is_not_dag_ancestry.2⟩,
   state_unavailable_fires_where_the_dag_hands_a_base,
   cc_never_unavailable,
   ⟨⟨linHistory_runRealized, counter_not_mergeClosed⟩,
    ⟨reset_mergeClosed, resetHistory_not_runRealized⟩⟩,
   ⟨counter_decision_iconfluentIn, by decide⟩,
   ⟨stateKeyed_sound_at_its_base, stateKeyed_unsound_at_the_root⟩⟩

end Uwueave.HistoryBase
