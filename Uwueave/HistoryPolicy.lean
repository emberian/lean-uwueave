/-
# Uwueave.HistoryPolicy — the base-selection procedure is part of the model.

## Why this file exists

`Histories.lean` and `HistoryBase.lean` answer *what a merge-base procedure may
honestly return* and *what the version DAG licenses*. Neither of them ever
**declares a procedure**. `History.Coherent` reads the base a merge node happens
to record (`Origin.merged base left right`) and asks only that it be *a* common
ancestor; §6's `base_accident_decides_the_invariant` then shows two equally
licensed records — one legal, one illegal — for the same two versions, and the
file has nowhere to put the fact that a *deployment* would have picked one of
them by a rule.

codex's review named the gap and the shape of the repair: the selection procedure
must be a field of the declared merge model, not something hidden behind
`AncestralMerge.merge3`'s first argument. `HistoryMerge` (§1) is that structure —
`select`, `reconcile`, `scope`, `selectSound` — and the four judgements are asked
of it.

## The four judgements, up front

  * **`BaseRobust`** (§3) — *every* history-valid base gives a legal and
    contextually equivalent output. It never mentions `select`: it is a property
    of the merge kernel and the DAG alone. The lock **satisfies** it at its
    ambiguous pair (`lock_baseRobust`, whose seed is
    `Histories.lock_join_base_insensitive`); the counter **refutes** it at its
    ambiguous pair (`counter_not_baseRobust`, whose content is
    `Histories.base_accident_decides_the_invariant`). `baseRobustAt_of_lowest`
    proves the judgement is free wherever a lowest common base exists — all of
    its content sits at ambiguous pairs.

  * **`SelectorSafe`** (§4) — the *particular* declared procedure always produces
    a legal output. Genuinely weaker: `ccPickRight` and `ccExplicit` are
    selector-safe on a history where base robustness **fails**
    (`selectorSafe_does_not_imply_baseRobust`). Sharper still,
    `safety_is_selector_relative`: two policies differing only in the **order**
    in which they name the two equally-licensed maximal bases — both
    `selectSound` — land on `4` and on `5` against a ceiling of `4`.

  * **`AmbiguityExplicit`** (§5) — on an ambiguous decision the result records the
    decision (`Decided.under`) and its state is a *declared conflict value*, a
    function of the two replicas alone. So no base is exercised: the state does
    not depend on which bases were named. `ccExplicit` satisfies it; `ccPickLeft`
    refutes it, and the refutation is `5 ≠ 4` again.

  * **`HistoryConvergent`** (§7) — two derivations over the same append-only
    record produce the same view at every version. Satisfiable
    (`recordDetermined_converges`, for every policy whose selector reads the
    record); refutable (`nosy_diverges`, for a selector that reads a *recorded
    merge result*).

## The crown — a derived view, and the first convergence result here

`Histories.lean` says in its own non-claims that **convergence is not proved
anywhere in it**, and both witnesses it offers against convergence survive into
this file. §7 nonetheless lands one, by taking codex's architecture literally:
replicate the append-only record, and *derive* the merge view from it.

`derive`/`viewOf` (§7.1) recompute a merge node's state from the record — the two
parents' derived states and the **policy's** base decision — deliberately
ignoring the base and the state the node recorded. Then

  * `recordDetermined_converges` — same DAG, same origin shapes, same states at
    non-merge nodes, same policy ⇒ **same view at every version**, even though
    the two records disagree at every merge node they contain;
  * `viewOf_eq_state` — the derivation is *complete*, not a truncation: on a
    coherent history whose merges the policy itself generated, the derived view
    reproduces the record (`lock_view_is_the_record` checks it on a real one);
  * `derived_view_repairs_the_base_accident` — on the criss-cross the recorded
    `joinLeft` holds `5`, over a ceiling of `4`, and the derived view under an
    ambiguity-explicit policy holds `3`. The accident is a property of the
    *record*; the derived view does not have it.
  * `ccHistory_not_policyGenerated` — and that record is **no policy's record at
    all**: `joinLeft` and `joinRight` merge the same pair and disagree, while a
    policy is a function of the pair. The criss-cross is what a version store
    without a declared selector can build, and nothing with one can.

**The obstruction, characterized** (§8). `Histories.swap_never_converges` is the
policy class that must be excluded, and the exclusion is exact: the swap is two
replicas running one rule — *take my own tip as the base* — on the pair presented
in **opposite orders**. That is `¬ SelectorSymmetric`, and `SelectorSymmetric` is
precisely what `replicas_agree_on_order` needs. The same law one layer down is
`Recoverable.SymmetricChooser.symm`, forced there by `AncestralMerge.comm`
(`Recoverable.comm_forces_symmetric_chooser`); nothing had stated it for the
*base procedure*. The second excluded class is `¬ RecordDetermined` — a selector
that consults a merge **result** rather than the record — and `nosy_diverges` is
its witness.

## The TRANSPORTS row this file owes

> **One-shot merge safety → history convergence** ✗ **REFUTED**, ⚠ repaired
> *transport* `HistoryPolicy.recordDetermined_converges` — same record + same
> policy ⇒ same derived view · *needs* the selector to read the **record**
> (`RecordDetermined`) · *without it* `HistoryPolicy.nosy_diverges` consults a
> recorded merge result and separates two otherwise-identical records. Pair
> symmetry is a distinct, one-step order-agreement judgement:
> `replicas_agree_on_order` needs `SelectorSymmetric` and
> `ReconcileSymmetric`; `Histories.swap_never_converges` witnesses why that
> separate law matters. ⚠ *what the version level already does* the swap's
> self-base decisions are **refused** by `HistoryBase.ValidInHistory`
> (`the_self_base_policy_is_not_history_licensed`), so the state-level and
> history-level licences disagree about exactly this policy.

## Non-claims

⟨TERMINAL⟩ = a theorem of this model; ⟨UNDONE U-0074⟩ = work wearing a caveat's clothes.

  * ⟨TERMINAL⟩ **`HistoryConvergent` is convergence of a derived function, not of
    a protocol.** Its two "replicas" are two derivations over records that
    already agree on the append-only part. Nothing here makes replicas *reach*
    the same record: there is no delivery model in this file, and
    `HistoryBase`'s `BasedWorld`/`ExtensionRealized` is where that question
    lives.
  * ⟨TERMINAL⟩ **The derived view does not replay operations.** A `ran` node's
    state is part of the record and is read, not recomputed; only merge nodes are
    derived. That is what makes `SameRecord`'s `states` clause the right
    hypothesis, and it is why `derive` needs no `Impl` at all.
  * ⟨TERMINAL⟩ **`scope` is a hiding place, and it is named as one.**
    `any_selector_has_a_sound_policy` proves *every* selector has a
    `selectSound` policy — declare the empty scope. Each witness therefore proves
    its scope contains the pair its judgement is asked at.
  * ⟨UNDONE U-0075, narrowed to automatic semantic decision synthesis⟩ **Declared
    policy decisions and higher judgements are now swept.** Downstream
    `HistoryEngine.semanticSweep` evaluates `HistoryMerge.select` and `apply`
    over every ordered pair of an explicitly enumerated history, returning
    selected/ambiguous/unavailable evidence inside scope and a proved refusal
    outside it. `SemanticDecision.graph_kind_eq` proves agreement with finite
    DAG classification on every claimed pair. `HistoryRuntime.higherSweep`
    now retains proof-carrying `BaseRobustAt` and pairwise `SelectorSafe`
    decisions for every ordered pair, while `classifyHigher` retains the
    whole-policy judgements. Their semantic decision procedures are explicit
    inputs; automatically synthesizing them, and tying `HistoryConvergent` to
    an authenticated/out-of-order delivery protocol, remain open.
  * ⟨UNDONE U-0076, narrowed to unrestricted selection and kernel synthesis⟩ **A
    total finite selector is now computed from a covered DAG.** Downstream
    `HistoryEngine.decidePair` performs proof-carrying four-way search under an
    explicit finite enumeration and computes selected, ambiguous, unavailable,
    or exact refusal evidence. `semanticSweep` applies an already-declared
    policy and refuses pairs outside its scope. `HistoryRuntime.finiteExplicit`
    eliminates refusal and supplies an all-pairs `HistoryMerge.select` and
    scope from an explicit finite enumeration, caller-provided reconciliation
    kernel, and conflict function. Discovering coverage for unrestricted DAGs
    and synthesizing those semantic reconciliation inputs remain open.
  * ⟨DONE⟩ **`SelectorSymmetric` is sufficient but not unconditionally
    necessary.** `HistoryRuntime.asymmetric_but_convergent` is the missing
    counterexample, while `orderAgreement_iff_selector_symmetric_at` gives the
    exact necessity theorem under named reconcile-symmetry and
    decision-separation premises.
  * ⟨DONE downstream at independent universes⟩ **History policies are
    universe-generic.** `HistoryMerge`, its recorded-decision law, and the
    record-determined convergence theorem retain independent version, state,
    operation, and observation levels.  The downstream closure probe exercises
    those laws at mixed `Type 0`/`Type 1`/lifted carriers.

Literature: as `Histories.lean` — Kaki et al. (MRDT, OOPSLA 2019) for the
version-store/LCA model, Sal 2026 §2 for the counter, Bailis et al. (VLDB 2015)
for I-confluence; the derived-view discipline is the tree's own
(`Move.derived_view_sec`).
-/
import Uwueave.HistoryBase
import Uwueave.Recoverable

namespace Uwueave.HistoryPolicy

open Uwueave Uwueave.Ancestral Uwueave.Necessity Uwueave.Histories Uwueave.HistoryBase

universe uV uS uOp uR

/-! ## §0. Two symmetries the base layer never needed

`Histories.CommonAncestor.symm` exists; the two derived notions did not, and
every pair-symmetric statement below needs them. -/

/-- A maximal common base does not care which replica is which. (Named without a
dot, because `MaximalCommonBase` unfolds to `And` and dot notation would find
`And.symm`.) -/
theorem maximalCommonBase_symm {V : Type uV} {D : VersionDag V} {x y b : V}
    (h : MaximalCommonBase D x y b) : MaximalCommonBase D y x b :=
  ⟨h.1.symm, fun c hc hbc => h.2 c hc.symm hbc⟩

/-- …and neither does a lowest one. -/
theorem lowestCommonBase_symm {V : Type uV} {D : VersionDag V} {x y b : V}
    (h : LowestCommonBase D x y b) : LowestCommonBase D y x b :=
  ⟨h.1.symm, fun c hc => h.2 c hc.symm⟩

/-- Equal outputs are contextually equivalent — the shape every base-insensitivity
witness below lands in. -/
theorem ctxEquiv_of_eq {S : Type uS} {R : Type uR} [MergeState S] {f : S → R} {u v : S} (h : u = v) :
    CtxEquiv f u v := h ▸ ctxEquiv_refl f u

/-! ## §1. The declared merge model

codex's shape, with one rename: the field he calls `merge` is `reconcile` here,
because `merge` is `MergeState`'s exported join and the two would shadow. The
point of the structure is unchanged and is the whole reason it exists —
**`select` is a field**. A merge model that hides its base procedure inside
`AncestralMerge.merge3`'s first argument cannot state any of §3–§5. -/

/-- Read a version-level decision through **any** labelling of versions by
states. `HistoryBase.stateDecision` is the instance at `H.state`
(`stateDecisionOf_state`); §7 needs the general form, where the labelling is the
*derived* view rather than the recorded one. -/
def stateDecisionOf {V : Type uV} {S : Type uS} (f : V → S) :
    MergeModel.BaseDecision V → MergeModel.BaseDecision S
  | .selected b => .selected (f b)
  | .ambiguous b₁ b₂ => .ambiguous (f b₁) (f b₂)
  | .unavailable => .unavailable

/-- `HistoryBase.stateDecision` is `stateDecisionOf` at the recorded labelling. -/
theorem stateDecisionOf_state {V : Type uV} {S : Type uS} {Op : Type uOp} (H : History V S Op)
    (d : MergeModel.BaseDecision V) : stateDecisionOf H.state d = stateDecision H d := by
  cases d <;> rfl

/-- Two labellings that agree on the versions a decision **names** give the same
state-level decision. The hypothesis is over `MergeModel.BaseDecision.bases`,
which is `MergeModel`'s own account of what a decision exposes. -/
theorem stateDecisionOf_congr {V : Type uV} {S : Type uS} {f g : V → S}
    (d : MergeModel.BaseDecision V) (h : ∀ b, b ∈ d.bases → f b = g b) :
    stateDecisionOf f d = stateDecisionOf g d := by
  cases d with
  | selected b => rw [stateDecisionOf, stateDecisionOf, h b (List.Mem.head _)]
  | ambiguous b₁ b₂ =>
      rw [stateDecisionOf, stateDecisionOf, h b₁ (List.Mem.head _),
        h b₂ (List.Mem.tail _ (List.Mem.head _))]
  | unavailable => rfl

/-- **A history merge policy.** The base-selection procedure is a *field*, and it
carries an obligation.

  * `kernel` — the three-way merge, with `AncestralMerge`'s two laws;
  * `select` — the merge-base procedure, over **versions**, returning
    `MergeModel.BaseDecision V`: the raw three-valued answer;
  * `reconcile` — the merge proper, reading the decision with its bases resolved
    to states, and returning `MergeModel.Decided S` so the decision travels with
    the result;
  * `scope` — the pairs the procedure claims to answer;
  * `selectSound` — ⚑ **the obligation**: inside its scope the answer is licensed
    by the version DAG (`HistoryBase.ValidInHistory`);
  * `records`, `reconcileSelected` — the two laws that stop `reconcile` from
    being an arbitrary function: it records what it was given, and with a
    selected base it *is* the kernel. The ambiguous and unavailable branches are
    deliberately free — that freedom is exactly what §5 judges.

Why `MergeModel.BaseDecision V` and not `Histories.BaseSelection`: the latter
fuses the answer with its proof, which would make `selectSound` vacuous and
`select` uninhabitable on a DAG with no honest answer. `ofBaseSelection` (below)
shows the two shapes carry the same content. -/
structure HistoryMerge (V : Type uV) (S : Type uS) (Op : Type uOp) where
  /-- The three-way merge kernel. -/
  kernel : AncestralMerge S
  /-- The merge-base procedure — a declared field, not an implicit argument. -/
  select : History V S Op → V → V → MergeModel.BaseDecision V
  /-- The merge proper, under a decision whose bases are read as states. -/
  reconcile : MergeModel.BaseDecision S → S → S → MergeModel.Decided S
  /-- The pairs the procedure claims. -/
  scope : History V S Op → V → V → Prop
  /-- Inside the scope, the answer is licensed by the version DAG. -/
  selectSound : ∀ H x y, scope H x y → ValidInHistory H x y (select H x y)
  /-- The result records the decision it was made under and the two replicas. -/
  records : ∀ d u v, (reconcile d u v).under = d ∧ (reconcile d u v).left = u
    ∧ (reconcile d u v).right = v
  /-- With a selected base the merge is the kernel's. -/
  reconcileSelected : ∀ l u v, (reconcile (.selected l) u v).state = kernel.merge3 l u v

/-- The state-level decision the policy works under at a pair. -/
def HistoryMerge.decisionAt {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op)
    (H : History V S Op) (x y : V) : MergeModel.BaseDecision S :=
  stateDecision H (P.select H x y)

/-- The policy's answer at a pair, with its decision attached. -/
def HistoryMerge.apply {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op)
    (H : History V S Op) (x y : V) : MergeModel.Decided S :=
  P.reconcile (P.decisionAt H x y) (H.state x) (H.state y)

/-- The state the policy produces at a pair. -/
def HistoryMerge.result {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op)
    (H : History V S Op) (x y : V) : S := (P.apply H x y).state

/-- **Every policy's result records its decision** — `records`, at `apply`. This
is the half of "ambiguity is explicit" that the structure gives away for free;
§5 judges the half it does not. -/
theorem apply_under {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) (H : History V S Op)
    (x y : V) : (P.apply H x y).under = P.decisionAt H x y := (P.records _ _ _).1

/-- `Histories.BaseSelection`'s proof-carrying answer, split into the raw answer
`select` returns… -/
def ofBaseSelection {V : Type uV} {S : Type uS} {Op : Type uOp} (H : History V S Op) {x y : V} :
    BaseSelection H.dag x y → MergeModel.BaseDecision V
  | .selected b _ => .selected b
  | .ambiguous b₁ b₂ _ _ _ => .ambiguous b₁ b₂
  | .unavailable _ => .unavailable

/-- …and the obligation `selectSound` states. So the two shapes carry the same
content, and the structure's split is a split of one object rather than a
weakening. -/
theorem ofBaseSelection_valid {V : Type uV} {S : Type uS} {Op : Type uOp} (H : History V S Op) {x y : V}
    (s : BaseSelection H.dag x y) : ValidInHistory H x y (ofBaseSelection H s) := by
  cases s with
  | selected b h => exact h
  | ambiguous b₁ b₂ h₁ h₂ hne => exact ⟨h₁, h₂, hne⟩
  | unavailable h => exact h

/-! ### §1.1 Two ready-made reconcilers, differing in one branch

`MergeModel.decidedMerge` is already the ambiguity-explicit shape: on two bases
or none it calls a *declared* conflict policy on the two replicas. `pickMerge` is
the same function with one branch changed — on two bases it **exercises the first
one**. Every §5 witness is one of these two, so the judgement isolates the branch
and nothing else. -/

/-- The ambiguity-explicit policy over a kernel and a declared conflict value.
`MergeModel.decidedMerge` does the work; what is added is the selector. -/
def explicit {V : Type uV} {S : Type uS} {Op : Type uOp} (M : AncestralMerge S) (conflict : S → S → S)
    (sel : History V S Op → V → V → MergeModel.BaseDecision V)
    (sc : History V S Op → V → V → Prop)
    (hs : ∀ H x y, sc H x y → ValidInHistory H x y (sel H x y)) : HistoryMerge V S Op where
  kernel := M
  select := sel
  reconcile := MergeModel.decidedMerge M conflict
  scope := sc
  selectSound := hs
  records := by intro d u v; cases d <;> exact ⟨rfl, rfl, rfl⟩
  reconcileSelected := by intro l u v; rfl

/-- ⚠ **The base-picking reconciler.** Identical to `MergeModel.decidedMerge`
except on `ambiguous`, where it merges against the **first** base named instead of
calling the conflict policy. This is the procedure `Histories` §6 describes in
prose — "a replica that must nonetheless merge picks one" — written down. -/
def pickMerge {S : Type uS} (M : AncestralMerge S) (conflict : S → S → S) :
    MergeModel.BaseDecision S → S → S → MergeModel.Decided S
  | .selected l, u, v => ⟨M.merge3 l u v, .selected l, u, v⟩
  | .ambiguous b₁ b₂, u, v => ⟨M.merge3 b₁ u v, .ambiguous b₁ b₂, u, v⟩
  | .unavailable, u, v => ⟨conflict u v, .unavailable, u, v⟩

/-- The base-picking policy. -/
def picking {V : Type uV} {S : Type uS} {Op : Type uOp} (M : AncestralMerge S) (conflict : S → S → S)
    (sel : History V S Op → V → V → MergeModel.BaseDecision V)
    (sc : History V S Op → V → V → Prop)
    (hs : ∀ H x y, sc H x y → ValidInHistory H x y (sel H x y)) : HistoryMerge V S Op where
  kernel := M
  select := sel
  reconcile := pickMerge M conflict
  scope := sc
  selectSound := hs
  records := by intro d u v; cases d <;> exact ⟨rfl, rfl, rfl⟩
  reconcileSelected := by intro l u v; rfl

/-- ⚠ **`scope` is where a policy can hide.** For *any* selector whatsoever there
is a `HistoryMerge` carrying it: declare the empty scope and `selectSound` is
discharged by `False.elim`. So `selectSound` on its own certifies nothing. Every
judgement below quantifies over `scope`, and every witness policy proves its scope
**contains the pair the judgement is asked at** (`ccScope_answers`,
`lvScope_answers`). -/
theorem any_selector_has_a_sound_policy {V : Type uV} {S : Type uS} {Op : Type uOp} (M : AncestralMerge S)
    (conflict : S → S → S) (sel : History V S Op → V → V → MergeModel.BaseDecision V) :
    ∃ P : HistoryMerge V S Op, P.select = sel ∧ ∀ H x y, ¬ P.scope H x y :=
  ⟨explicit M conflict sel (fun _ _ _ => False) (fun _ _ _ h => h.elim), rfl,
   fun _ _ _ h => h⟩

/-! ## §2. What a licensed answer may name

One lemma, used by every implication in §6: a decision the history licenses names
only **maximal common bases**. That is what makes `BaseRobust` (a condition on
*all* history-valid bases) an upper bound for `SelectorSafe` (a condition on the
one the procedure returned). -/

/-- **Every base a licensed decision names is a maximal common base.** `selected`
names a lowest one (`Histories.LowestCommonBase.maximal`), `ambiguous` names two
maximal ones by definition, and `unavailable` names none. -/
theorem validInHistory_bases_are_maximal {V : Type uV} {S : Type uS} {Op : Type uOp} {H : History V S Op}
    {x y : V} {d : MergeModel.BaseDecision V} (h : ValidInHistory H x y d) :
    ∀ b, b ∈ d.bases → MaximalCommonBase H.dag x y b := by
  cases d with
  | selected b =>
      intro c hc
      cases hc with
      | head => exact h.maximal
      | tail _ hx => cases hx
  | ambiguous b₁ b₂ =>
      intro c hc
      cases hc with
      | head => exact h.1
      | tail _ hx =>
        cases hx with
        | head => exact h.2.1
        | tail _ hy => cases hy
  | unavailable => intro c hc; cases hc

/-- **Inside a coherent history a licensed selector never answers
`unavailable`** — `HistoryBase.coherent_never_unavailable`, read as a fact about
procedures: the third case is not "I looked and found nothing", so a policy that
returns it inside its scope is unsound by construction. -/
theorem scope_never_unavailable {V : Type uV} {S : Type uS} {Op : Type uOp} {P : HistoryMerge V S Op}
    {H : History V S Op} {M : AncestralMerge S} {impl : Impl S Op}
    (hco : H.Coherent M impl) {x y : V} (hsc : P.scope H x y) :
    P.select H x y ≠ .unavailable := by
  intro hu
  exact coherent_never_unavailable hco x y (hu ▸ P.selectSound H x y hsc)

/-! ## §3. `BaseRobust` — the judgement that does not mention the selector

"Every history-valid base gives a legal, contextually equivalent output."
*History-valid* is §2's answer: a maximal common base. *Contextually equivalent*
is `MinimalSummary.CtxEquiv`, reused rather than reinvented — two outputs no
future gossip can tell apart for the query `f`. -/

/-- **Base robustness at a pair.** Every maximal common base of `x` and `y` gives
a legal output, and any two of them give contextually equivalent ones. Note what
is absent: `P.select`. This judgement is about the kernel and the DAG. -/
def BaseRobustAt {V : Type uV} {S : Type uS} {Op : Type uOp} {R : Type uR} [MergeState S] (P : HistoryMerge V S Op)
    (H : History V S Op) (I : Invariant S) (f : S → R) (x y : V) : Prop :=
  ∀ b₁ b₂ : V, MaximalCommonBase H.dag x y b₁ → MaximalCommonBase H.dag x y b₂ →
    I (H.state x) → I (H.state y) →
      I (P.kernel.merge3 (H.state b₁) (H.state x) (H.state y))
        ∧ CtxEquiv f (P.kernel.merge3 (H.state b₁) (H.state x) (H.state y))
            (P.kernel.merge3 (H.state b₂) (H.state x) (H.state y))

/-- Base robustness over the pairs the policy claims. -/
def BaseRobust {V : Type uV} {S : Type uS} {Op : Type uOp} {R : Type uR} [MergeState S] (P : HistoryMerge V S Op)
    (H : History V S Op) (I : Invariant S) (f : S → R) : Prop :=
  ∀ x y, P.scope H x y → BaseRobustAt P H I f x y

/-- **All of the judgement's content sits at ambiguous pairs.** Where a lowest
common base exists it is the *only* maximal one
(`Histories.lowestCommonBase_unique` in the form the maximality condition gives),
so robustness reduces to a single legality obligation and the contextual
equivalence is reflexivity. -/
theorem baseRobustAt_of_lowest {V : Type uV} {S : Type uS} {Op : Type uOp} {R : Type uR} [MergeState S]
    (P : HistoryMerge V S Op) (H : History V S Op) (I : Invariant S) (f : S → R)
    {x y b₀ : V} (hlow : LowestCommonBase H.dag x y b₀)
    (hleg : I (H.state x) → I (H.state y) →
      I (P.kernel.merge3 (H.state b₀) (H.state x) (H.state y))) :
    BaseRobustAt P H I f x y := by
  intro b₁ b₂ h₁ h₂ hx hy
  have e₁ : b₀ = b₁ := h₁.2 b₀ hlow.1 (hlow.2 b₁ h₁.1)
  have e₂ : b₀ = b₂ := h₂.2 b₀ hlow.1 (hlow.2 b₂ h₂.1)
  subst e₁
  subst e₂
  exact ⟨hleg hx hy, ctxEquiv_refl _ _⟩

/-! ## §4. The witnesses — two histories, four policies

The criss-cross of `Histories` §3 and the lock history of §7.2, with selectors
written down and proved sound. Both scopes are the pair whose base decision is
genuinely ambiguous, in both orders. -/

/-- Every version of the criss-cross is reached by its root. -/
theorem cc_root_reaches (v : Ver) : Reaches ccDag .root v := by
  have hl : Ancestry ccDag .root .left := Ancestry.direct (by decide)
  have hr : Ancestry ccDag .root .right := Ancestry.direct (by decide)
  have hml : Ancestry ccDag .root .mergeL := Ancestry.extend hl (by decide)
  have hmr : Ancestry ccDag .root .mergeR := Ancestry.extend hl (by decide)
  have hjl : Ancestry ccDag .root .joinLeft := Ancestry.extend hml (by decide)
  have hjr : Ancestry ccDag .root .joinRight := Ancestry.extend hml (by decide)
  cases v
  · exact Reaches.refl _ _
  · exact Or.inr hl
  · exact Or.inr hr
  · exact Or.inr hml
  · exact Or.inr hmr
  · exact Or.inr hjl
  · exact Or.inr hjr

/-- Every version of the lock history is reached by its root. -/
theorem lv_root_reaches (v : LVer) : Reaches lvDag .root v := by
  have ha : Ancestry lvDag .root .alice := Ancestry.direct (by decide)
  have hb : Ancestry lvDag .root .bob := Ancestry.direct (by decide)
  have h1 : Ancestry lvDag .root .m1 := Ancestry.extend ha (by decide)
  have h2 : Ancestry lvDag .root .m2 := Ancestry.extend ha (by decide)
  have hj : Ancestry lvDag .root .j := Ancestry.extend h1 (by decide)
  cases v
  · exact Reaches.refl _ _
  · exact Or.inr ha
  · exact Or.inr hb
  · exact Or.inr h1
  · exact Or.inr h2
  · exact Or.inr hj

/-- The criss-cross selector, naming `left` first. Symmetric in the pair by
construction; outside the ambiguous pair it answers with the fork point, which
`cc_root_reaches` makes an ancestor of everything (§7 needs that; soundness of
*that* answer is claimed only inside `ccScope`). -/
def ccSelectLR (_ : History Ver Nat Unit) : Ver → Ver → MergeModel.BaseDecision Ver
  | .mergeL, .mergeR => .ambiguous .left .right
  | .mergeR, .mergeL => .ambiguous .left .right
  | _, _ => .selected .root

/-- The same selector naming `right` first. Both orders are licensed — `left` and
`right` are maximal common bases and neither is lower — so the two selectors are
equally sound, which is the whole of `safety_is_selector_relative`. -/
def ccSelectRL (_ : History Ver Nat Unit) : Ver → Ver → MergeModel.BaseDecision Ver
  | .mergeL, .mergeR => .ambiguous .right .left
  | .mergeR, .mergeL => .ambiguous .right .left
  | _, _ => .selected .root

/-- The scope: the ambiguous pair of any history built over `ccDag`. Pinning the
DAG rather than a particular history is what makes `selectSound` provable without
naming the labelling. -/
def ccScope (H : History Ver Nat Unit) (x y : Ver) : Prop :=
  H.dag = ccDag ∧ ((x = .mergeL ∧ y = .mergeR) ∨ (x = .mergeR ∧ y = .mergeL))

/-- `ccSelectLR` is sound on `ccScope` — `Histories.cc_left_maximal` and
`cc_right_maximal` are the whole proof. -/
theorem ccSelectLR_sound : ∀ H x y, ccScope H x y →
    ValidInHistory H x y (ccSelectLR H x y) := by
  rintro H x y ⟨hd, hxy | hxy⟩ <;> obtain ⟨rfl, rfl⟩ := hxy
  · show MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [hd]
    exact ⟨cc_left_maximal, cc_right_maximal, by decide⟩
  · show MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [hd]
    exact ⟨maximalCommonBase_symm cc_left_maximal, maximalCommonBase_symm cc_right_maximal, by decide⟩

/-- …and so is `ccSelectRL`, on the same scope. -/
theorem ccSelectRL_sound : ∀ H x y, ccScope H x y →
    ValidInHistory H x y (ccSelectRL H x y) := by
  rintro H x y ⟨hd, hxy | hxy⟩ <;> obtain ⟨rfl, rfl⟩ := hxy
  · show MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [hd]
    exact ⟨cc_right_maximal, cc_left_maximal, by decide⟩
  · show MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [hd]
    exact ⟨maximalCommonBase_symm cc_right_maximal, maximalCommonBase_symm cc_left_maximal, by decide⟩

/-- The scope is inhabited by the history the judgements are asked of. -/
theorem ccScope_answers : ccScope ccHistory .mergeL .mergeR :=
  ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- The **ambiguity-explicit** counter policy: honest `ambiguous`, and a declared
conflict value (`Nat.max`, the tree's own join on `Nat`) that names no base. -/
def ccExplicit : HistoryMerge Ver Nat Unit :=
  explicit counterAM (fun u v => Nat.max u v) ccSelectLR ccScope ccSelectLR_sound

/-- ⚠ The **base-picking** counter policy, naming `left` first: it exercises a
base the DAG does not prefer. -/
def ccPickLeft : HistoryMerge Ver Nat Unit :=
  picking counterAM (fun u v => Nat.max u v) ccSelectLR ccScope ccSelectLR_sound

/-- The same policy naming `right` first — equally sound, and safe where the
other is not. -/
def ccPickRight : HistoryMerge Ver Nat Unit :=
  picking counterAM (fun u v => Nat.max u v) ccSelectRL ccScope ccSelectRL_sound

/-- The lock selector: the two maximal bases of the lock history's merge pair. -/
def lvSelect (_ : History LVer Lock LockOp) : LVer → LVer → MergeModel.BaseDecision LVer
  | .m1, .m2 => .ambiguous .alice .bob
  | .m2, .m1 => .ambiguous .alice .bob
  | _, _ => .selected .root

/-- The lock scope. -/
def lvScope (H : History LVer Lock LockOp) (x y : LVer) : Prop :=
  H.dag = lvDag ∧ ((x = .m1 ∧ y = .m2) ∨ (x = .m2 ∧ y = .m1))

/-- `lvSelect` is sound on `lvScope` — `Histories.lv_alice_maximal` and
`lv_bob_maximal`. -/
theorem lvSelect_sound : ∀ H x y, lvScope H x y →
    ValidInHistory H x y (lvSelect H x y) := by
  rintro H x y ⟨hd, hxy | hxy⟩ <;> obtain ⟨rfl, rfl⟩ := hxy
  · show MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [hd]
    exact ⟨lv_alice_maximal, lv_bob_maximal, by decide⟩
  · show MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [hd]
    exact ⟨maximalCommonBase_symm lv_alice_maximal, maximalCommonBase_symm lv_bob_maximal, by decide⟩

/-- The lock scope is inhabited by the lock history. -/
theorem lvScope_answers : lvScope lockHistory .m1 .m2 := ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- The ambiguity-explicit lock policy; the conflict value is `lockPriority`,
which `Ancestral.lockPriority_atMostOne` keeps legal. -/
def lvExplicit : HistoryMerge LVer Lock LockOp :=
  explicit lockAM lockPriority lvSelect lvScope lvSelect_sound

/-- The base-picking lock policy. -/
def lvPick : HistoryMerge LVer Lock LockOp :=
  picking lockAM lockPriority lvSelect lvScope lvSelect_sound

/-- ⚠ The lock policy with an **illegal** declared conflict value: on ambiguity
it hands the lock to both. Base-robust (the kernel is untouched) and unsafe — the
witness for row 1 of §6. -/
def lvBadConflict : HistoryMerge LVer Lock LockOp :=
  explicit lockAM (fun _ _ => (⟨true, true⟩ : Lock)) lvSelect lvScope lvSelect_sound

/-! ### §4.1 `BaseRobust`: the lock satisfies it, the counter refutes it -/

/-- The maximal common bases of the lock's two merge versions are exactly `alice`
and `bob`. `root` is excluded because `alice` lies strictly beyond it. -/
theorem lv_maximal_m1m2 {b : LVer} (h : MaximalCommonBase lvDag .m1 .m2 b) :
    b = .alice ∨ b = .bob := by
  rcases lv_commonAncestors b h.1 with rfl | rfl | rfl
  · exact absurd (h.2 .alice lv_alice_common (Or.inr (.direct (by decide)))) (by decide)
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- ⚑ **The lock is base-robust at its ambiguous pair — for every policy built on
the lock kernel.** Two maximal common bases with distinct states, a genuinely
ambiguous decision (`Histories.lock_ambiguous_valid`), and the merge does not
care: `Histories.lock_join_base_insensitive` is the cross case, and mutual
exclusion holds for either choice.

Stated over an arbitrary `P` with `P.kernel = lockAM` because §6 needs it for
three policies that differ only in what they do with the ambiguity — which is
exactly the point it makes. -/
theorem lock_baseRobustAt {R : Type uR} {P : HistoryMerge LVer Lock LockOp}
    (hk : P.kernel = lockAM) (f : Lock → R) {x y : LVer}
    (hsc : lvScope lockHistory x y) : BaseRobustAt P lockHistory AtMostOne f x y := by
  obtain ⟨_, hxy | hxy⟩ := hsc <;> obtain ⟨rfl, rfl⟩ := hxy
  · intro b₁ b₂ h₁ h₂ _ _
    rcases lv_maximal_m1m2 h₁ with rfl | rfl <;> rcases lv_maximal_m1m2 h₂ with rfl | rfl <;>
      rw [hk] <;> refine ⟨by decide, ctxEquiv_of_eq ?_⟩
    · rfl
    · exact lock_join_base_insensitive
    · exact lock_join_base_insensitive.symm
    · rfl
  · intro b₁ b₂ h₁ h₂ _ _
    rcases lv_maximal_m1m2 (maximalCommonBase_symm h₁) with rfl | rfl <;>
      rcases lv_maximal_m1m2 (maximalCommonBase_symm h₂) with rfl | rfl <;>
      rw [hk] <;> refine ⟨by decide, ctxEquiv_of_eq ?_⟩
    · rfl
    · exact lock_join_base_insensitive
    · exact lock_join_base_insensitive.symm
    · rfl

/-- The ambiguity-explicit lock policy is base-robust. -/
theorem lock_baseRobust {R : Type uR} (f : Lock → R) :
    BaseRobust lvExplicit lockHistory AtMostOne f :=
  fun _ _ hsc => lock_baseRobustAt rfl f hsc

/-- ⚠ **The two counter bases are contextually distinguishable**, for the query
that matters: `Recoverable.obs` of the ceiling separates `5` from `4` outright,
so no future gossip is needed to tell the two legitimate merges apart. -/
theorem counter_bases_not_ctxEquiv :
    ¬ CtxEquiv (Recoverable.obs (fun n : Nat => n ≤ 4)) 5 4 :=
  fun h => absurd h.1 (by decide)

/-- ⚠ **The counter refutes base robustness at its ambiguous pair** — and the
refutation *is* `Histories.base_accident_decides_the_invariant`: `left` and
`right` are both maximal common bases, the results are `5` and `4`, and the
ceiling is `4`. Both halves of the judgement fail: the legality half here, the
contextual-equivalence half in `counter_bases_not_ctxEquiv`. -/
theorem counter_not_baseRobust {R : Type uR} (f : Nat → R) :
    ¬ BaseRobust ccExplicit ccHistory (fun n => n ≤ 4) f := by
  intro h
  obtain ⟨hml, hmr, _, _, h5, _, hno, _⟩ := base_accident_decides_the_invariant
  have hb : counterAM.merge3 (ccState .left) (ccState .mergeL) (ccState .mergeR) ≤ 4 :=
    (h .mergeL .mergeR ccScope_answers .left .right hml hmr (by decide) (by decide)).1
  rw [h5] at hb
  exact hno hb

/-- **The criss-cross's *first* round is base-robust, and for free.** `root` is
the lowest common base of the two branches (`Histories.cc_root_lowest`), so
`baseRobustAt_of_lowest` applies and the only obligation left is that
`counterMerge 0 1 2 = 3` is under the ceiling. Set beside
`counter_not_baseRobust`: the same history, the same kernel, and the judgement
turns over exactly when the base decision becomes ambiguous. -/
theorem cc_first_round_baseRobust {R : Type uR} (f : Nat → R) :
    BaseRobustAt ccExplicit ccHistory (fun n => n ≤ 4) f .left .right :=
  baseRobustAt_of_lowest ccExplicit ccHistory (fun n => n ≤ 4) f cc_root_lowest
    (fun _ _ => by decide)

/-! ### §4.2 `SelectorSafe`, and the separation codex asked for -/

/-- **Selector safety**: the policy's own answer, on the pairs it claims, is
legal. The difference from `BaseRobust` is exactly one quantifier — over *the
base the procedure returned* rather than over every base the DAG licenses. -/
def SelectorSafe {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) (H : History V S Op)
    (I : Invariant S) : Prop :=
  ∀ x y, P.scope H x y → I (H.state x) → I (H.state y) → I (P.result H x y)

/-- **The ambiguity-explicit counter policy is selector-safe.** On the ambiguous
pair it returns the declared conflict value `Nat.max 3 3 = 3`, under the ceiling.

The honest reading: this is not a repair of the merge. `counterMerge` still
escalates against either base; the policy simply never asks it to, because the
decision is ambiguous and the conflict value is declared. -/
theorem ccExplicit_selectorSafe :
    SelectorSafe ccExplicit ccHistory (fun n => n ≤ 4) := by
  rintro x y ⟨_, hxy | hxy⟩ _ _ <;> obtain ⟨rfl, rfl⟩ := hxy <;> decide

/-- **…and so is the base-picking policy that names `right` first**, for a
completely different reason: it *does* merge against a base, and that base's
state is `2`, so `counterMerge 2 3 3 = 4` lands on the ceiling.

⚠ Say what the choice rests on. Nothing in the DAG prefers `right`:
`cc_left_maximal` and `cc_right_maximal` are the same theorem twice. The
preference is knowledge about `counterMerge` — a higher base credits less
spending — and that is precisely why this is *selector* safety and not base
robustness. -/
theorem ccPickRight_selectorSafe :
    SelectorSafe ccPickRight ccHistory (fun n => n ≤ 4) := by
  rintro x y ⟨_, hxy | hxy⟩ _ _ <;> obtain ⟨rfl, rfl⟩ := hxy <;> decide

/-- ⚠ **…and the policy that names `left` first is not.** Same kernel, same
history, same scope, same soundness proof shape — `5` against a ceiling of `4`. -/
theorem ccPickLeft_not_selectorSafe :
    ¬ SelectorSafe ccPickLeft ccHistory (fun n => n ≤ 4) := by
  intro h
  exact absurd (h .mergeL .mergeR ccScope_answers (by decide) (by decide)) (by decide)

/-- ⚑ **Safety is selector-relative.** Two policies that differ only in the
**order** in which they name the two maximal common bases — both discharging
`selectSound` against the same DAG, both licensed by
`Histories.cc_left_maximal`/`cc_right_maximal`, neither preferred by any graph
fact — land on `4` and on `5` against a ceiling of `4`.

This is `base_accident_decides_the_invariant` moved from the *record* to the
*procedure*, which is where a deployment would meet it. -/
theorem safety_is_selector_relative :
    SelectorSafe ccPickRight ccHistory (fun n => n ≤ 4)
      ∧ ¬ SelectorSafe ccPickLeft ccHistory (fun n => n ≤ 4)
      ∧ ccPickRight.result ccHistory .mergeL .mergeR = 4
      ∧ ccPickLeft.result ccHistory .mergeL .mergeR = 5 :=
  ⟨ccPickRight_selectorSafe, ccPickLeft_not_selectorSafe, by decide, by decide⟩

/-- ⚑ **Selector safety is genuinely weaker than base robustness** — codex's
separation, on one object. `ccExplicit` is safe on the very history and pair
where base robustness fails. -/
theorem selectorSafe_does_not_imply_baseRobust :
    SelectorSafe ccExplicit ccHistory (fun n => n ≤ 4)
      ∧ ¬ BaseRobust ccExplicit ccHistory (fun n => n ≤ 4)
          (Recoverable.obs (fun n : Nat => n ≤ 4)) :=
  ⟨ccExplicit_selectorSafe, counter_not_baseRobust _⟩

/-! ## §5. `AmbiguityExplicit` — no base is exercised

"Ambiguous bases produce a stored conflict value rather than an arbitrary
choice." Two halves, and the structure supplies one of them: `records` already
makes the result carry the decision (`apply_under`). The half with content is
that the *state* is a function of the two replicas alone — so the answer does not
depend on which bases were named, which is what "no arbitrary choice" means
extensionally. -/

/-- **Ambiguity is explicit**: on an ambiguous decision the reconciled state is a
declared conflict value — a function of the two replicas — so no base is
exercised. -/
def AmbiguityExplicit {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) : Prop :=
  ∃ conflict : S → S → S,
    ∀ b₁ b₂ u v : S, (P.reconcile (.ambiguous b₁ b₂) u v).state = conflict u v

/-- **The declared-conflict policies satisfy it**, with the conflict value they
were built from. -/
theorem explicit_ambiguityExplicit {V : Type uV} {S : Type uS} {Op : Type uOp} (M : AncestralMerge S)
    (conflict : S → S → S) (sel : History V S Op → V → V → MergeModel.BaseDecision V)
    (sc : History V S Op → V → V → Prop)
    (hs : ∀ H x y, sc H x y → ValidInHistory H x y (sel H x y)) :
    AmbiguityExplicit (explicit M conflict sel sc hs) :=
  ⟨conflict, fun _ _ _ _ => rfl⟩

/-- **…and the result stores the ambiguity it was decided under**, so a reader
can tell a conflict from a reconciliation. This is `records` at `apply`; it is
free, and it is the half `MergeModel.Decided` was already shaped for. -/
theorem explicit_records_the_conflict {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op)
    (H : History V S Op) (x y : V) {b₁ b₂ : V}
    (h : P.select H x y = .ambiguous b₁ b₂) :
    (P.apply H x y).under = .ambiguous (H.state b₁) (H.state b₂) := by
  rw [apply_under, HistoryMerge.decisionAt, h]
  rfl

/-- ⚠ **The base-picking counter policy refutes it.** Its ambiguous branch merges
against the first base named, and the two bases disagree — `5` against `4`. No
function of the two replicas can be both, so the choice is not merely
undocumented: it is *observable in the output*, which is what the judgement
forbids. -/
theorem ccPickLeft_not_ambiguityExplicit : ¬ AmbiguityExplicit ccPickLeft := by
  rintro ⟨c, hc⟩
  have h1 : (5 : Nat) = c 3 3 := hc 1 2 3 3
  have h2 : (4 : Nat) = c 3 3 := hc 2 1 3 3
  exact absurd (h1.trans h2.symm) (by decide)

/-- ⚠ **…and so does the base-picking lock policy**, on the very triple that busts
the two-way join. The lock is base-*robust* at its ambiguous history pair
(`lock_baseRobust`) and still exercises a choice on other triples: the two
judgements are about different quantifiers, which §6 states as orthogonality. -/
theorem lvPick_not_ambiguityExplicit : ¬ AmbiguityExplicit lvPick := by
  rintro ⟨c, hc⟩
  have h1 : (⟨false, true⟩ : Lock) = c ⟨false, true⟩ ⟨true, false⟩ :=
    hc ⟨true, false⟩ ⟨false, true⟩ ⟨false, true⟩ ⟨true, false⟩
  have h2 : (⟨true, false⟩ : Lock) = c ⟨false, true⟩ ⟨true, false⟩ :=
    hc ⟨false, true⟩ ⟨true, false⟩ ⟨false, true⟩ ⟨true, false⟩
  exact absurd (h1.trans h2.symm) (by decide)

/-! ## §6. The four judgements against each other

Each answer is a theorem or a witness; none is prose. -/

/-- **A base-using policy**: its reconciled state is always the kernel's merge
against one of the bases the decision *names*. The `unavailable` case demands a
base that does not exist, which is why the condition is stated with
`scope_never_unavailable` beside it. -/
def BaseUsing {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) : Prop :=
  ∀ (d : MergeModel.BaseDecision S) (u v : S), d ≠ .unavailable →
    ∃ b, b ∈ d.bases ∧ (P.reconcile d u v).state = P.kernel.merge3 b u v

/-- ⚠ The guard is not decoration: `unavailable` names **no** base, so without it
`BaseUsing` would be satisfied by nothing at all and the implication below would
be vacuous. What licenses dropping the case is `scope_never_unavailable` —
inside a coherent history a licensed selector never answers it. -/
theorem picking_baseUsing {V : Type uV} {S : Type uS} {Op : Type uOp} (M : AncestralMerge S)
    (conflict : S → S → S) (sel : History V S Op → V → V → MergeModel.BaseDecision V)
    (sc : History V S Op → V → V → Prop)
    (hs : ∀ H x y, sc H x y → ValidInHistory H x y (sel H x y)) :
    BaseUsing (picking M conflict sel sc hs) := by
  intro d u v hne
  cases d with
  | selected l => exact ⟨l, List.Mem.head _, rfl⟩
  | ambiguous b₁ b₂ => exact ⟨b₁, List.Mem.head _, rfl⟩
  | unavailable => exact absurd rfl hne

/-- **Row 1, positive half. BaseRobust → SelectorSafe, for a base-using policy.**
The bases a licensed decision names are maximal common bases (§2), base
robustness covers every one of them, and a base-using policy's answer is the
kernel at one of them. The coherence hypothesis is used once, to retire the
`unavailable` case through `scope_never_unavailable`. -/
theorem baseRobust_implies_selectorSafe {V : Type uV} {S : Type uS} {Op : Type uOp} {R : Type uR} [MergeState S]
    {P : HistoryMerge V S Op} {H : History V S Op} {I : Invariant S} {f : S → R}
    {M : AncestralMerge S} {impl : Impl S Op} (hco : H.Coherent M impl)
    (hbu : BaseUsing P) (hbr : BaseRobust P H I f) : SelectorSafe P H I := by
  intro x y hsc hx hy
  have hval := P.selectSound H x y hsc
  have hnu := scope_never_unavailable hco hsc
  cases hd : P.select H x y with
  | selected c =>
      have hdec : P.decisionAt H x y = .selected (H.state c) := by
        rw [HistoryMerge.decisionAt, hd]; rfl
      obtain ⟨b, hmem, heq⟩ := hbu (P.decisionAt H x y) (H.state x) (H.state y)
        (by rw [hdec]; intro h; cases h)
      rw [hdec] at hmem
      have hb : b = H.state c := by
        cases hmem with
        | head => rfl
        | tail _ hx' => cases hx'
      have hmax : MaximalCommonBase H.dag x y c :=
        validInHistory_bases_are_maximal (hd ▸ hval) c (List.Mem.head _)
      rw [HistoryMerge.result, HistoryMerge.apply, heq, hb]
      exact (hbr x y hsc c c hmax hmax hx hy).1
  | ambiguous c₁ c₂ =>
      have hdec : P.decisionAt H x y = .ambiguous (H.state c₁) (H.state c₂) := by
        rw [HistoryMerge.decisionAt, hd]; rfl
      obtain ⟨b, hmem, heq⟩ := hbu (P.decisionAt H x y) (H.state x) (H.state y)
        (by rw [hdec]; intro h; cases h)
      rw [hdec] at hmem
      have hval' : MaximalCommonBase H.dag x y c₁ ∧ MaximalCommonBase H.dag x y c₂ :=
        ⟨validInHistory_bases_are_maximal (hd ▸ hval) c₁ (List.Mem.head _),
         validInHistory_bases_are_maximal (hd ▸ hval) c₂
           (List.Mem.tail _ (List.Mem.head _))⟩
      rw [HistoryMerge.result, HistoryMerge.apply, heq]
      cases hmem with
      | head => exact (hbr x y hsc c₁ c₁ hval'.1 hval'.1 hx hy).1
      | tail _ hx' =>
        cases hx' with
        | head => exact (hbr x y hsc c₂ c₂ hval'.2 hval'.2 hx hy).1
        | tail _ hy' => cases hy'
  | unavailable => exact absurd hd hnu

/-- ⚑ **The implication has content**: the base-picking lock policy is
selector-safe *because* the lock is base-robust — no computation on `lvPick`'s
own answer anywhere in the proof. -/
theorem lvPick_selectorSafe : SelectorSafe lvPick lockHistory AtMostOne :=
  baseRobust_implies_selectorSafe lockHistory_coherent
    (picking_baseUsing lockAM lockPriority lvSelect lvScope lvSelect_sound)
    (fun _ _ hsc => lock_baseRobustAt (P := lvPick) rfl (Recoverable.obs AtMostOne) hsc)

/-- ⚠ **Row 1, negative half. Without `BaseUsing` the implication is false.** The
lock is base-robust at its ambiguous pair and its *conflict policy* is
unconstrained by that fact: `lvBadConflict` hands the lock to both replicas.
Base robustness quantifies over bases; the ambiguous branch uses none. -/
theorem baseRobust_does_not_imply_selectorSafe {R : Type uR} (f : Lock → R) :
    BaseRobust lvBadConflict lockHistory AtMostOne f
      ∧ ¬ SelectorSafe lvBadConflict lockHistory AtMostOne := by
  refine ⟨fun _ _ hsc => lock_baseRobustAt rfl f hsc, ?_⟩
  intro h
  exact absurd (h .m1 .m2 lvScope_answers (by decide) (by decide)) (by decide)

/-- ⚠ **Row 2. Selector safety plus an agreed selector does not give
convergence.** Both replicas run one rule — *take my own state as the base* —
which `MergeModel.BaseDecision.Valid` fully licenses
(`Histories.lock_two_valid_bases`); every output is legal
(`Ancestral.lock_merge_atMostOne`); and they swap forever
(`Histories.swap_never_converges`). Safety is a property of each step, and
convergence is a property of the orbit. -/
theorem selectorSafe_and_agreement_do_not_converge :
    (∀ x y : Lock, AtMostOne x → AtMostOne y →
        AtMostOne (MergeModel.decidedMerge lockAM lockPriority (.selected x) x y).state)
      ∧ (∀ (n : Nat) (x y : Lock), x ≠ y →
        (iter swapRound n (x, y)).1 ≠ (iter swapRound n (x, y)).2) :=
  ⟨fun x y hx hy => lock_merge_atMostOne x x y hx hy, swap_never_converges⟩

/-- ⚑ **Row 3. `AmbiguityExplicit` and `BaseRobust` are orthogonal**, both
witnesses on real objects: `ccExplicit` is ambiguity-explicit on a history where
base robustness fails, and `lvPick` is base-robust at its ambiguous pair while
exercising a base elsewhere. Neither judgement is a weakening of the other. -/
theorem ambiguityExplicit_and_baseRobust_are_orthogonal :
    (AmbiguityExplicit ccExplicit
      ∧ ¬ BaseRobust ccExplicit ccHistory (fun n => n ≤ 4)
          (Recoverable.obs (fun n : Nat => n ≤ 4)))
    ∧ (BaseRobust lvPick lockHistory AtMostOne (Recoverable.obs AtMostOne)
      ∧ ¬ AmbiguityExplicit lvPick) := by
  exact ⟨⟨explicit_ambiguityExplicit _ _ _ _ _, counter_not_baseRobust _⟩,
    ⟨fun _ _ hsc => lock_baseRobustAt rfl _ hsc, lvPick_not_ambiguityExplicit⟩⟩

/-- ⚠ **Row 4. Ambiguity-explicitness buys no safety, and safety buys no
explicitness.** `lvBadConflict` declares a conflict value and it is illegal;
`ccPickRight` is safe and exercises a base. The two axes are independent in this
direction too. -/
theorem ambiguityExplicit_and_selectorSafe_are_independent :
    (AmbiguityExplicit lvBadConflict ∧ ¬ SelectorSafe lvBadConflict lockHistory AtMostOne)
      ∧ (SelectorSafe ccPickRight ccHistory (fun n => n ≤ 4)
          ∧ ¬ AmbiguityExplicit ccPickRight) := by
  refine ⟨⟨explicit_ambiguityExplicit _ _ _ _ _, ?_⟩, ⟨ccPickRight_selectorSafe, ?_⟩⟩
  · intro h
    exact absurd (h .m1 .m2 lvScope_answers (by decide) (by decide)) (by decide)
  · rintro ⟨c, hc⟩
    have h1 : (5 : Nat) = c 3 3 := hc 1 2 3 3
    have h2 : (4 : Nat) = c 3 3 := hc 2 1 3 3
    exact absurd (h1.trans h2.symm) (by decide)

/-! ## §7. The crown — the derived view

codex's architecture, taken literally: replicate the append-only record, and
derive the merge view from it as a deterministic function of that record and the
policy. The pattern is the tree's own (`Move.derived_view_sec`); what is new is
that the thing being derived is a *merge* over a version DAG, and that the
hypothesis making it work is a condition on the **base procedure**. -/

/-- Whether an origin is a merge — the versions a derivation recomputes. -/
def isMergedOrigin {V : Type uV} : Origin V → Bool
  | .merged _ _ _ => true
  | _ => false

/-- **The same origin *shape*: the two parents, with the base deliberately
forgotten.** Two replicas that merged the same pair may have selected different
bases and recorded different results; what they share is *that* the pair was
merged. -/
def SameShape {V : Type uV} : Origin V → Origin V → Prop
  | .root, .root => True
  | .ran p, .ran q => p = q
  | .merged _ x y, .merged _ x' y' => x = x' ∧ y = y'
  | _, _ => False

/-- Eliminate origin-shape agreement without repeating the nine-way constructor
cross-product. Bases remain intentionally unrelated in the merge case. -/
theorem SameShape.classify {V : Type uV} {o₁ o₂ : Origin V} (h : SameShape o₁ o₂) :
    (o₁ = .root ∧ o₂ = .root) ∨
      (∃ p, o₁ = .ran p ∧ o₂ = .ran p) ∨
      (∃ l₁ l₂ x y, o₁ = .merged l₁ x y ∧ o₂ = .merged l₂ x y) := by
  cases o₁ with
  | root =>
      cases o₂ with
      | root => exact Or.inl ⟨rfl, rfl⟩
      | ran _ => exact h.elim
      | merged _ _ _ => exact h.elim
  | ran p =>
      cases o₂ with
      | root => exact h.elim
      | ran q =>
          subst q
          exact Or.inr (Or.inl ⟨p, rfl, rfl⟩)
      | merged _ _ _ => exact h.elim
  | merged l₁ x₁ y₁ =>
      cases o₂ with
      | root => exact h.elim
      | ran _ => exact h.elim
      | merged l₂ x₂ y₂ =>
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr (Or.inr ⟨l₁, l₂, x₁, y₁, rfl, rfl⟩)

/-- **The same append-only record.** Same version graph, same root, the same
origin shape at every version, the same state wherever nobody merged, and the
same genesis. The two records may disagree at **every** merge node they contain —
in the base each replica selected and in the state it recorded — which is exactly
`Histories.base_accident_decides_the_invariant`'s situation. -/
structure SameRecord {V : Type uV} {S : Type uS} {Op : Type uOp} (H₁ H₂ : History V S Op) : Prop where
  /-- The same version graph. -/
  dag : H₁.dag = H₂.dag
  /-- The same root version. -/
  root : H₁.root = H₂.root
  /-- The same origin shape everywhere — bases forgotten. -/
  shape : ∀ v, SameShape (H₁.origin v) (H₂.origin v)
  /-- The same state wherever nobody merged. -/
  states : ∀ v, isMergedOrigin (H₁.origin v) = false → H₁.state v = H₂.state v
  /-- The same genesis. -/
  genesis : H₁.state H₁.root = H₂.state H₂.root

/-- The genesis clause is **free** whenever the root records `Origin.root`, which
`History.Coherent.root_unique` is the other half of. It is a field because a
history is not obliged to record it. -/
theorem sameRecord_genesis_of_root {V : Type uV} {S : Type uS} {Op : Type uOp} {H₁ H₂ : History V S Op}
    (hdag : H₁.root = H₂.root)
    (hst : ∀ v, isMergedOrigin (H₁.origin v) = false → H₁.state v = H₂.state v)
    (hr : H₁.origin H₁.root = Origin.root) :
    H₁.state H₁.root = H₂.state H₂.root := by
  rw [← hdag]
  exact hst H₁.root (by rw [hr]; rfl)

/-! ### §7.1 The derivation

A merge node's state is **recomputed**: from its two parents' derived states and
the base decision the *policy* makes now. The base and the state the node
recorded are ignored. A `ran` node's state is part of the record and is read —
this file has no operation replay, and says so in its non-claims. -/

/-- **The derived view at fuel `n`.** -/
def derive {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) (H : History V S Op) :
    Nat → V → S
  | 0 => fun _ => H.state H.root
  | n + 1 => fun v =>
    match H.origin v with
    | .root => H.state v
    | .ran _ => H.state v
    | .merged _ x y =>
        (P.reconcile (stateDecisionOf (derive P H n) (P.select H x y))
          (derive P H n x) (derive P H n y)).state

/-- Out of fuel, the derivation reports the genesis. -/
theorem derive_zero {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) (H : History V S Op)
    (v : V) : derive P H 0 v = H.state H.root := rfl

/-- A root node is read from the record. -/
theorem derive_root_case {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op)
    (H : History V S Op) (n : Nat) {v : V} (h : H.origin v = .root) :
    derive P H (n + 1) v = H.state v := by
  simp only [derive, h]

/-- A run node is read from the record — operations are not replayed. -/
theorem derive_ran_case {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op)
    (H : History V S Op) (n : Nat) {v p : V} (h : H.origin v = .ran p) :
    derive P H (n + 1) v = H.state v := by
  simp only [derive, h]

/-- A merge node is **recomputed** — under the policy's decision, not the
recorded base. -/
theorem derive_merged_case {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op)
    (H : History V S Op) (n : Nat) {v l x y : V} (h : H.origin v = .merged l x y) :
    derive P H (n + 1) v =
      (P.reconcile (stateDecisionOf (derive P H n) (P.select H x y))
        (derive P H n x) (derive P H n y)).state := by
  simp only [derive, h]

/-- **The derived view**: fuel is the version's rank, which the DAG supplies. -/
def viewOf {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) (H : History V S Op) (v : V) : S :=
  derive P H (H.dag.rank v) v

/-! ### §7.2 The derivation is complete, not a truncation

A view computed with bounded fuel is worth nothing until the bound is shown
sufficient. Two hypotheses do it: the history's merge nodes record their parents
(`History.Coherent`), and the selector names **ancestors**, so a base's rank never
exceeds its parents'. -/

/-- **The selector names ancestors.** Inside a policy's scope this is
`selectSound` plus §2; as a hypothesis of the fuel lemma it is what bounds the
recursion. -/
def SelectsAncestors {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op)
    (H : History V S Op) : Prop :=
  ∀ x y b, b ∈ (P.select H x y).bases → CommonAncestor H.dag x y b

/-- **One more unit of fuel changes nothing** once the fuel covers the version's
rank. -/
theorem derive_succ {V : Type uV} {S : Type uS} {Op : Type uOp} {P : HistoryMerge V S Op} {H : History V S Op}
    {M : AncestralMerge S} {impl : Impl S Op} (hco : H.Coherent M impl)
    (hanc : SelectsAncestors P H) :
    ∀ n v, H.dag.rank v ≤ n → derive P H n v = derive P H (n + 1) v := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hnode := hco.nodes v
      cases hor : H.origin v with
      | root =>
          have hv' : v = H.root := hco.root_unique v hor
          rw [derive_root_case P H 0 hor, derive_zero, hv']
      | ran p =>
          simp only [OriginOK, hor] at hnode
          exact absurd (Nat.lt_of_lt_of_le (H.dag.rank_lt _ _ hnode.1) hv)
            (Nat.not_lt_zero _)
      | merged l x y =>
          simp only [OriginOK, hor] at hnode
          exact absurd (Nat.lt_of_lt_of_le (H.dag.rank_lt _ _ hnode.1) hv)
            (Nat.not_lt_zero _)
  | succ n ih =>
      intro v hv
      have hnode := hco.nodes v
      cases hor : H.origin v with
      | root => rw [derive_root_case P H n hor, derive_root_case P H (n + 1) hor]
      | ran p => rw [derive_ran_case P H n hor, derive_ran_case P H (n + 1) hor]
      | merged l x y =>
          simp only [OriginOK, hor] at hnode
          have hx : H.dag.rank x ≤ n :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (H.dag.rank_lt _ _ hnode.1) hv)
          have hy : H.dag.rank y ≤ n :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (H.dag.rank_lt _ _ hnode.2.1) hv)
          have hbases : ∀ b, b ∈ (P.select H x y).bases →
              derive P H n b = derive P H (n + 1) b := by
            intro b hb
            exact ih b (Nat.le_trans (Reaches.rank_le (hanc x y b hb).1) hx)
          rw [derive_merged_case P H n hor, derive_merged_case P H (n + 1) hor,
            stateDecisionOf_congr _ hbases, ih x hx, ih y hy]

/-- **The fuel above the rank is idle**: any sufficient fuel gives the view. -/
theorem derive_eq_viewOf {V : Type uV} {S : Type uS} {Op : Type uOp} {P : HistoryMerge V S Op}
    {H : History V S Op} {M : AncestralMerge S} {impl : Impl S Op}
    (hco : H.Coherent M impl) (hanc : SelectsAncestors P H) (n : Nat) (v : V)
    (hv : H.dag.rank v ≤ n) : derive P H n v = viewOf P H v := by
  have key : ∀ k, derive P H (H.dag.rank v + k) v = derive P H (H.dag.rank v) v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ihk =>
        rw [show H.dag.rank v + (k + 1) = (H.dag.rank v + k) + 1 from rfl,
          ← derive_succ hco hanc (H.dag.rank v + k) v (by omega)]
        exact ihk
  have hn : n = H.dag.rank v + (n - H.dag.rank v) := by omega
  rw [hn]
  exact key _

/-- **A history the policy itself generated**: every merge node records exactly
the state the policy computes for it. -/
def PolicyGenerated {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op)
    (H : History V S Op) : Prop :=
  ∀ v l x y, H.origin v = .merged l x y → H.state v = (P.apply H x y).state

/-- ⚑ **The derivation is complete.** On a coherent, policy-generated history
whose selector names ancestors, the derived view **reproduces the record** at
every version. So `viewOf` is not a truncation, and §7.3's convergence is about
the real object. -/
theorem viewOf_eq_state {V : Type uV} {S : Type uS} {Op : Type uOp} {P : HistoryMerge V S Op}
    {H : History V S Op} {M : AncestralMerge S} {impl : Impl S Op}
    (hco : H.Coherent M impl) (hanc : SelectsAncestors P H)
    (hgen : PolicyGenerated P H) : ∀ v, viewOf P H v = H.state v := by
  refine hco.induction (P := fun v => viewOf P H v = H.state v) ?_ ?_ ?_
  · intro v hor
    have hv' : v = H.root := hco.root_unique v hor
    cases hr : H.dag.rank v with
    | zero => rw [viewOf, hr, derive_zero, hv']
    | succ m => rw [viewOf, hr, derive_root_case P H m hor]
  · intro v _ hor hpar _ _
    have hlt := H.dag.rank_lt _ _ hpar
    cases hr : H.dag.rank v with
    | zero => rw [hr] at hlt; exact absurd hlt (Nat.not_lt_zero _)
    | succ m => rw [viewOf, hr, derive_ran_case P H m hor]
  · intro v l x y hor hpx hpy _ _ _ ihx ihy ihbase
    have hltx := H.dag.rank_lt _ _ hpx
    have hlty := H.dag.rank_lt _ _ hpy
    cases hr : H.dag.rank v with
    | zero => rw [hr] at hltx; exact absurd hltx (Nat.not_lt_zero _)
    | succ m =>
        have hx : H.dag.rank x ≤ m := by omega
        have hy : H.dag.rank y ≤ m := by omega
        have hbases : ∀ b, b ∈ (P.select H x y).bases →
            derive P H m b = H.state b := by
          intro b hb
          have hrb : H.dag.rank b ≤ m :=
            Nat.le_trans (Reaches.rank_le (hanc x y b hb).1) hx
          rw [derive_eq_viewOf hco hanc m b hrb]
          exact ihbase b (hanc x y b hb)
        rw [viewOf, hr, derive_merged_case P H m hor,
          stateDecisionOf_congr _ hbases, derive_eq_viewOf hco hanc m x hx,
          derive_eq_viewOf hco hanc m y hy, ihx, ihy, stateDecisionOf_state]
        exact (hgen v l x y hor).symm

/-! ### §7.3 Convergence

The hypothesis is on the **selector**: it must read the record. A selector that
consults a merge *result* is reading the very thing the derivation is recomputing,
and `nosy_diverges` is what that costs. -/

/-- **The selector reads the record.** Two histories with the same append-only
record get the same answer. -/
def RecordDetermined {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) : Prop :=
  ∀ H₁ H₂ : History V S Op, SameRecord H₁ H₂ → ∀ x y, P.select H₁ x y = P.select H₂ x y

/-- **History convergence**: two derivations over the same record agree at every
version. -/
def HistoryConvergent {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) : Prop :=
  ∀ H₁ H₂ : History V S Op, SameRecord H₁ H₂ → ∀ v, viewOf P H₁ v = viewOf P H₂ v

/-- The derivation at every fuel is a function of the record alone. -/
theorem derive_sameRecord {V : Type uV} {S : Type uS} {Op : Type uOp} {P : HistoryMerge V S Op}
    (hrd : RecordDetermined P) {H₁ H₂ : History V S Op} (hs : SameRecord H₁ H₂) :
    ∀ n v, derive P H₁ n v = derive P H₂ n v := by
  intro n
  induction n with
  | zero => intro v; exact hs.genesis
  | succ n ih =>
      intro v
      rcases (hs.shape v).classify with ⟨h1, h2⟩ | ⟨p, h1, h2⟩ |
          ⟨l₁, l₂, x, y, h1, h2⟩
      · rw [derive_root_case P H₁ n h1, derive_root_case P H₂ n h2]
        exact hs.states v (by rw [h1]; rfl)
      · rw [derive_ran_case P H₁ n h1, derive_ran_case P H₂ n h2]
        exact hs.states v (by rw [h1]; rfl)
      · rw [derive_merged_case P H₁ n h1, derive_merged_case P H₂ n h2,
          hrd H₁ H₂ hs x y, funext ih]

/-- ⚑ **THE CROWN: same record, same policy, same view.** Two replicas whose
append-only records agree — same DAG, same origin shapes, same states wherever
nobody merged — derive the **same state at every version**, however wildly their
recorded merges disagree.

The hypothesis is exactly `RecordDetermined`: the base procedure must be a
function of the record. Everything else is supplied by the shape of
`HistoryMerge`, which is why codex's structural demand was the load-bearing
part — a model that hides its selector cannot state this theorem, let alone
prove it.

This is the first convergence result in the history layer.
`Histories.lean`'s own non-claims say convergence is proved nowhere in it, and
both of its counterexamples survive: §6 row 2 keeps
`Histories.swap_never_converges`, and §8 characterizes the class it lives in. -/
theorem recordDetermined_converges {V : Type uV} {S : Type uS} {Op : Type uOp} {P : HistoryMerge V S Op}
    (hrd : RecordDetermined P) : HistoryConvergent P := by
  intro H₁ H₂ hs v
  rw [viewOf, viewOf, hs.dag]
  exact derive_sameRecord hrd hs _ v

/-- A selector that ignores the history is record-determined — the trivial
sufficient condition, and the one every witness here meets. -/
theorem recordDetermined_of_constant {V : Type uV} {S : Type uS} {Op : Type uOp} {P : HistoryMerge V S Op}
    (h : ∀ H₁ H₂ : History V S Op, ∀ x y, P.select H₁ x y = P.select H₂ x y) :
    RecordDetermined P := fun H₁ H₂ _ x y => h H₁ H₂ x y

/-- The criss-cross policies read no history at all, so they converge. -/
theorem ccExplicit_convergent : HistoryConvergent ccExplicit :=
  recordDetermined_converges (recordDetermined_of_constant (fun _ _ _ _ => rfl))

/-- …and so does the base-picking one. ⚠ Read it as the orthogonality it is:
`ccPickLeft` is **convergent and illegal** — every replica derives `5` against a
ceiling of `4`. Convergence is agreement, not safety. -/
theorem ccPickLeft_convergent : HistoryConvergent ccPickLeft :=
  recordDetermined_converges (recordDetermined_of_constant (fun _ _ _ _ => rfl))

/-! ### §7.4 The derived view on the two real histories -/

/-- `SelectsAncestors` for the criss-cross selectors: the fork point reaches
every version (`cc_root_reaches`), and the ambiguous pair names its two maximal
bases. -/
theorem ccSelectLR_selectsAncestors (H : History Ver Nat Unit) (hd : H.dag = ccDag) :
    SelectsAncestors ccExplicit H := by
  intro x y b hb
  rw [hd]
  revert hb
  cases x <;> cases y <;>
    (intro hb
     first
      | (cases hb with
         | head => exact ⟨cc_root_reaches _, cc_root_reaches _⟩
         | tail _ h => cases h)
      | (cases hb with
         | head => exact cc_left_common
         | tail _ h =>
            cases h with
            | head => exact cc_right_common
            | tail _ h' => cases h')
      | (cases hb with
         | head => exact cc_left_common.symm
         | tail _ h =>
            cases h with
            | head => exact cc_right_common.symm
            | tail _ h' => cases h'))

/-- `SelectsAncestors` for the lock selector. -/
theorem lvSelect_selectsAncestors (H : History LVer Lock LockOp) (hd : H.dag = lvDag) :
    SelectsAncestors lvExplicit H := by
  intro x y b hb
  rw [hd]
  revert hb
  cases x <;> cases y <;>
    (intro hb
     first
      | (cases hb with
         | head => exact ⟨lv_root_reaches _, lv_root_reaches _⟩
         | tail _ h => cases h)
      | (cases hb with
         | head => exact lv_alice_common
         | tail _ h =>
            cases h with
            | head => exact lv_bob_common
            | tail _ h' => cases h')
      | (cases hb with
         | head => exact lv_alice_common.symm
         | tail _ h =>
            cases h with
            | head => exact lv_bob_common.symm
            | tail _ h' => cases h'))

/-- **The lock history is the policy's own record**: every merge node holds
exactly what `lvExplicit` computes for its pair. Both of `Histories` §7.2's
merges are re-derived, and so is the merge of the merges. -/
theorem lockHistory_policyGenerated : PolicyGenerated lvExplicit lockHistory := by
  intro v l x y hor
  cases v
  · simp [lockHistory, lvOrigin] at hor
  · simp [lockHistory, lvOrigin] at hor
  · simp [lockHistory, lvOrigin] at hor
  · injection hor with _ hx hy; subst hx; subst hy; decide
  · injection hor with _ hx hy; subst hx; subst hy; decide
  · injection hor with _ hx hy; subst hx; subst hy; decide

/-- ⚑ **The derived view reproduces the lock history exactly** — and it is
`viewOf_eq_state` that says so, with all three of its hypotheses discharged on a
history that exists: `Histories.lockHistory_coherent`,
`lvSelect_selectsAncestors` and `lockHistory_policyGenerated`. So the general
adequacy theorem is not resting on hypotheses nothing meets, and `viewOf` is not
a truncation. -/
theorem lock_view_is_the_record : ∀ v : LVer, viewOf lvExplicit lockHistory v = lvState v :=
  viewOf_eq_state lockHistory_coherent (lvSelect_selectsAncestors lockHistory rfl)
    lockHistory_policyGenerated

/-- ⚠ **…and the criss-cross record is no policy's record at all.** `joinLeft`
and `joinRight` merge the *same pair* `(mergeL, mergeR)` and record `5` and `4`.
A policy is a function of the pair, so **no** `HistoryMerge` whatsoever generates
this history — the accident `Histories` §6 exhibits lives in a record that no
declared procedure could have produced. It is the sharpest statement of what
declaring the selector buys. -/
theorem ccHistory_not_policyGenerated (P : HistoryMerge Ver Nat Unit) :
    ¬ PolicyGenerated P ccHistory := by
  intro h
  have h5 := h .joinLeft .left .mergeL .mergeR rfl
  have h4 := h .joinRight .right .mergeL .mergeR rfl
  exact absurd (h5.trans h4.symm) (by decide)

/-- ⚑ **The derived view repairs the base accident.** `ccHistory` records `5` at
`joinLeft`, over a ceiling of `4` — `Histories.repeated_merge_breaks_the_invariant`
is that node. Under an ambiguity-explicit policy the derived view holds `3`, and
`3 ≤ 4`.

The accident is a property of the **record**: one replica happened to merge
against `left`. A view derived from the record under a declared policy does not
have it — which is the practical content of the whole file. -/
theorem derived_view_repairs_the_base_accident :
    viewOf ccExplicit ccHistory .joinLeft = 3
      ∧ ccState .joinLeft = 5
      ∧ ¬ ((5 : Nat) ≤ 4)
      ∧ ((3 : Nat) ≤ 4) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- ⚠ **…and a base-picking policy derives the accident instead.** Same record,
same DAG, two policies: `3` and `5`. The record does not decide the view; the
**policy** does, which is why it has to be declared. -/
theorem the_policy_decides_the_view :
    viewOf ccExplicit ccHistory .joinLeft = 3
      ∧ viewOf ccPickLeft ccHistory .joinLeft = 5
      ∧ viewOf ccPickRight ccHistory .joinLeft = 4 :=
  ⟨by decide, by decide, by decide⟩

/-! ### §7.5 The record half of the obstruction

A selector that reads a merge **result** is not record-determined, and the
convergence fails outright — two records that agree on everything append-only
derive different views. -/

/-- The criss-cross record with `joinLeft` holding `4` instead of `5` — the other
replica's equally licensed merge (`Histories.base_accident_decides_the_invariant`
is the pair). -/
def ccStateFour : Ver → Nat
  | .joinLeft => 4
  | v => ccState v

/-- The same record, differing only at a merge node. -/
def ccHistoryFour : History Ver Nat Unit where
  dag := ccDag
  state := ccStateFour
  origin := ccOrigin
  root := .root

/-- The two criss-cross records are the same append-only record. -/
theorem ccHistory_sameRecord : SameRecord ccHistory ccHistoryFour where
  dag := rfl
  root := rfl
  shape := by intro v; cases v <;> first | exact True.intro | rfl | exact ⟨rfl, rfl⟩
  states := by intro v; cases v <;> decide
  genesis := rfl

/-- ⚠ **A selector that reads a merge result.** It answers with the two maximal
bases in an order chosen by looking at what `joinLeft` recorded — a perfectly
sound answer either way (`ccSelectLR_sound`'s argument applies to both orders),
and not a function of the record. -/
def nosySelect (H : History Ver Nat Unit) : Ver → Ver → MergeModel.BaseDecision Ver
  | .mergeL, .mergeR =>
      if H.state .joinLeft = 5 then .ambiguous .left .right else .ambiguous .right .left
  | .mergeR, .mergeL =>
      if H.state .joinLeft = 5 then .ambiguous .left .right else .ambiguous .right .left
  | _, _ => .selected .root

/-- The nosy selector is sound on `ccScope` — both branches name the same two
maximal common bases, in the two orders. -/
theorem nosySelect_sound : ∀ H x y, ccScope H x y →
    ValidInHistory H x y (nosySelect H x y) := by
  rintro H x y ⟨hd, hxy | hxy⟩ <;> obtain ⟨rfl, rfl⟩ := hxy <;>
    by_cases hj : H.state .joinLeft = 5
  · show ValidInHistory H .mergeL .mergeR
      (if H.state .joinLeft = 5 then .ambiguous .left .right else .ambiguous .right .left)
    rw [if_pos hj]
    show MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [hd]
    exact ⟨cc_left_maximal, cc_right_maximal, by decide⟩
  · show ValidInHistory H .mergeL .mergeR
      (if H.state .joinLeft = 5 then .ambiguous .left .right else .ambiguous .right .left)
    rw [if_neg hj]
    show MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [hd]
    exact ⟨cc_right_maximal, cc_left_maximal, by decide⟩
  · show ValidInHistory H .mergeR .mergeL
      (if H.state .joinLeft = 5 then .ambiguous .left .right else .ambiguous .right .left)
    rw [if_pos hj]
    show MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [hd]
    exact ⟨maximalCommonBase_symm cc_left_maximal, maximalCommonBase_symm cc_right_maximal, by decide⟩
  · show ValidInHistory H .mergeR .mergeL
      (if H.state .joinLeft = 5 then .ambiguous .left .right else .ambiguous .right .left)
    rw [if_neg hj]
    show MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [hd]
    exact ⟨maximalCommonBase_symm cc_right_maximal, maximalCommonBase_symm cc_left_maximal, by decide⟩

/-- The nosy policy: a licensed selector, a base-picking reconciler. -/
def ccNosy : HistoryMerge Ver Nat Unit :=
  picking counterAM (fun u v => Nat.max u v) nosySelect ccScope nosySelect_sound

/-- ⚠ **A selector that reads a merge result destroys convergence.** Two records
that agree on everything append-only derive `5` and `4` at the same version — and
the policy is `selectSound` throughout (`nosySelect_sound`), so nothing weaker
than `RecordDetermined` rules it out. This is the record half of the obstruction
§8 characterizes. -/
theorem nosy_diverges :
    SameRecord ccHistory ccHistoryFour
      ∧ viewOf ccNosy ccHistory .joinLeft ≠ viewOf ccNosy ccHistoryFour .joinLeft
      ∧ ¬ HistoryConvergent ccNosy
      ∧ ¬ RecordDetermined ccNosy := by
  have hne : viewOf ccNosy ccHistory .joinLeft ≠ viewOf ccNosy ccHistoryFour .joinLeft := by
    decide
  refine ⟨ccHistory_sameRecord, hne, fun h => hne (h _ _ ccHistory_sameRecord _), ?_⟩
  intro h
  exact hne (recordDetermined_converges h _ _ ccHistory_sameRecord _)

/-! ## §8. The excluded class, characterized

`Histories.swap_never_converges` is the standing refutation of convergence, and
the mission is to say **which policies it excludes**. It is not the merge:
`AncestralMerge.comm` holds there. It is the *base procedure*, and precisely its
dependence on which replica is asking — the two sides present the same pair in
opposite orders and the selector answers differently.

`Recoverable.SymmetricChooser.symm` is the same law one layer down, forced by
`AncestralMerge.comm` (`Recoverable.comm_forces_symmetric_chooser`). Nothing had
stated it for the base procedure. -/

/-- **The selector does not depend on which replica is asking.** -/
def SelectorSymmetric {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) : Prop :=
  ∀ H x y, P.select H x y = P.select H y x

/-- **The reconciler does not either.** For a declared-conflict policy this
follows from `AncestralMerge.comm` on the selected branch and from commutativity
of the conflict value on the other two. -/
def ReconcileSymmetric {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op) : Prop :=
  ∀ d u v, (P.reconcile d u v).state = (P.reconcile d v u).state

/-- A declared-conflict policy with a commutative conflict value is
reconcile-symmetric. -/
theorem explicit_reconcileSymmetric {V : Type uV} {S : Type uS} {Op : Type uOp} (M : AncestralMerge S)
    (conflict : S → S → S) (hc : ∀ u v, conflict u v = conflict v u)
    (sel : History V S Op → V → V → MergeModel.BaseDecision V)
    (sc : History V S Op → V → V → Prop)
    (hs : ∀ H x y, sc H x y → ValidInHistory H x y (sel H x y)) :
    ReconcileSymmetric (explicit M conflict sel sc hs) := by
  intro d u v
  cases d with
  | selected l => exact M.comm l u v
  | ambiguous b₁ b₂ => exact hc u v
  | unavailable => exact hc u v

/-- ⚑ **Replicas agree on the order they present the pair in** — the one-step
statement `swapRound` refutes. Both hypotheses are needed and both are about
symmetry: of the selector, and of the reconciler. -/
theorem replicas_agree_on_order {V : Type uV} {S : Type uS} {Op : Type uOp} {P : HistoryMerge V S Op}
    (hsym : SelectorSymmetric P) (hrec : ReconcileSymmetric P)
    (H : History V S Op) (x y : V) : (P.apply H x y).state = (P.apply H y x).state := by
  rw [HistoryMerge.apply, HistoryMerge.apply, HistoryMerge.decisionAt,
    HistoryMerge.decisionAt, hsym H x y]
  exact hrec _ _ _

/-- The criss-cross selector is symmetric. -/
theorem ccSelectLR_symmetric : SelectorSymmetric ccExplicit := by
  intro _ x y
  cases x <;> cases y <;> rfl

/-- The lock selector is symmetric. -/
theorem lvSelect_symmetric : SelectorSymmetric lvExplicit := by
  intro _ x y
  cases x <;> cases y <;> rfl

/-- The lock policy's reconciler is symmetric — `Ancestral.lockPriority_comm` is
the conflict half. -/
theorem lvExplicit_reconcileSymmetric : ReconcileSymmetric lvExplicit :=
  explicit_reconcileSymmetric lockAM lockPriority lockPriority_comm lvSelect lvScope
    lvSelect_sound

/-- …and the counter policy's, by `Nat.max_comm`. -/
theorem ccExplicit_reconcileSymmetric : ReconcileSymmetric ccExplicit :=
  explicit_reconcileSymmetric counterAM (fun u v => Nat.max u v) Nat.max_comm ccSelectLR
    ccScope ccSelectLR_sound

/-- ⚑ **The lock policy's two replicas agree on the order** — the statement the
swap refutes, discharged on the policy the file has been using throughout. Both
hypotheses of `replicas_agree_on_order` are met, so the theorem is about
something. -/
theorem lvExplicit_replicas_agree (H : History LVer Lock LockOp) (x y : LVer) :
    (lvExplicit.apply H x y).state = (lvExplicit.apply H y x).state :=
  replicas_agree_on_order lvSelect_symmetric lvExplicit_reconcileSymmetric H x y

/-- …and the counter policy's. -/
theorem ccExplicit_replicas_agree (H : History Ver Nat Unit) (x y : Ver) :
    (ccExplicit.apply H x y).state = (ccExplicit.apply H y x).state :=
  replicas_agree_on_order ccSelectLR_symmetric ccExplicit_reconcileSymmetric H x y

/-- **The swap is two self-based merges.** `Histories.swapRound` — each replica
taking its own state as the base — is exactly the pair of results a policy
answering `selected` *at the first argument* produces on the two orders. -/
theorem swapRound_is_two_self_based_merges (x y : Lock) :
    swapRound (x, y)
      = ((MergeModel.decidedMerge lockAM lockPriority (.selected x) x y).state,
         (MergeModel.decidedMerge lockAM lockPriority (.selected y) y x).state) := rfl

/-- ⚠ **…and that selector is not symmetric.** One rule, two orders, two
different bases — which `replicas_agree_on_order` is precisely the exclusion
of. -/
theorem self_base_selector_not_symmetric :
    (MergeModel.BaseDecision.selected (⟨true, false⟩ : Lock))
      ≠ MergeModel.BaseDecision.selected (⟨false, true⟩ : Lock) := by
  intro h
  have hb : (⟨true, false⟩ : Lock) = ⟨false, true⟩ := by injection h
  exact absurd hb (by decide)

/-- ⚠ **The asymmetry is observable in one step**, before any orbit: the two
sides of the swap disagree immediately. -/
theorem the_swap_is_order_dependence :
    (MergeModel.decidedMerge lockAM lockPriority
        (.selected (⟨true, false⟩ : Lock)) ⟨true, false⟩ ⟨false, true⟩).state
      ≠ (MergeModel.decidedMerge lockAM lockPriority
        (.selected (⟨false, true⟩ : Lock)) ⟨false, true⟩ ⟨true, false⟩).state := by decide

/-- ⚑ **The version level already refuses the swap's decision.** At the state
level both bases are licensed — `Histories.lock_two_valid_bases` discharges
`MergeModel.BaseDecision.Valid` for each. At the *history* level neither is:
`m1` is not a common ancestor of `m1` and `m2`, so `ValidInHistory` refuses both
`selected` answers.

So the two licences disagree about exactly the policy that never converges, and
the history-level one is the one that is right. That is the policy hypothesis of
this file's TRANSPORTS row. -/
theorem the_self_base_policy_is_not_history_licensed :
    ¬ ValidInHistory lockHistory .m1 .m2 (.selected .m1)
      ∧ ¬ ValidInHistory lockHistory .m1 .m2 (.selected .m2) := by
  constructor
  · intro h
    rcases h.1.2 with he | ha
    · exact absurd he (by decide)
    · exact absurd ha.rank_lt (by decide)
  · intro h
    rcases h.1.1 with he | ha
    · exact absurd he (by decide)
    · exact absurd ha.rank_lt (by decide)

/-- ⚠ **The two obstructions, kept distinct.** The swap witnesses failure of
order agreement when replicas choose different self-bases; `nosy_diverges`
witnesses failure of history convergence when a selector is not
record-determined. The positive convergence statement is exactly the last
conjunct: every `RecordDetermined` policy converges. It does **not** require
selector symmetry — `ccPickLeft_convergent` is the deliberately asymmetric
sanity check — while `replicas_agree_on_order` is the separate theorem that
does. -/
theorem the_obstruction :
    (∀ (n : Nat) (x y : Lock), x ≠ y →
        (iter swapRound n (x, y)).1 ≠ (iter swapRound n (x, y)).2)
      ∧ (¬ RecordDetermined ccNosy ∧ ¬ HistoryConvergent ccNosy)
      ∧ (∀ {V : Type uV} {S : Type uS} {Op : Type uOp} (P : HistoryMerge V S Op), RecordDetermined P →
          HistoryConvergent P) :=
  ⟨swap_never_converges, ⟨nosy_diverges.2.2.2, nosy_diverges.2.2.1⟩,
   fun _ h => recordDetermined_converges h⟩

/-! ## §9. The verdicts, side by side -/

/-- **The four judgements, each satisfiable and each refutable, and the crown.**

  * `BaseRobust` — the lock satisfies it at its ambiguous pair; the counter
    refutes it at its own, and the refutation is
    `Histories.base_accident_decides_the_invariant`.
  * `SelectorSafe` — satisfied by two counter policies for two different reasons,
    refuted by a third that differs from one of them only in the *order* it names
    two equally licensed bases.
  * `AmbiguityExplicit` — satisfied by the declared-conflict policies, refuted by
    the base-picking ones, whose choice is observable in the output.
  * `HistoryConvergent` — every record-determined policy converges; a selector
    that reads a merge result does not.
  * …and the derived view is **complete** (`viewOf_eq_state`,
    `lock_view_is_the_record`), **repairs** the base accident the record carries,
    and the record carrying it is no policy's record at all. -/
theorem the_verdicts :
    (BaseRobust lvExplicit lockHistory AtMostOne (Recoverable.obs AtMostOne)
      ∧ ¬ BaseRobust ccExplicit ccHistory (fun n => n ≤ 4)
          (Recoverable.obs (fun n : Nat => n ≤ 4)))
    ∧ (SelectorSafe ccExplicit ccHistory (fun n => n ≤ 4)
      ∧ SelectorSafe ccPickRight ccHistory (fun n => n ≤ 4)
      ∧ ¬ SelectorSafe ccPickLeft ccHistory (fun n => n ≤ 4))
    ∧ (AmbiguityExplicit ccExplicit ∧ ¬ AmbiguityExplicit ccPickLeft)
    ∧ (HistoryConvergent ccExplicit ∧ ¬ HistoryConvergent ccNosy)
    ∧ (∀ v : LVer, viewOf lvExplicit lockHistory v = lvState v)
    ∧ (viewOf ccExplicit ccHistory .joinLeft = 3 ∧ ccState .joinLeft = 5)
    ∧ (∀ P : HistoryMerge Ver Nat Unit, ¬ PolicyGenerated P ccHistory) :=
  ⟨⟨lock_baseRobust _, counter_not_baseRobust _⟩,
   ⟨ccExplicit_selectorSafe, ccPickRight_selectorSafe, ccPickLeft_not_selectorSafe⟩,
   ⟨explicit_ambiguityExplicit _ _ _ _ _, ccPickLeft_not_ambiguityExplicit⟩,
   ⟨ccExplicit_convergent, nosy_diverges.2.2.1⟩,
   lock_view_is_the_record,
   ⟨by decide, by decide⟩,
   ccHistory_not_policyGenerated⟩

end Uwueave.HistoryPolicy
