/-
# Uwueave.HistoryEngine — an executable finite history boundary

`FiniteHistory` searches a caller-covered `VersionDag`; `HistoryPolicy` gives a
semantic merge policy; and `CompositeDelta` retains the patches needed to turn a
selected base into an operational merge.  This module joins those three layers
without strengthening any of their trust boundaries.

There are two deliberately different refusals:

* graph search returns `refused` only when the certified finite search returned
  no `BaseSelection`; it is not relabelled `unavailable`;
* semantic policy evaluation returns `refused` outside the policy's declared
  scope.  Thus an all-pairs sweep cannot make a partial policy look total.

Patch admission is equally explicit.  A selected version base is accompanied
by two caller-supplied, patch-labelled branches.  A residual algebra grows the
diamond and proves that the policy result is its common legal endpoint.  No
patch is reconstructed from endpoint states.

Finally, one delivery of each residual patch always converges.  Duplicate
delivery requires the named `ReplayStable` premise; with it, every positive
number of deliveries converges and remains admitted.  This is the strongest
repeat-delivery statement available from the current algebra: residual
commutation alone does not imply idempotence.
-/
import Uwueave.FiniteHistory
import Uwueave.HistoryPolicy
import Uwueave.CompositeDelta

namespace Uwueave.HistoryEngine

open Uwueave Uwueave.Ancestral Uwueave.Necessity
open Uwueave.Histories Uwueave.HistoryBase Uwueave.HistoryPolicy
open Uwueave.FiniteHistory Uwueave.CompositeDelta

universe u v

/-! ## §1. Four-way proof-carrying graph decisions -/

/-- Executable finite search that returns either a listed witness or a proof
that every listed element fails.  Unlike `Option`, the negative branch retains
the evidence needed by an operational refusal. -/
inductive SearchResult {α : Type} (xs : List α) (P : α → Prop) where
  | found (value : α) (member : value ∈ xs) (holds : P value)
  | absent (none : ∀ value, value ∈ xs → ¬ P value)

def searchTotal {α : Type} (xs : List α) (P : α → Prop)
    (decP : ∀ x, Decidable (P x)) : SearchResult xs P :=
  match xs with
  | [] => .absent (by simp)
  | x :: rest =>
      match decP x with
      | isTrue hx => .found x (List.Mem.head _) hx
      | isFalse hx =>
          match searchTotal rest P decP with
          | .found y hy hP => .found y (List.Mem.tail _ hy) hP
          | .absent hnone => .absent (by
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact hx
              · exact hnone y hy)

/-- A total *operational* response from the finite search.  `refused` carries
proof that none of the three exact predicates was established: there is no
lowest base, common ancestry is not absent, and no two distinct maximal bases
were found.  It preserves the exhaustive candidate list and is deliberately
not relabelled `unavailable`. -/
inductive PairDecision {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) where
  | selected (base : V) (lowest : LowestCommonBase D x y base)
      (common : List V) (common_exact : ∀ b, b ∈ common ↔ CommonAncestor D x y b)
  | ambiguous (first second : V)
      (first_maximal : MaximalCommonBase D x y first)
      (second_maximal : MaximalCommonBase D x y second) (distinct : first ≠ second)
      (common : List V) (common_exact : ∀ b, b ∈ common ↔ CommonAncestor D x y b)
  | unavailable (none_common : ∀ b, ¬ CommonAncestor D x y b)
      (common : List V) (common_exact : ∀ b, b ∈ common ↔ CommonAncestor D x y b)
  | refused (common : List V)
      (common_exact : ∀ b, b ∈ common ↔ CommonAncestor D x y b)
      (no_lowest : ¬ ∃ b, LowestCommonBase D x y b)
      (common_not_absent : ¬ (∀ b, ¬ CommonAncestor D x y b))
      (no_ambiguity : ¬ ∃ b₁ b₂, MaximalCommonBase D x y b₁ ∧
        MaximalCommonBase D x y b₂ ∧ b₁ ≠ b₂)

/-- Decide the three exact finite predicates and retain a fourth, proved
refusal branch instead of inventing a base. -/
def decidePair {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) : PairDecision F x y :=
  match searchTotal F.vertices (fun b => LowestCommonBase D x y b)
      (fun b => F.decideLowestCommonBase x y b) with
  | .found base _ lowest =>
      .selected base lowest (commonCandidates F x y)
        (mem_commonCandidates_iff F x y)
  | .absent noLowestListed =>
      match F.decideUnavailable x y with
      | isTrue noneCommon =>
          .unavailable noneCommon (commonCandidates F x y)
            (mem_commonCandidates_iff F x y)
      | isFalse commonNotAbsent =>
          match searchTotal (orderedPairs F.vertices)
              (fun p => MaximalCommonBase D x y p.1 ∧
                MaximalCommonBase D x y p.2 ∧ p.1 ≠ p.2)
              (fun p =>
                @instDecidableAnd _ _ (F.decideMaximalCommonBase x y p.1)
                  (@instDecidableAnd _ _ (F.decideMaximalCommonBase x y p.2)
                    (inferInstance : Decidable (p.1 ≠ p.2)))) with
          | .found pair _ proof =>
              .ambiguous pair.1 pair.2 proof.1 proof.2.1 proof.2.2
                (commonCandidates F x y)
                (mem_commonCandidates_iff F x y)
          | .absent noAmbiguityListed =>
              .refused (commonCandidates F x y) (mem_commonCandidates_iff F x y)
                (by
                  rintro ⟨b, hb⟩
                  exact noLowestListed b (F.complete b) hb)
                commonNotAbsent
                (by
                  rintro ⟨b₁, b₂, h₁, h₂, hne⟩
                  exact noAmbiguityListed (b₁, b₂)
                    (by simp [orderedPairs, F.complete b₁, F.complete b₂])
                    ⟨h₁, h₂, hne⟩)

/-- The deployment-facing shape, erasing proofs but not refusal. -/
inductive DecisionKind where
  | selected
  | ambiguous
  | unavailable
  | refused
  deriving DecidableEq, Repr

/-- Proof erasure for tests and transports. -/
def PairDecision.kind {V : Type} [DecidableEq V] {D : VersionDag V}
    {F : Enumeration D} {x y : V} : PairDecision F x y → DecisionKind
  | .selected .. => .selected
  | .ambiguous .. => .ambiguous
  | .unavailable .. => .unavailable
  | .refused .. => .refused

/-- A successful graph decision erases to the raw semantic decision type. -/
def PairDecision.toDecision? {V : Type} [DecidableEq V] {D : VersionDag V}
    {F : Enumeration D} {x y : V} :
    PairDecision F x y → Option (MergeModel.BaseDecision V)
  | .selected b .. => some (.selected b)
  | .ambiguous b₁ b₂ .. => some (.ambiguous b₁ b₂)
  | .unavailable .. => some .unavailable
  | .refused .. => none

/-- Every non-refused erasure satisfies the exact DAG-level contract. -/
theorem PairDecision.toDecision?_valid {V : Type} [DecidableEq V]
    {D : VersionDag V} {F : Enumeration D} {x y : V} (d : PairDecision F x y) :
    ∀ raw, d.toDecision? = some raw → DecisionValid D x y raw := by
  intro raw h
  cases d with
  | selected b hb common exact => simp only [PairDecision.toDecision?, Option.some.injEq] at h; subst raw; exact hb
  | ambiguous b₁ b₂ h₁ h₂ hne common exact =>
      simp only [PairDecision.toDecision?, Option.some.injEq] at h
      subst raw
      exact ⟨h₁, h₂, hne⟩
  | unavailable hno common exact =>
      simp only [PairDecision.toDecision?, Option.some.injEq] at h
      subst raw
      exact hno
  | refused common exact noLowest notAbsent noAmbiguity =>
      change none = some raw at h
      cases h

/-- One graph response for every ordered pair. -/
structure PairEntry {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) where
  x : V
  y : V
  decision : PairDecision F x y

/-- Deterministic all-ordered-pairs graph sweep. -/
def graphSweep {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) : List (PairEntry F) :=
  F.vertices.flatMap fun x => F.vertices.map fun y => ⟨x, y, decidePair F x y⟩

/-- The graph sweep contains every carrier pair, including refusals. -/
theorem graphSweep_complete {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) :
    ∃ e, e ∈ graphSweep F ∧ e.x = x ∧ e.y = y := by
  let e : PairEntry F := ⟨x, y, decidePair F x y⟩
  refine ⟨e, ?_, rfl, rfl⟩
  simp only [graphSweep, List.mem_flatMap, List.mem_map]
  exact ⟨x, F.complete x, y, F.complete y, rfl⟩

/-- A certified lowest base forces the finite engine's selected branch. -/
theorem decidePair_selected_of_lowest {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) {x y b : V}
    (lowest : LowestCommonBase D x y b) : (decidePair F x y).kind = .selected := by
  unfold decidePair
  cases searchTotal F.vertices (fun c => LowestCommonBase D x y c)
      (fun c => F.decideLowestCommonBase x y c) with
  | found value member holds => rfl
  | absent none => exact (none b (F.complete b) lowest).elim

/-- Two distinct maximal bases force the finite engine's ambiguous branch. -/
theorem decidePair_ambiguous_of_maximal {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) {x y b₁ b₂ : V}
    (first : MaximalCommonBase D x y b₁)
    (second : MaximalCommonBase D x y b₂) (distinct : b₁ ≠ b₂) :
    (decidePair F x y).kind = .ambiguous := by
  have noLowest : ¬ ∃ b, LowestCommonBase D x y b :=
    ambiguous_excludes_lowest first second distinct
  have notUnavailable : ¬ (∀ b, ¬ CommonAncestor D x y b) :=
    fun h => h b₁ first.1
  unfold decidePair
  cases searchTotal F.vertices (fun c => LowestCommonBase D x y c)
      (fun c => F.decideLowestCommonBase x y c) with
  | found value member holds => exact (noLowest ⟨value, holds⟩).elim
  | absent none =>
      cases F.decideUnavailable x y with
      | isTrue unavailable => exact (notUnavailable unavailable).elim
      | isFalse present =>
          cases searchTotal (orderedPairs F.vertices)
              (fun p => MaximalCommonBase D x y p.1 ∧
                MaximalCommonBase D x y p.2 ∧ p.1 ≠ p.2)
              (fun p =>
                @instDecidableAnd _ _ (F.decideMaximalCommonBase x y p.1)
                  (@instDecidableAnd _ _ (F.decideMaximalCommonBase x y p.2)
                    (inferInstance : Decidable (p.1 ≠ p.2)))) with
          | found pair member holds => rfl
          | absent none =>
              exact (none (b₁, b₂)
                (by simp [orderedPairs, F.complete b₁, F.complete b₂])
                ⟨first, second, distinct⟩).elim

/-- A proof that no common ancestor exists forces `unavailable`, never generic
refusal. -/
theorem decidePair_unavailable_of_none {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) {x y : V}
    (noneCommon : ∀ b, ¬ CommonAncestor D x y b) :
    (decidePair F x y).kind = .unavailable := by
  unfold decidePair
  cases searchTotal F.vertices (fun c => LowestCommonBase D x y c)
      (fun c => F.decideLowestCommonBase x y c) with
  | found value member holds => exact (noneCommon value holds.1).elim
  | absent none =>
      cases F.decideUnavailable x y with
      | isTrue absent => rfl
      | isFalse present => exact (present noneCommon).elim

/-! ## §2. Sweeping the semantic policy, not merely the graph -/

/-- A policy decision at one pair.  The three admitted constructors retain the
policy's exact answer, scope proof, and history-validity proof.  The fourth
constructor proves the pair is outside scope. -/
inductive SemanticDecision {V S Op : Type} (P : HistoryMerge V S Op)
    (H : History V S Op) (x y : V) where
  | selected (base : V) (in_scope : P.scope H x y)
      (select_eq : P.select H x y = .selected base)
      (lowest : LowestCommonBase H.dag x y base)
  | ambiguous (first second : V) (in_scope : P.scope H x y)
      (select_eq : P.select H x y = .ambiguous first second)
      (first_maximal : MaximalCommonBase H.dag x y first)
      (second_maximal : MaximalCommonBase H.dag x y second) (distinct : first ≠ second)
  | unavailable (in_scope : P.scope H x y)
      (select_eq : P.select H x y = .unavailable)
      (none_common : ∀ b, ¬ CommonAncestor H.dag x y b)
  | refused (out_of_scope : ¬ P.scope H x y)

/-- Evaluate one semantic pair.  Decidability of scope is an explicit runtime
input; `HistoryMerge.selectSound` supplies all positive proof fields. -/
def decideSemantic {V S Op : Type} (P : HistoryMerge V S Op)
    (H : History V S Op) (x y : V) (scopeDec : Decidable (P.scope H x y)) :
    SemanticDecision P H x y :=
  match scopeDec with
  | isFalse hscope => .refused hscope
  | isTrue hscope =>
      match heq : P.select H x y with
      | .selected b =>
          have valid : ValidInHistory H x y (.selected b) := by
            rw [← heq]
            exact P.selectSound H x y hscope
          .selected b hscope heq valid
      | .ambiguous b₁ b₂ =>
          let valid : ValidInHistory H x y (.ambiguous b₁ b₂) := by
            rw [← heq]
            exact P.selectSound H x y hscope
          .ambiguous b₁ b₂ hscope heq valid.1 valid.2.1 valid.2.2
      | .unavailable =>
          have valid : ValidInHistory H x y .unavailable := by
            rw [← heq]
            exact P.selectSound H x y hscope
          .unavailable hscope heq valid

/-- The four observable semantic outcomes. -/
def SemanticDecision.kind {V S Op : Type} {P : HistoryMerge V S Op}
    {H : History V S Op} {x y : V} : SemanticDecision P H x y → DecisionKind
  | .selected .. => .selected
  | .ambiguous .. => .ambiguous
  | .unavailable .. => .unavailable
  | .refused .. => .refused

/-- Admitted decisions evaluate the policy; refusal has no fabricated state. -/
def SemanticDecision.result? {V S Op : Type} {P : HistoryMerge V S Op}
    {H : History V S Op} {x y : V} : SemanticDecision P H x y → Option S
  | .selected .. => some (P.result H x y)
  | .ambiguous .. => some (P.result H x y)
  | .unavailable .. => some (P.result H x y)
  | .refused .. => none

/-- One semantic answer in an exhaustive finite sweep. -/
structure SemanticEntry {V S Op : Type} [DecidableEq V]
    (P : HistoryMerge V S Op) (H : History V S Op) (F : Enumeration H.dag)
    (scopeDec : ∀ x y, Decidable (P.scope H x y)) where
  x : V
  y : V
  decision : SemanticDecision P H x y

/-- Evaluate the declared semantic policy over every ordered version pair. -/
def semanticSweep {V S Op : Type} [DecidableEq V]
    (P : HistoryMerge V S Op) (H : History V S Op) (F : Enumeration H.dag)
    (scopeDec : ∀ x y, Decidable (P.scope H x y)) :
    List (SemanticEntry P H F scopeDec) :=
  F.vertices.flatMap fun x =>
    F.vertices.map fun y => ⟨x, y, decideSemantic P H x y (scopeDec x y)⟩

/-- The semantic sweep cannot hide an unclaimed pair: every carrier pair has an
admitted decision or an explicit proof-backed refusal. -/
theorem semanticSweep_complete {V S Op : Type} [DecidableEq V]
    (P : HistoryMerge V S Op) (H : History V S Op) (F : Enumeration H.dag)
    (scopeDec : ∀ x y, Decidable (P.scope H x y)) (x y : V) :
    ∃ e, e ∈ semanticSweep P H F scopeDec ∧ e.x = x ∧ e.y = y := by
  let e : SemanticEntry P H F scopeDec :=
    ⟨x, y, decideSemantic P H x y (scopeDec x y)⟩
  refine ⟨e, ?_, rfl, rfl⟩
  simp only [semanticSweep, List.mem_flatMap, List.mem_map]
  exact ⟨x, F.complete x, y, F.complete y, rfl⟩

/-- No admitted semantic response escapes the policy's declared scope. -/
theorem SemanticDecision.result?_some_iff_scope {V S Op : Type}
    {P : HistoryMerge V S Op} {H : History V S Op} {x y : V}
    (d : SemanticDecision P H x y) :
    (∃ s, d.result? = some s) ↔ P.scope H x y := by
  cases d with
  | selected b hscope heq hlow => simp [SemanticDecision.result?, hscope]
  | ambiguous b₁ b₂ hscope heq h₁ h₂ hne => simp [SemanticDecision.result?, hscope]
  | unavailable hscope heq hno => simp [SemanticDecision.result?, hscope]
  | refused hscope => simp [SemanticDecision.result?, hscope]

/-- On every claimed pair, the semantic policy and finite graph engine agree on
the decision class.  In particular, an in-scope policy cannot turn finite
refusal into an admission. -/
theorem SemanticDecision.graph_kind_eq {V S Op : Type} [DecidableEq V]
    {P : HistoryMerge V S Op} {H : History V S Op} {x y : V}
    (F : Enumeration H.dag) (decision : SemanticDecision P H x y)
    (inScope : P.scope H x y) :
    (decidePair F x y).kind = decision.kind := by
  cases decision with
  | selected base scope selected lowest =>
      exact decidePair_selected_of_lowest F lowest
  | ambiguous first second scope selected firstMax secondMax distinct =>
      exact decidePair_ambiguous_of_maximal F firstMax secondMax distinct
  | unavailable scope selected noneCommon =>
      exact decidePair_unavailable_of_none F noneCommon
  | refused outOfScope => exact (outOfScope inScope).elim

/-! ## §3. Version-native patch branches and selected admission -/

variable {S Op : Type}

/-- A finite version branch that retains the exact patch producing its tip.
`versions` is graph evidence; `admitted`/`tip_eq` are operational evidence.
Neither is reconstructed from the other. -/
structure VersionPatch {V : Type} (H : History V S Op) (g : Guarded S Op)
    (base tip : V) where
  versions : Reaches H.dag base tip
  patch : Patch Op
  admitted : patch.Admitted g (H.state base)
  tip_eq : patch.exec g (H.state base) = H.state tip

/-- Forget a version patch to the state-level patch edge used by the residual
algebra. -/
def VersionPatch.toEdge {V : Type} {H : History V S Op} {g : Guarded S Op}
    {base tip : V} (branch : VersionPatch H g base tip) : PatchEdge g where
  parent := H.state base
  child := H.state tip
  patch := branch.patch
  admitted := branch.admitted
  child_eq := branch.tip_eq

/-- The retained patch witnesses state reachability. -/
theorem VersionPatch.reachable {V : Type} {H : History V S Op}
    {g : Guarded S Op} {base tip : V} (branch : VersionPatch H g base tip) :
    Reachable g.impl (H.state base) (H.state tip) :=
  branch.toEdge.reachable

/-- All evidence needed to drive a selected semantic decision through a
residual algebra. -/
structure SelectedRequest {V : Type} (P : HistoryMerge V S Op)
    (H : History V S Op) (g : Guarded S Op) (I : Invariant S) (x y : V) where
  base : V
  in_scope : P.scope H x y
  selected : P.select H x y = .selected base
  left : VersionPatch H g base x
  right : VersionPatch H g base y
  base_legal : I (H.state base)
  left_legal : I (H.state x)
  right_legal : I (H.state y)

/-- The semantic selector proof makes the request's base a certified lowest
common base. -/
theorem SelectedRequest.lowest {V : Type} {P : HistoryMerge V S Op}
    {H : History V S Op} {g : Guarded S Op} {I : Invariant S} {x y : V}
    (request : SelectedRequest P H g I x y) :
    LowestCommonBase H.dag x y request.base := by
  have valid := P.selectSound H x y request.in_scope
  simpa [request.selected] using valid

/-- The selected operational request is also selected by every covering finite
enumeration of the history DAG. -/
theorem SelectedRequest.graph_selected {V : Type} [DecidableEq V]
    {P : HistoryMerge V S Op} {H : History V S Op} {g : Guarded S Op}
    {I : Invariant S} {x y : V} (request : SelectedRequest P H g I x y)
    (F : Enumeration H.dag) : (decidePair F x y).kind = .selected :=
  decidePair_selected_of_lowest F request.lowest

/-- The admitted result of one selected merge: exact policy state, legal common
endpoint, and both residual continuations. -/
structure SelectedAdmission {V : Type} (P : HistoryMerge V S Op)
    (H : History V S Op) (g : Guarded S Op) (I : Invariant S) (x y : V) where
  base : V
  lowest : LowestCommonBase H.dag x y base
  merged : S
  policy_eq : P.result H x y = merged
  legal : I merged
  left : VersionPatch H g base x
  right : VersionPatch H g base y
  diamond : ResidualDiamond g left.toEdge right.toEdge merged

/-- A selected base plus explicit sibling patches and a residual algebra drives
an admitted, policy-identical merge. -/
def admitSelected {V : Type} {P : HistoryMerge V S Op}
    {H : History V S Op} {g : Guarded S Op} {I : Invariant S} {x y : V}
    (A : Algebra P.kernel g I) (request : SelectedRequest P H g I x y) :
    SelectedAdmission P H g I x y := by
  let merged := P.kernel.merge3 (H.state request.base) (H.state x) (H.state y)
  have policyEq : P.result H x y = merged := by
    unfold HistoryMerge.result HistoryMerge.apply HistoryMerge.decisionAt
    rw [request.selected]
    exact P.reconcileSelected _ _ _
  have diamond := A.residualDiamond request.left.toEdge request.right.toEdge rfl
    request.base_legal request.left_legal request.right_legal
  have legal : I merged := by
    dsimp [merged]
    rw [← request.left.tip_eq, ← request.right.tip_eq]
    exact A.legalUnderComposition (H.state request.base)
      request.left.patch request.right.patch request.base_legal
      request.left.admitted request.right.admitted
      (request.left.tip_eq ▸ request.left_legal)
      (request.right.tip_eq ▸ request.right_legal)
  exact
    { base := request.base
      lowest := request.lowest
      merged := merged
      policy_eq := policyEq
      legal := legal
      left := request.left
      right := request.right
      diamond := diamond }

/-! ## §4. Delivery and the exact duplicate-delivery premise -/

/-- Reapply one patch `n` times. -/
def repeatExec (g : Guarded S Op) (patch : Patch Op) : Nat → S → S
  | 0, state => state
  | n + 1, state => repeatExec g patch n (patch.exec g state)

/-- Every replay in a prefix is admitted. -/
def RepeatAdmitted (g : Guarded S Op) (patch : Patch Op) : Nat → S → Prop
  | 0, _ => True
  | n + 1, state => patch.Admitted g state ∧
      RepeatAdmitted g patch n (patch.exec g state)

/-- The additional law duplicate delivery needs: the patch is admitted and is
idempotent at its first endpoint.  Residual commutation does not imply it. -/
def ReplayStable {g : Guarded S Op} (edge : PatchEdge g) : Prop :=
  edge.patch.Admitted g edge.child ∧ edge.patch.exec g edge.child = edge.child

private theorem repeatExec_fixed (g : Guarded S Op) (patch : Patch Op) (state : S)
    (fixed : patch.exec g state = state) : ∀ n, repeatExec g patch n state = state := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [repeatExec, fixed, ih]

private theorem repeatAdmitted_fixed (g : Guarded S Op) (patch : Patch Op) (state : S)
    (admitted : patch.Admitted g state) (fixed : patch.exec g state = state) :
    ∀ n, RepeatAdmitted g patch n state := by
  intro n
  induction n with
  | zero => trivial
  | succ n ih => simpa [RepeatAdmitted, fixed] using And.intro admitted ih

/-- After any positive number of deliveries, a replay-stable patch edge remains
at its certified child. -/
theorem PatchEdge.repeatExec_succ {g : Guarded S Op} (edge : PatchEdge g)
    (stable : ReplayStable edge) (n : Nat) :
    repeatExec g edge.patch (n + 1) edge.parent = edge.child := by
  simp only [repeatExec, edge.child_eq]
  exact repeatExec_fixed g edge.patch edge.child stable.2 n

/-- Every delivery in that positive prefix is admitted. -/
theorem PatchEdge.repeatAdmitted_succ {g : Guarded S Op} (edge : PatchEdge g)
    (stable : ReplayStable edge) (n : Nat) :
    RepeatAdmitted g edge.patch (n + 1) edge.parent := by
  simp only [RepeatAdmitted]
  refine ⟨edge.admitted, ?_⟩
  rw [edge.child_eq]
  exact repeatAdmitted_fixed g edge.patch edge.child stable.1 stable.2 n

/-- One residual delivery to each sibling always converges; no replay premise is
needed for this one-shot result. -/
theorem ResidualDiamond.deliver_once_converges {g : Guarded S Op}
    {left right : PatchEdge g} {merged : S}
    (diamond : ResidualDiamond g left right merged) :
    diamond.leftToMerge.patch.exec g left.child =
      diamond.rightToMerge.patch.exec g right.child := by
  rw [← diamond.left_parent, ← diamond.right_parent,
    diamond.leftToMerge.child_eq, diamond.rightToMerge.child_eq,
    diamond.left_child, diamond.right_child]

/-- **Repeated-delivery convergence.** With the exact replay-stability premise,
arbitrary positive duplicate counts on the two replicas remain at the common
merge endpoint. -/
theorem ResidualDiamond.repeated_delivery_converges {g : Guarded S Op}
    {left right : PatchEdge g} {merged : S}
    (diamond : ResidualDiamond g left right merged)
    (leftStable : ReplayStable diamond.leftToMerge)
    (rightStable : ReplayStable diamond.rightToMerge) (m n : Nat) :
    repeatExec g diamond.leftToMerge.patch (m + 1) left.child =
      repeatExec g diamond.rightToMerge.patch (n + 1) right.child := by
  rw [← diamond.left_parent, ← diamond.right_parent,
    Uwueave.HistoryEngine.PatchEdge.repeatExec_succ diamond.leftToMerge leftStable,
    Uwueave.HistoryEngine.PatchEdge.repeatExec_succ diamond.rightToMerge rightStable,
    diamond.left_child, diamond.right_child]

/-- The same repeated-delivery theorem also retains admission of every replay. -/
theorem ResidualDiamond.repeated_delivery_admitted {g : Guarded S Op}
    {left right : PatchEdge g} {merged : S}
    (diamond : ResidualDiamond g left right merged)
    (leftStable : ReplayStable diamond.leftToMerge)
    (rightStable : ReplayStable diamond.rightToMerge) (m n : Nat) :
    RepeatAdmitted g diamond.leftToMerge.patch (m + 1) left.child ∧
      RepeatAdmitted g diamond.rightToMerge.patch (n + 1) right.child := by
  rw [← diamond.left_parent, ← diamond.right_parent]
  exact ⟨Uwueave.HistoryEngine.PatchEdge.repeatAdmitted_succ
      diamond.leftToMerge leftStable m,
    Uwueave.HistoryEngine.PatchEdge.repeatAdmitted_succ
      diamond.rightToMerge rightStable n⟩

/-! ## §5. Executable acceptance fixtures -/

/-- The one-node root DAG used to check the reflexive selected case. -/
inductive Root where
  | root
  deriving DecidableEq, Repr

def rootDag : VersionDag Root where
  parent := fun _ _ => false
  rank := fun _ => 0
  rank_lt := by intro p c; cases p <;> cases c <;> decide

def rootEnumeration : Enumeration rootDag where
  vertices := [.root]
  nodup := by decide
  complete := by intro v; cases v; decide

/-- A singleton selects itself as the exact lowest common base. -/
theorem root_pair_selected : (decidePair rootEnumeration .root .root).kind = .selected := by
  rfl

/-- The no-common-ancestor pair remains `unavailable`, not refused. -/
theorem two_pair_unavailable :
    (decidePair twoEnumeration .x .y).kind = .unavailable := by
  rfl

/-- The fork branches select their root. -/
theorem cc_branch_pair_selected :
    (decidePair ccEnumeration .left .right).kind = .selected := by
  rfl

/-- The criss-cross merge pair remains honestly ambiguous. -/
theorem cc_merge_pair_ambiguous :
    (decidePair ccEnumeration .mergeL .mergeR).kind = .ambiguous := by
  rfl

/-- The semantic engine admits the declared ambiguous pair. -/
theorem cc_semantic_pair_ambiguous :
    (decideSemantic ccExplicit ccHistory .mergeL .mergeR
      (isTrue ccScope_answers)).kind =
      .ambiguous := by
  simp [decideSemantic, ccExplicit, explicit, ccSelectLR,
    SemanticDecision.kind]

/-- The same all-pairs semantic engine explicitly refuses an undeclared pair. -/
private theorem cc_root_pair_out_of_scope :
    ¬ ccExplicit.scope ccHistory .root .root := by
  simp [ccExplicit, explicit, ccScope]

theorem cc_semantic_root_pair_refused :
    (decideSemantic ccExplicit ccHistory .root .root
      (isFalse cc_root_pair_out_of_scope)).kind = .refused := by
  rfl

/-! ### §5.1 A selected lock merge really grows a residual diamond -/

/-- Complete enumeration for the existing lock history. -/
def lockEnumeration : Enumeration lvDag where
  vertices := [.root, .alice, .bob, .m1, .m2, .j]
  nodup := by decide
  complete := by intro v; cases v <;> decide

/-- The root is the exact lowest base of the two lock grants.  The finite
candidate list makes the negative half executable. -/
theorem lock_root_lowest : LowestCommonBase lvDag .alice .bob .root := by
  refine ⟨lv_root_common, ?_⟩
  intro c hc
  have member := (mem_commonCandidates_iff lockEnumeration .alice .bob c).2 hc
  have exactCandidates :
      commonCandidates lockEnumeration .alice .bob = [.root] := by rfl
  rw [exactCandidates] at member
  simp only [List.mem_singleton] at member
  subst c
  exact Reaches.refl _ _

def lockForkSelect (_ : History LVer Lock LockOp) :
    LVer → LVer → MergeModel.BaseDecision LVer
  | .alice, .bob => .selected .root
  | .bob, .alice => .selected .root
  | _, _ => .unavailable

def lockForkScope (H : History LVer Lock LockOp) (x y : LVer) : Prop :=
  H.dag = lvDag ∧
    ((x = .alice ∧ y = .bob) ∨ (x = .bob ∧ y = .alice))

theorem lockForkSelect_sound : ∀ H x y, lockForkScope H x y →
    ValidInHistory H x y (lockForkSelect H x y) := by
  rintro H x y ⟨dag, hxy | hxy⟩ <;> obtain ⟨rfl, rfl⟩ := hxy
  · change LowestCommonBase H.dag .alice .bob .root
    rw [dag]
    exact lock_root_lowest
  · change LowestCommonBase H.dag .bob .alice .root
    rw [dag]
    exact lowestCommonBase_symm lock_root_lowest

/-- A narrow selected policy for the two grant versions. -/
def lockForkPolicy : HistoryMerge LVer Lock LockOp :=
  explicit lockAM lockPriority lockForkSelect lockForkScope lockForkSelect_sound

def lockRootToAlice : VersionPatch lockHistory lockOps .root .alice where
  versions := Or.inr (.direct (by decide))
  patch := [.grantAlice]
  admitted := by exact ⟨rfl, trivial⟩
  tip_eq := rfl

def lockRootToBob : VersionPatch lockHistory lockOps .root .bob where
  versions := Or.inr (.direct (by decide))
  patch := [.grantBob]
  admitted := by exact ⟨rfl, trivial⟩
  tip_eq := rfl

def lockForkRequest :
    SelectedRequest lockForkPolicy lockHistory lockOps AtMostOne .alice .bob where
  base := .root
  in_scope := ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  selected := rfl
  left := lockRootToAlice
  right := lockRootToBob
  base_legal := by decide
  left_legal := by decide
  right_legal := by decide

/-- The positive operational fixture: finite selection, semantic selection,
explicit branch patches, legal merge, and a residual diamond in one object. -/
def lockForkAdmission :
    SelectedAdmission lockForkPolicy lockHistory lockOps AtMostOne .alice .bob :=
  admitSelected cheapLockAlgebra.toAlgebra lockForkRequest

theorem lockFork_graph_selected :
    (decidePair lockEnumeration .alice .bob).kind = .selected :=
  lockForkRequest.graph_selected lockEnumeration

theorem lockFork_admission_is_legal : AtMostOne lockForkAdmission.merged :=
  lockForkAdmission.legal

theorem lockFork_deliver_once_converges :
    lockForkAdmission.diamond.leftToMerge.patch.exec lockOps
        lockForkAdmission.left.toEdge.child =
      lockForkAdmission.diamond.rightToMerge.patch.exec lockOps
        lockForkAdmission.right.toEdge.child :=
  Uwueave.HistoryEngine.ResidualDiamond.deliver_once_converges
    lockForkAdmission.diamond

/-- Cheap-lock residuals are replacement patches, so duplicate delivery really
does satisfy the extra replay premise. -/
theorem lockFork_left_replay_stable :
    ReplayStable lockForkAdmission.diamond.leftToMerge := by
  simp [lockForkAdmission, admitSelected, lockForkRequest, lockRootToAlice,
    lockRootToBob, cheapLockAlgebra, Algebra.residualDiamond, VersionPatch.toEdge,
    ReplayStable, lockResidual, lockForkPolicy, explicit, lockHistory, lvState,
    lockAM, lockMerge, lockOps, lockPatch, lockEff, lockPriority, Patch.Admitted,
    Patch.exec]

theorem lockFork_right_replay_stable :
    ReplayStable lockForkAdmission.diamond.rightToMerge := by
  simp [lockForkAdmission, admitSelected, lockForkRequest, lockRootToAlice,
    lockRootToBob, cheapLockAlgebra, Algebra.residualDiamond, VersionPatch.toEdge,
    ReplayStable, lockResidual, lockForkPolicy, explicit, lockHistory, lvState,
    lockAM, lockMerge, lockOps, lockPatch, lockEff, lockPriority, Patch.Admitted,
    Patch.exec]

/-- The concrete operational fixture therefore converges for arbitrary
positive duplicate counts, not merely one delivery. -/
theorem lockFork_repeated_delivery_converges (m n : Nat) :
    repeatExec lockOps lockForkAdmission.diamond.leftToMerge.patch (m + 1)
        lockForkAdmission.left.toEdge.child =
      repeatExec lockOps lockForkAdmission.diamond.rightToMerge.patch (n + 1)
        lockForkAdmission.right.toEdge.child :=
  Uwueave.HistoryEngine.ResidualDiamond.repeated_delivery_converges
    lockForkAdmission.diamond lockFork_left_replay_stable
      lockFork_right_replay_stable m n

/-- The length-two spend witness cannot supply even an uncosted residual
algebra.  This is the operational refusal point: both branches are admitted,
but no lawful residual admission object exists for ceiling three. -/
theorem counter_length_two_has_no_algebra :
    ¬ Nonempty (Algebra counterAM (spendOps 2) (fun n => n ≤ 3)) := by
  rintro ⟨A⟩
  exact counter_not_legalUnderComposition A.legalUnderComposition

/-- The exact admitted length-two branches are retained beside the refusal. -/
theorem counter_length_two_refusal_fixture :
    Patch.Admitted (spendOps 2) 0 [(), ()] ∧
      Patch.Admitted (spendOps 2) 0 [(), ()] ∧
      ¬ Nonempty (Algebra counterAM (spendOps 2) (fun n => n ≤ 3)) :=
  ⟨counter_two_patch_admitted, counter_two_patch_admitted,
    counter_length_two_has_no_algebra⟩

end Uwueave.HistoryEngine
