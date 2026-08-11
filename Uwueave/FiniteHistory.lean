/-
# Uwueave.FiniteHistory — certified search on an explicitly finite version DAG.

This module pays the finite, executable part of the merge-base frontier.  Its
premise is deliberately visible: the caller supplies a duplicate-free list
containing every vertex.  Nothing here decides reachability on an arbitrary or
infinite `VersionDag`, and nothing turns `VersionDag.rank` into a discovered
acyclicity certificate.

The search is proof-carrying.  Reachability is decided by bounded path search;
base answers reuse `Histories.BaseSelection`; and every answer also exposes the
complete filtered list of common ancestors.  A separate all-pairs checker turns
a proposed raw `MergeModel.BaseDecision` policy into a certificate covering
every ordered pair in the supplied enumeration.
-/
import Uwueave.Histories

namespace Uwueave.FiniteHistory

open Uwueave Uwueave.Histories

/-! ## §1. The finite premise and bounded reachability -/

/-- An explicit finite enumeration of all vertices of `D`.

`nodup` makes the list a genuine enumeration rather than merely a search list;
`complete` is the premise that justifies every negative search result. -/
structure Enumeration {V : Type} [DecidableEq V] (D : VersionDag V) where
  vertices : List V
  nodup : vertices.Nodup
  complete : ∀ v, v ∈ vertices

/-- A finite-list existential, kept in `Prop` so path search has no hidden
carrier-level choice. -/
inductive AnyIn {α : Type} (P : α → Prop) : List α → Prop where
  | head {x xs} : P x → AnyIn P (x :: xs)
  | tail {x xs} : AnyIn P xs → AnyIn P (x :: xs)

/-- A path with at most `fuel` edges, searched backwards from its endpoint.
The backwards orientation follows `Ancestry.extend`, so extending a certified
path by its final parent edge is definitionally one search step. -/
def BoundedReaches {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) : Nat → V → V → Prop
  | 0, a, b => a = b
  | fuel + 1, a, b =>
      a = b ∨ AnyIn (fun p => BoundedReaches F fuel a p ∧ D.parent p b = true) F.vertices

private theorem any_of_mem {α : Type} {P : α → Prop} {xs : List α} {x : α}
    (hx : x ∈ xs) (hP : P x) : AnyIn P xs := by
  induction xs with
  | nil => exact False.elim (by simp at hx)
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with hxy | hx
      · subst y
        exact .head hP
      · exact .tail (ih hx)

private theorem any_exists {α : Type} {P : α → Prop} {xs : List α}
    (h : AnyIn P xs) : ∃ x, x ∈ xs ∧ P x := by
  induction h with
  | @head x xs hx => exact ⟨x, List.Mem.head _, hx⟩
  | @tail x xs h ih => exact ⟨ih.choose, List.Mem.tail _ ih.choose_spec.1, ih.choose_spec.2⟩

private theorem AnyIn.map {α : Type} {P Q : α → Prop} {xs : List α}
    (h : AnyIn P xs) (f : ∀ x, P x → Q x) : AnyIn Q xs := by
  induction h with
  | @head x xs hx => exact .head (f x hx)
  | @tail x xs h ih => exact .tail ih

/-- A finite-list existential is decidable when its element predicate is. -/
def decideExistsIn {α : Type} (xs : List α) (P : α → Prop)
    (decP : ∀ x, Decidable (P x)) : Decidable (∃ x, x ∈ xs ∧ P x) :=
  match xs with
  | [] => isFalse (by simp)
  | x :: rest =>
      match decP x with
      | isTrue hx => isTrue ⟨x, List.Mem.head _, hx⟩
      | isFalse hx =>
          match decideExistsIn rest P decP with
          | isTrue h =>
              isTrue ⟨h.choose, List.Mem.tail _ h.choose_spec.1, h.choose_spec.2⟩
          | isFalse h =>
              isFalse (by
                rintro ⟨y, hy, hPy⟩
                rcases List.mem_cons.mp hy with rfl | hy
                · exact hx hPy
                · exact h ⟨y, hy, hPy⟩)

/-- A finite-list universal is decidable when its element predicate is. -/
def decideForallIn {α : Type} (xs : List α) (P : α → Prop)
    (decP : ∀ x, Decidable (P x)) : Decidable (∀ x, x ∈ xs → P x) :=
  match xs with
  | [] => isTrue (by simp)
  | x :: rest =>
      match decP x with
      | isFalse hx => isFalse (fun h => hx (h x (List.Mem.head _)))
      | isTrue hx =>
          match decideForallIn rest P decP with
          | isFalse h =>
              isFalse (fun hall => h (fun y hy => hall y (List.Mem.tail _ hy)))
          | isTrue h =>
              isTrue (by
                intro y hy
                rcases List.mem_cons.mp hy with rfl | hy
                · exact hx
                · exact h y hy)

/-- Quantification over the carrier is decidable from a covering enumeration. -/
def Enumeration.decideExists {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (P : V → Prop) (decP : ∀ x, Decidable (P x)) :
    Decidable (∃ x, P x) :=
  match decideExistsIn F.vertices P decP with
  | isTrue h => isTrue ⟨h.choose, h.choose_spec.2⟩
  | isFalse h => isFalse (fun hex => h ⟨hex.choose, F.complete _, hex.choose_spec⟩)

/-- Universal quantification over the carrier is decidable from coverage. -/
def Enumeration.decideForall {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (P : V → Prop) (decP : ∀ x, Decidable (P x)) :
    Decidable (∀ x, P x) :=
  match decideForallIn F.vertices P decP with
  | isTrue h => isTrue (fun x => h x (F.complete x))
  | isFalse h => isFalse (fun hall => h (fun x _ => hall x))

/-- A bounded certificate remains valid with one additional unit of fuel. -/
theorem bounded_succ {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) {fuel : Nat} {a b : V}
    (h : BoundedReaches F fuel a b) : BoundedReaches F (fuel + 1) a b := by
  induction fuel generalizing a b with
  | zero =>
      simp only [BoundedReaches] at h ⊢
      exact Or.inl h
  | succ fuel ih =>
      simp only [BoundedReaches] at h ⊢
      rcases h with hab | hpath
      · exact Or.inl hab
      · exact Or.inr (hpath.map fun p hp => ⟨ih hp.1, hp.2⟩)

/-- Bounded reachability is monotone in its fuel. -/
theorem bounded_mono {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) {n m : Nat} {a b : V} (hnm : n ≤ m)
    (h : BoundedReaches F n a b) : BoundedReaches F m a b := by
  induction hnm with
  | refl => exact h
  | @step m hnm ih => exact bounded_succ F ih

/-- Bounded search is sound for `Histories.Reaches`. -/
theorem bounded_sound {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) {fuel : Nat} {a b : V}
    (h : BoundedReaches F fuel a b) : Reaches D a b := by
  induction fuel generalizing a b with
  | zero => exact Or.inl h
  | succ fuel ih =>
      rcases h with hab | hpath
      · exact Or.inl hab
      · obtain ⟨p, _, hp, edge⟩ := any_exists hpath
        exact (ih hp).trans (Or.inr (.direct edge))

/-- Search with the endpoint rank as fuel is complete. -/
theorem reaches_bounded {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) {a b : V} (h : Reaches D a b) :
    BoundedReaches F (D.rank b) a b := by
  rcases h with h | h
  · subst b
    cases D.rank a <;> simp [BoundedReaches]
  · induction h with
    | direct e =>
        have hone : BoundedReaches F 1 _ _ :=
          Or.inr (any_of_mem (F.complete _) ⟨rfl, e⟩)
        have hr := D.rank_lt _ _ e
        exact bounded_mono F (by omega) hone
    | extend h e ih =>
        have hstep : BoundedReaches F (D.rank _ + 1) _ _ :=
          Or.inr (any_of_mem (F.complete _) ⟨ih, e⟩)
        exact bounded_mono F (D.rank_lt _ _ e) hstep

/-- The exact correctness theorem for finite bounded reachability. -/
theorem reaches_iff_bounded {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (a b : V) :
    Reaches D a b ↔ BoundedReaches F (D.rank b) a b :=
  ⟨reaches_bounded F, bounded_sound F⟩

/-- Bounded reachability itself is decidable by scanning the enumeration. -/
def decideBounded {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) : ∀ fuel a b, Decidable (BoundedReaches F fuel a b)
  | 0, a, b =>
      match (inferInstance : Decidable (a = b)) with
      | isTrue h => isTrue h
      | isFalse h => isFalse h
  | fuel + 1, a, b => by
      cases (inferInstance : Decidable (a = b)) with
      | isTrue h => exact isTrue (Or.inl h)
      | isFalse h =>
          let decP : ∀ p, Decidable
              (BoundedReaches F fuel a p ∧ D.parent p b = true) := fun p =>
            @instDecidableAnd _ _ (decideBounded F fuel a p) inferInstance
          cases decideExistsIn F.vertices
              (fun p => BoundedReaches F fuel a p ∧ D.parent p b = true) decP with
          | isTrue hex =>
              exact isTrue (Or.inr (any_of_mem hex.choose_spec.1 hex.choose_spec.2))
          | isFalse hno =>
              exact isFalse (by
                intro hr
                rcases hr with heq | hany
                · exact h heq
                · obtain ⟨p, hp, hP⟩ := any_exists hany
                  exact hno ⟨p, hp, hP⟩)

/-- Certified decidable reachability, available only through an enumeration. -/
def Enumeration.decideReaches {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (a b : V) : Decidable (Reaches D a b) :=
  match decideBounded F (D.rank b) a b with
  | isTrue h => isTrue (bounded_sound F h)
  | isFalse h => isFalse (fun hr => h (reaches_bounded F hr))

/-! ## §2. Decidable base predicates and certified search -/

private def decideImp {P Q : Prop} (dP : Decidable P) (dQ : Decidable Q) :
    Decidable (P → Q) :=
  match dP, dQ with
  | isFalse hP, _ => isTrue (fun h => False.elim (hP h))
  | isTrue _, isTrue hQ => isTrue (fun _ => hQ)
  | isTrue hP, isFalse hQ => isFalse (fun h => hQ (h hP))

/-- Common ancestry is decidable under the finite premise. -/
def Enumeration.decideCommonAncestor {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) (x y b : V) :
    Decidable (CommonAncestor D x y b) :=
  match F.decideReaches b x, F.decideReaches b y with
  | isTrue hx, isTrue hy => isTrue ⟨hx, hy⟩
  | isFalse hx, _ => isFalse (fun h => hx h.1)
  | _, isFalse hy => isFalse (fun h => hy h.2)

/-- The exact lowest-base predicate is decidable; this is stronger than merely
finding a common ancestor with high rank. -/
def Enumeration.decideLowestCommonBase {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) (x y b : V) :
    Decidable (LowestCommonBase D x y b) :=
  match F.decideCommonAncestor x y b with
  | isFalse h => isFalse (fun hlow => h hlow.1)
  | isTrue hcommon =>
      match F.decideForall
          (fun c => CommonAncestor D x y c → Reaches D c b)
          (fun c => decideImp (F.decideCommonAncestor x y c) (F.decideReaches c b)) with
      | isTrue hleast => isTrue ⟨hcommon, hleast⟩
      | isFalse hleast => isFalse (fun hlow => hleast hlow.2)

/-- The exact maximal-base predicate is decidable. -/
def Enumeration.decideMaximalCommonBase {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) (x y b : V) :
    Decidable (MaximalCommonBase D x y b) :=
  match F.decideCommonAncestor x y b with
  | isFalse h => isFalse (fun hmax => h hmax.1)
  | isTrue hcommon =>
      let decClause : ∀ c, Decidable
          (CommonAncestor D x y c → Reaches D b c → c = b) := fun c =>
        decideImp (F.decideCommonAncestor x y c)
          (decideImp (F.decideReaches b c) (inferInstance : Decidable (c = b)))
      match F.decideForall
          (fun c => CommonAncestor D x y c → Reaches D b c → c = b) decClause with
      | isTrue hmax => isTrue ⟨hcommon, hmax⟩
      | isFalse hmax => isFalse (fun h => hmax h.2)

/-- A finite search can decide whether any lowest base exists. -/
def Enumeration.decideExistsLowest {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) (x y : V) :
    Decidable (∃ b, LowestCommonBase D x y b) :=
  F.decideExists (fun b => LowestCommonBase D x y b)
    (fun b => F.decideLowestCommonBase x y b)

/-- A finite search can decide that no common base exists. -/
def Enumeration.decideUnavailable {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) (x y : V) :
    Decidable (∀ b, ¬ CommonAncestor D x y b) :=
  F.decideForall (fun b => ¬ CommonAncestor D x y b)
    (fun b =>
      match F.decideCommonAncestor x y b with
      | isTrue h => isFalse (fun hn => hn h)
      | isFalse h => isTrue h)

/-- A finite search can decide whether two distinct maximal bases witness the
honest ambiguous case. -/
def Enumeration.decideAmbiguous {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) (x y : V) :
    Decidable (∃ b₁ b₂, MaximalCommonBase D x y b₁ ∧
      MaximalCommonBase D x y b₂ ∧ b₁ ≠ b₂) :=
  F.decideExists
    (fun b₁ => ∃ b₂, MaximalCommonBase D x y b₁ ∧
      MaximalCommonBase D x y b₂ ∧ b₁ ≠ b₂)
    (fun b₁ =>
      F.decideExists
        (fun b₂ => MaximalCommonBase D x y b₁ ∧
          MaximalCommonBase D x y b₂ ∧ b₁ ≠ b₂)
        (fun b₂ =>
          @instDecidableAnd _ _ (F.decideMaximalCommonBase x y b₁)
            (@instDecidableAnd _ _ (F.decideMaximalCommonBase x y b₂)
              (inferInstance : Decidable (b₁ ≠ b₂)))))

/-- Executable finite search that returns its witness and proof together. -/
def findCertified {α : Type} (xs : List α) (P : α → Prop)
    (decP : ∀ x, Decidable (P x)) : Option {x // P x} :=
  match xs with
  | [] => none
  | x :: rest =>
      match decP x with
      | isTrue h => some ⟨x, h⟩
      | isFalse _ => findCertified rest P decP

/-- Search the enumeration for a certified lowest base. -/
def findLowest {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) : Option {b // LowestCommonBase D x y b} :=
  findCertified F.vertices (fun b => LowestCommonBase D x y b)
    (fun b => F.decideLowestCommonBase x y b)

/-- Ordered pairs from the supplied finite enumeration. -/
def orderedPairs {V : Type} (xs : List V) : List (V × V) :=
  xs.flatMap (fun x => xs.map (fun y => (x, y)))

/-- Search the finite ordered-pair list for two distinct maximal bases. -/
def findAmbiguous {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) :
    Option {p : V × V // MaximalCommonBase D x y p.1 ∧
      MaximalCommonBase D x y p.2 ∧ p.1 ≠ p.2} :=
  findCertified (orderedPairs F.vertices)
    (fun p => MaximalCommonBase D x y p.1 ∧
      MaximalCommonBase D x y p.2 ∧ p.1 ≠ p.2)
    (fun p =>
      @instDecidableAnd _ _ (F.decideMaximalCommonBase x y p.1)
        (@instDecidableAnd _ _ (F.decideMaximalCommonBase x y p.2)
          (inferInstance : Decidable (p.1 ≠ p.2))))

/-- The three-valued finite merge-base search.  `none` is deliberately not
relabelled as `unavailable`: it says only that none of the three certified
constructors was obtained. -/
def searchSelection {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) : Option (BaseSelection D x y) :=
  match findLowest F x y with
  | some h => some (.selected h.1 h.2)
  | none =>
      match F.decideUnavailable x y with
      | isTrue h => some (.unavailable h)
      | isFalse _ =>
          match findAmbiguous F x y with
          | some h =>
              some (.ambiguous h.1.1 h.1.2 h.2.1 h.2.2.1 h.2.2.2)
          | none => none

private def decisionBool {P : Prop} : Decidable P → Bool
  | isTrue _ => true
  | isFalse _ => false

private theorem decisionBool_eq_true {P : Prop} (d : Decidable P) :
    decisionBool d = true ↔ P := by
  cases d with
  | isTrue h => simp [decisionBool, h]
  | isFalse h => simp [decisionBool, h]

/-- The complete filtered list of common ancestors of a pair. -/
def commonCandidates {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) : List V :=
  F.vertices.filter (fun b => decisionBool (F.decideCommonAncestor x y b))

/-- Filtering loses no common ancestor because `F.complete` covers the carrier. -/
theorem mem_commonCandidates_iff {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y b : V) :
    b ∈ commonCandidates F x y ↔ CommonAncestor D x y b := by
  rw [commonCandidates, List.mem_filter, decisionBool_eq_true]
  exact and_iff_right (F.complete b)

/-- A merge-base answer together with its exhaustive finite common-ancestor
witness list.  In particular, ambiguity and unavailability retain the complete
evidence set instead of discarding it after classification. -/
structure CertifiedSelection {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) where
  selection : BaseSelection D x y
  common : List V
  common_exact : ∀ b, b ∈ common ↔ CommonAncestor D x y b

/-- Attach the exhaustive candidate list to any proof-carrying answer. -/
def certifySelection {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) {x y : V} (s : BaseSelection D x y) :
    CertifiedSelection F x y where
  selection := s
  common := commonCandidates F x y
  common_exact := mem_commonCandidates_iff F x y

/-- Certified search with exhaustive witnesses. -/
def searchCertified {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) : Option (CertifiedSelection F x y) :=
  (searchSelection F x y).map (certifySelection F)

/-! ## §3. Raw decisions, all-pairs sweeps, and policy checking -/

/-- Exact version-DAG legality for the raw decision type consumed by
`HistoryPolicy.HistoryMerge.select`. -/
def DecisionValid {V : Type} (D : VersionDag V) (x y : V) :
    MergeModel.BaseDecision V → Prop
  | .selected b => LowestCommonBase D x y b
  | .ambiguous b₁ b₂ =>
      MaximalCommonBase D x y b₁ ∧ MaximalCommonBase D x y b₂ ∧ b₁ ≠ b₂
  | .unavailable => ∀ b, ¬ CommonAncestor D x y b

/-- Erase only the proofs from an honest history-level selection. -/
def toDecision {V : Type} {D : VersionDag V} {x y : V} :
    BaseSelection D x y → MergeModel.BaseDecision V
  | .selected b _ => .selected b
  | .ambiguous b₁ b₂ _ _ _ => .ambiguous b₁ b₂
  | .unavailable _ => .unavailable

/-- Proof erasure preserves exact history-level legality. -/
theorem toDecision_valid {V : Type} {D : VersionDag V} {x y : V}
    (s : BaseSelection D x y) : DecisionValid D x y (toDecision s) := by
  cases s with
  | selected b h => exact h
  | ambiguous b₁ b₂ h₁ h₂ hne => exact ⟨h₁, h₂, hne⟩
  | unavailable h => exact h

/-- Raw decision legality is decidable under the same finite premise. -/
def Enumeration.decideDecisionValid {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) (x y : V)
    (d : MergeModel.BaseDecision V) : Decidable (DecisionValid D x y d) :=
  match d with
  | .selected b => F.decideLowestCommonBase x y b
  | .ambiguous b₁ b₂ =>
      @instDecidableAnd _ _ (F.decideMaximalCommonBase x y b₁)
        (@instDecidableAnd _ _ (F.decideMaximalCommonBase x y b₂)
          (inferInstance : Decidable (b₁ ≠ b₂)))
  | .unavailable => F.decideUnavailable x y

/-- A raw selector is licensed on every ordered pair of the finite carrier. -/
def PolicyValid {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (select : V → V → MergeModel.BaseDecision V) : Prop :=
  ∀ x, x ∈ F.vertices → ∀ y, y ∈ F.vertices → DecisionValid D x y (select x y)

/-- Proof-carrying all-pairs policy checker.  Its negative branch is a proof
that the proposed selector fails somewhere; its positive branch certifies every
ordered pair covered by the enumeration. -/
def checkPolicy {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (select : V → V → MergeModel.BaseDecision V) :
    Decidable (PolicyValid F select) :=
  decideForallIn F.vertices
    (fun x => ∀ y, y ∈ F.vertices → DecisionValid D x y (select x y))
    (fun x => decideForallIn F.vertices
      (fun y => DecisionValid D x y (select x y))
      (fun y => F.decideDecisionValid x y (select x y)))

/-- Boolean projection of the proof-carrying checker for deployment-facing
tests.  The theorem below, not the boolean alone, is its specification. -/
def policyAccepted {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (select : V → V → MergeModel.BaseDecision V) : Bool :=
  decisionBool (checkPolicy F select)

/-- Exact acceptance theorem for the whole finite-DAG policy checker. -/
theorem policyAccepted_iff {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (select : V → V → MergeModel.BaseDecision V) :
    policyAccepted F select = true ↔ PolicyValid F select :=
  decisionBool_eq_true _

/-- One entry in the explicit all-ordered-pairs search sweep. -/
structure SweepEntry {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) where
  x : V
  y : V
  answer : Option (CertifiedSelection F x y)

/-- The explicit finite ordered-pair sweep. -/
def sweepEntries {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) : List (SweepEntry F) :=
  F.vertices.flatMap (fun x =>
    F.vertices.map (fun y => ⟨x, y, searchCertified F x y⟩))

/-- The sweep contains an entry for every ordered pair in the carrier. -/
theorem sweepEntries_complete {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) :
    ∃ e, e ∈ sweepEntries F ∧ e.x = x ∧ e.y = y := by
  let e : SweepEntry F := ⟨x, y, searchCertified F x y⟩
  refine ⟨e, ?_, rfl, rfl⟩
  simp only [sweepEntries, List.mem_flatMap, List.mem_map]
  refine ⟨x, F.complete x, ?_⟩
  exact ⟨y, F.complete y, rfl⟩

/-! ## §4. Executable fixtures -/

/-- Complete enumeration of the seven-node criss-cross fixture. -/
def ccEnumeration : Enumeration ccDag where
  vertices := [.root, .left, .right, .mergeL, .mergeR, .joinLeft, .joinRight]
  nodup := by decide
  complete := by intro v; cases v <;> decide

/-- Complete enumeration of the edgeless two-node fixture. -/
def twoEnumeration : Enumeration twoDag where
  vertices := [.x, .y]
  nodup := by decide
  complete := by intro v; cases v <;> decide

/-- Observable result shape, with proof fields erased. -/
inductive SelectionKind where
  | selected
  | ambiguous
  | unavailable
  deriving DecidableEq, Repr

/-- The result shape of a proof-carrying selection. -/
def selectionKind {V : Type} {D : VersionDag V} {x y : V} :
    BaseSelection D x y → SelectionKind
  | .selected _ _ => .selected
  | .ambiguous _ _ _ _ _ => .ambiguous
  | .unavailable _ => .unavailable

/-- The branch pair computes the already-proved root selection. -/
theorem cc_root_pair_selected :
    (searchSelection ccEnumeration .left .right).map selectionKind =
      some .selected := by
  rfl

/-- The selected constructor names `root`, not merely some common ancestor. -/
theorem cc_root_pair_decision :
    (searchSelection ccEnumeration .left .right).map toDecision =
      some (.selected .root) := by
  rfl

/-- The criss-cross merge pair computes the honest ambiguous answer. -/
theorem cc_merge_pair_ambiguous :
    (searchSelection ccEnumeration .mergeL .mergeR).map selectionKind =
      some .ambiguous := by
  rfl

/-- The ambiguous constructor retains the two exact maximal bases. -/
theorem cc_merge_pair_decision :
    (searchSelection ccEnumeration .mergeL .mergeR).map toDecision =
      some (.ambiguous .left .right) := by
  rfl

/-- The edgeless pair computes unavailable, not ambiguous or an arbitrary base. -/
theorem two_pair_unavailable :
    (searchSelection twoEnumeration .x .y).map selectionKind =
      some .unavailable := by
  rfl

/-- The no-common-base fixture returns the exact raw unavailable decision. -/
theorem two_pair_decision :
    (searchSelection twoEnumeration .x .y).map toDecision = some .unavailable := by
  rfl

/-- The criss-cross exhaustive witness list is exactly root, left, and right. -/
theorem cc_common_candidates_exact :
    commonCandidates ccEnumeration .mergeL .mergeR = [.root, .left, .right] := by
  rfl

/-- The unavailable fixture retains the exhaustive empty witness list. -/
theorem two_common_candidates_empty :
    commonCandidates twoEnumeration .x .y = [] := by
  rfl

/-- Selecting one criss-cross maximal base as though it were a *lowest* base is
rejected by the exact raw-decision contract. -/
theorem cc_nonlowest_selected_rejected :
    ¬ DecisionValid ccDag .mergeL .mergeR (.selected .left) := by
  intro h
  exact cc_no_lowest ⟨.left, h⟩

/-- A whole-DAG policy that always lies by selecting `left` is rejected by the
all-ordered-pairs checker, witnessed already at `(mergeL, mergeR)`. -/
theorem cc_constant_left_policy_rejected :
    policyAccepted ccEnumeration (fun _ _ => .selected .left) = false := by
  have hbad : ¬ PolicyValid ccEnumeration (fun _ _ => .selected .left) := by
    intro h
    exact cc_nonlowest_selected_rejected
      (h .mergeL (ccEnumeration.complete _) .mergeR (ccEnumeration.complete _))
  cases hcheck : checkPolicy ccEnumeration (fun _ _ => .selected .left) with
  | isTrue h => exact False.elim (hbad h)
  | isFalse _ => rfl

end Uwueave.FiniteHistory
