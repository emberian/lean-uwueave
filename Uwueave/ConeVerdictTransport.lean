import Uwueave.Ancestral

namespace Uwueave.ConeVerdictTransport
open Ancestral

abbrev Path := String
abbrev BlobHash := String
abbrev Tree := Path → Option BlobHash

inductive Verdict where | pass | fail deriving DecidableEq

/-- On incompatible edits this total model returns the base value. Git admits
    only clean links to the train. The transport law depends only on its final tree. -/
def ancestralMerge (base left right : Tree) : Tree := fun p =>
  if left p = base p then right p else if right p = base p then left p
  else if left p = right p then left p else base p

def treeMerge : AncestralMerge Tree where
  merge3 := ancestralMerge
  comm b x y := by
    funext p
    by_cases hx : x p = b p <;> by_cases hy : y p = b p <;>
      by_cases he : x p = y p <;> simp_all [ancestralMerge, eq_comm]
  fastforward b y := by funext p; simp [ancestralMerge]

def disjointDiffs (base left right : Tree) := ∀ p, left p = base p ∨ right p = base p

def ConePureGate (G : Tree → Verdict) (K : List Path) :=
  ∀ a b, (∀ p ∈ K, a p = b p) → G a = G b

structure ConeVerdictReceipt where
  gateHash : String
  toolchainHash : String
  cone : List Path
  coneDigestMap : (p : Path) → p ∈ cone → Option BlobHash
  verdict : Verdict

def Valid (r : ConeVerdictReceipt) (G : Tree → Verdict) (gate tools : String) (C : Tree) :=
  r.gateHash = gate ∧ r.toolchainHash = tools ∧
  (∀ p (h : p ∈ r.cone), r.coneDigestMap p h = C p) ∧ r.verdict = G C

theorem cone_verdict_transports_across_rebase {r G gate tools C M}
    (pureGate : ConePureGate G r.cone) (valid : Valid r G gate tools C)
    (passed : r.verdict = .pass) (same : ∀ p (h : p ∈ r.cone), M p = r.coneDigestMap p h) :
    G M = .pass :=
  (pureGate M C (fun p h => (same p h).trans (valid.2.2.1 p h))).trans
    (valid.2.2.2.symm.trans passed)

def stack (base tip : Tree) (siblings : List Tree) : Tree :=
  siblings.foldl (treeMerge.merge3 base) tip

theorem batch_train_cone_transport_sound {r G gate tools base C siblings}
    (pureGate : ConePureGate G r.cone) (valid : Valid r G gate tools C)
    (passed : r.verdict = .pass) (same : ∀ p ∈ r.cone, stack base C siblings p = C p) :
    G (stack base C siblings) = .pass :=
  cone_verdict_transports_across_rebase pureGate valid passed
    (fun p h => (same p h).trans (valid.2.2.1 p h).symm)

/-- Equality is necessary when a reuse decision must work for *all* pure gates. -/
theorem universal_transport_iff (a b : Tree) (K : List Path) :
    (∀ G, ConePureGate G K → G a = G b) ↔ ∀ p ∈ K, a p = b p := by
  constructor
  · intro all p hp
    let probe : Tree → Verdict := fun t => if t p = a p then .pass else .fail
    have eq := all probe (fun x y same => by simp only [probe, same p hp])
    by_cases equal : a p = b p
    · exact equal
    · simp [probe, Ne.symm equal] at eq
  · intro same G pureGate
    exact pureGate a b same

def initial : Tree := fun _ => some "old"
def edit (path : Path) : Tree := fun p => if p = path then some "new" else initial p
def importsCompatible (t : Tree) : Verdict :=
  if t "f" = some "new" ∧ t "d" = some "new" then .fail else .pass

theorem imports_pure : ConePureGate importsCompatible ["f", "d"] := by
  intro a b same
  simp only [importsCompatible, same "f" (by decide), same "d" (by decide)]

def fileReceipt : ConeVerdictReceipt :=
  ⟨"gate", "tools", ["f", "d"], fun p _ => edit "f" p, .pass⟩

theorem disjoint_sibling_transports :
    Valid fileReceipt importsCompatible "gate" "tools" (edit "f") ∧
    edit "q" ≠ initial ∧ importsCompatible (stack initial (edit "f") [edit "q"]) = .pass := by
  refine ⟨⟨rfl, rfl, fun _ _ => rfl, rfl⟩, ?_, rfl⟩
  intro eq
  have h := congrFun eq "q"
  contradiction

theorem naive_tip_rebase_unsound_on_transitive_edit :
    disjointDiffs initial (edit "d") (edit "f") ∧
    edit "f" "d" = initial "d" ∧ edit "d" "d" ≠ initial "d" ∧
    importsCompatible (edit "d") = .pass ∧ importsCompatible (edit "f") = .pass ∧
    importsCompatible (treeMerge.merge3 initial (edit "d") (edit "f")) = .fail := by
  refine ⟨?_, rfl, by decide, rfl, rfl, rfl⟩
  intro p
  by_cases h : p = "d"
  · subst p; exact Or.inr rfl
  · exact Or.inl (by simp [edit, h])

/-- Executable bisection returns a checked adjacent pass/fail boundary.
    No monotonicity assumption is needed, even for an interaction failure. -/
def bisect (gate : Nat → Verdict) (lo hi : Nat) (lt : lo < hi)
    (good : gate lo = .pass) (bad : gate hi = .fail) :
    { i // lo ≤ i ∧ i < hi ∧ gate i = .pass ∧ gate (i+1) = .fail } := by
  if adjacent : hi = lo+1 then
    exact ⟨lo, Nat.le_refl _, lt, good, adjacent ▸ bad⟩
  else
    let mid := lo + (hi-lo)/2
    have left : lo < mid := by dsimp [mid]; omega
    have right : mid < hi := by dsimp [mid]; omega
    cases result : gate mid with
    | pass =>
      obtain ⟨i, lower, upper, before, after⟩ := bisect gate mid hi right result bad
      exact ⟨i, by omega, upper, before, after⟩
    | fail =>
      obtain ⟨i, lower, upper, before, after⟩ := bisect gate lo mid left good result
      exact ⟨i, lower, by omega, before, after⟩
termination_by hi-lo
decreasing_by all_goals omega

theorem bisect_isolates_culprit (G : Tree → Verdict) (prefixTree : Nat → Tree) {k : Nat}
    (hk : 0 < k) (base : G (prefixTree 0) = .pass) (batch : G (prefixTree k) = .fail) :
    ∃ i < k, G (prefixTree i) = .pass ∧ G (prefixTree (i+1)) = .fail := by
  obtain ⟨i, _, bound, before, after⟩ := bisect (G ∘ prefixTree) 0 k hk base batch
  exact ⟨i, bound, before, after⟩

/-- info: 'Uwueave.ConeVerdictTransport.cone_verdict_transports_across_rebase' does not depend on any axioms -/
#guard_msgs in
#print axioms cone_verdict_transports_across_rebase
/-- info: 'Uwueave.ConeVerdictTransport.batch_train_cone_transport_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batch_train_cone_transport_sound
/-- info: 'Uwueave.ConeVerdictTransport.universal_transport_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms universal_transport_iff
/-- info: 'Uwueave.ConeVerdictTransport.disjoint_sibling_transports' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms disjoint_sibling_transports
/-- info: 'Uwueave.ConeVerdictTransport.naive_tip_rebase_unsound_on_transitive_edit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms naive_tip_rebase_unsound_on_transitive_edit
/-- info: 'Uwueave.ConeVerdictTransport.bisect_isolates_culprit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bisect_isolates_culprit
end Uwueave.ConeVerdictTransport
