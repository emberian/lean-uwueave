/-
# Uwueave.KernelCFCS — embedding the move kernel as a `Necessity.Impl`.

`Necessity.lean` defines the Bailis CFCS model (`Impl`, `IsCFCS`).
`ExecRefine.lean` proves that `absReplay` yields an acyclic derived view on
*every* op array over a grounded structural base (`absReplay_acyclic`).
This file wires the two together.

## Honesty about CFCS here

Under `GroundedBase`, `DerivedAcyclic` holds of **every** log: its body
quantifies over materializations, but `absReplay_acyclic` ignores log
membership and fires on any `Array Op`. Local safety and I-confluence of
`DerivedAcyclic` are therefore free — `IsCFCS` via
`iconfluent_implies_cfcs` is an embedding check, not a new confluence
argument. The interesting content is the **shape of the embedding**:

  * state = grow-only set of kernel ops (`GSet Op`);
  * `tryApply` = insert (always commits; cycle control is not a local abort);
  * the invariant speaks about `absReplay` on finite materializations of that set.

If you want a nontrivial confluence proof, look at `Necessity` itself
(e.g. G-Set membership) or at the edge-set counterexample
(`Acyclicity.acyclicity_not_iconfluent`) that this pattern exits.

## What *is* load-bearing here

  1. **DecidableEq / Impl packaging** — the shipping op alphabet as a
     `Necessity.Impl` over a lattice already in the catalog.
  2. **Materialization** — relating the abstract log (`α → Bool`) to the
     concrete arrays `absReplay` consumes, with theorems that *use*
     membership (insert preserves / extends materializations; exact
     materializations determine the view via `absReplay_ext_mem`).
  3. **SEC companion** — `kernel_derived_view_sec`: the view is a function
     of the op *set* (order-blind, redelivery-blind, acyclic on a grounded
     base). That is real content from `ExecRefine`, re-exported as the
     derived-view half of the same pattern.

## Scope

  * Structural first parents `fp` are a **parameter**, not replica state.
  * **Not claimed**: view stability under log growth (`Move.view_not_stable`).
  * **Not claimed**: CFCS for raw edge-set acyclicity under free insertion
    (`Acyclicity.acyclicity_not_iconfluent`).
  * Ungrounded bases void the grounded theorems, same as `absReplay_acyclic`.

Literature: Bailis et al. arXiv:1402.2237; Kleppmann et al. move-op CRDT;
this library's `Necessity`, `Move`, `ExecRefine`.
-/
import Uwueave.Necessity
import Uwueave.Acyclicity
import Uwueave.ExecRefine
import Uwueave.Move

namespace Uwueave.KernelCFCS

open Uwueave Uwueave.Catalog Uwueave.Necessity
open Uwueave.Exec

/-! ## §1. Decidable equality on kernel ops

`GSet.insert` (via `decide (b = a)`) needs `DecidableEq Op`. The kernel's
`Op` only derived `Inhabited`; the four fields all carry `DecidableEq` in
core, so the structure does too. -/

instance instDecidableEqOp : DecidableEq Op := fun a b =>
  if h : a.lamport = b.lamport ∧ a.replica = b.replica ∧
      a.child = b.child ∧ a.dest = b.dest then
    isTrue (by cases a; cases b; simp_all)
  else
    isFalse (fun heq => by cases heq; exact h ⟨rfl, rfl, rfl, rfl⟩)

/-! ## §2. The log carrier and the insert implementation -/

/-- The replicated state: the grow-only set of move ops ever issued. Merge is
`GSet`'s union — inherited, not re-proved. -/
abbrev MoveLog := GSet Op

example : MergeState MoveLog := inferInstance

/-- The move-kernel implementation as a `Necessity.Impl`: ops are kernel ops;
a local commit is insert-into-log. No cycle check, no peer peek — that is the
coordination-freedom content, matching the shipping design (the cycle rule
lives in `applyOp` / `absReplay`, not at commit). -/
def moveImpl : Impl MoveLog Op :=
  gsetAddImpl Op

/-- Insert is definitionally the G-Set add. -/
@[simp] theorem moveImpl_tryApply (op : Op) (s : MoveLog) :
    moveImpl.tryApply op s = some (fun b => s b || decide (b = op)) :=
  rfl

/-- Insert into the empty log yields the singleton membership predicate. -/
theorem tryApply_empty (op : Op) :
    moveImpl.tryApply op (fun _ => false) = some (fun b => decide (b = op)) := by
  rw [moveImpl_tryApply]
  apply congrArg some
  funext b
  simp

/-- The committed op is present in the post-state. -/
theorem tryApply_mem {op : Op} {s s' : MoveLog}
    (h : moveImpl.tryApply op s = some s') : s' op = true := by
  cases h
  simp

/-- Insert is monotone on membership. -/
theorem tryApply_mono_mem {op x : Op} {s s' : MoveLog}
    (h : moveImpl.tryApply op s = some s') (hx : s x = true) : s' x = true := by
  cases h
  simp [hx]

/-! ## §3. Finite materializations and the derived-view invariant -/

/-- An array **materializes a subset of** the log: every entry is a member the
log claims present. Operationally, any finite batch a replica has already
committed. -/
def Materializes (log : MoveLog) (ops : Array Op) : Prop :=
  ∀ op ∈ ops.toList, log op = true

/-- **Exact** materialization: the array's members are precisely the log. -/
def ExactMaterializes (log : MoveLog) (ops : Array Op) : Prop :=
  ∀ op, log op = true ↔ op ∈ ops.toList

theorem materializes_of_exact {log : MoveLog} {ops : Array Op}
    (h : ExactMaterializes log ops) : Materializes log ops :=
  fun op hop => (h op).mpr hop

/-- Empty log, empty array. -/
theorem materializes_empty :
    Materializes (fun _ => false) (#[] : Array Op) := by
  intro op hop
  cases hop

theorem exactMaterializes_empty :
    ExactMaterializes (fun _ => false) (#[] : Array Op) := by
  intro op
  constructor
  · intro h; exact False.elim (Bool.false_ne_true h)
  · intro hop; cases hop

/-- Singleton log materializes `#[op]`. -/
theorem materializes_singleton (op : Op) :
    Materializes (fun b => decide (b = op)) #[op] := by
  intro x hx
  have hx' : x = op := by
    simpa using hx
  simp [hx']

theorem exactMaterializes_singleton (op : Op) :
    ExactMaterializes (fun b => decide (b = op)) #[op] := by
  intro x
  constructor
  · intro hx
    have : x = op := of_decide_eq_true hx
    simp [this]
  · intro hx
    have : x = op := by simpa using hx
    simp [this]

/-- Insert into empty materializes the singleton array. -/
theorem materializes_after_insert_empty (op : Op) :
    ∃ s', moveImpl.tryApply op (fun _ => false) = some s' ∧
      Materializes s' #[op] ∧ ExactMaterializes s' #[op] := by
  refine ⟨fun b => decide (b = op), tryApply_empty op,
    materializes_singleton op, exactMaterializes_singleton op⟩

/-- Materialization is monotone in the log (growing the log keeps old arrays
legal). -/
theorem materializes_mono_log {log log' : MoveLog} {ops : Array Op}
    (hle : ∀ op, log op = true → log' op = true)
    (hm : Materializes log ops) : Materializes log' ops :=
  fun op hop => hle op (hm op hop)

/-- Merge enlarges the set of legal materializations' carrier. -/
theorem materializes_merge_left {x y : MoveLog} {ops : Array Op}
    (hm : Materializes x ops) : Materializes (x ⊔ y) ops :=
  materializes_mono_log (fun op hop => by
    show (x op || y op) = true
    simp [hop]) hm

theorem materializes_merge_right {x y : MoveLog} {ops : Array Op}
    (hm : Materializes y ops) : Materializes (x ⊔ y) ops :=
  materializes_mono_log (fun op hop => by
    show (x op || y op) = true
    simp [hop]) hm

/-- After a successful insert, every pre-insert materialization remains legal
in the post-state, and so does that array with `op` appended. -/
theorem materializes_of_tryApply {log s' : MoveLog} {op : Op} {ops : Array Op}
    (htry : moveImpl.tryApply op log = some s')
    (hm : Materializes log ops) :
    Materializes s' ops ∧ Materializes s' (ops.push op) := by
  simp only [moveImpl_tryApply] at htry
  injection htry with hs
  subst hs
  constructor
  · exact materializes_mono_log (fun y hy => by simp [hy]) hm
  · intro x hx
    have hx' : x ∈ ops.toList ∨ x = op := by
      simpa [Array.toList_push] using hx
    cases hx' with
    | inl hmem => simp [hm x hmem]
    | inr heq => simp [heq]

/-- **Derived-view acyclicity** on the log: every finite materialization, fed
to `absReplay` against structural base `fp`, has no cycle. Under
`GroundedBase` this holds of every log by `absReplay_acyclic` (membership
unused). The definition still quantifies over materializations so the
embedding matches the "view of the log" reading. -/
def DerivedAcyclic (fp : Array Int) : Invariant MoveLog :=
  fun log =>
    ∀ (ops : Array Op), Materializes log ops →
      ∀ i, ¬ Reaches fp (absReplay fp ops) i i

/-- Stronger form: every chain of every materialization **terminates** at
root. Implies `DerivedAcyclic` via `Terminates.not_reaches_self`. -/
def DerivedTerminates (fp : Array Int) : Invariant MoveLog :=
  fun log =>
    ∀ (ops : Array Op), Materializes log ops →
      ∀ i, Terminates fp (absReplay fp ops) i

theorem derivedAcyclic_of_terminates {fp : Array Int} {log : MoveLog}
    (h : DerivedTerminates fp log) : DerivedAcyclic fp log :=
  fun ops hm i => (h ops hm i).not_reaches_self

/-! ## §4. View determination from exact materialization

These theorems *use* log membership: exact materializations pin the op set,
and `absReplay_ext_mem` collapses every presentation of that set to one view. -/

/-- Exact materializations of the **same** log agree under `absReplay`. -/
theorem absReplay_eq_of_exactMaterializes (fp : Array Int) {log : MoveLog}
    {a b : Array Op}
    (ha : ExactMaterializes log a) (hb : ExactMaterializes log b) :
    absReplay fp a = absReplay fp b :=
  absReplay_ext_mem fp fun op => (ha op).symm.trans (hb op)

/-- Exact materializations of **pointwise-equal** logs agree under `absReplay`. -/
theorem absReplay_eq_of_log_eq_exact (fp : Array Int)
    {log₁ log₂ : MoveLog} {a b : Array Op}
    (ha : ExactMaterializes log₁ a) (hb : ExactMaterializes log₂ b)
    (heq : ∀ op, log₁ op = log₂ op) :
    absReplay fp a = absReplay fp b :=
  absReplay_ext_mem fp fun op => by
    constructor
    · intro hmem
      exact (hb op).mp (heq op ▸ (ha op).mpr hmem)
    · intro hmem
      exact (ha op).mp ((heq op).symm ▸ (hb op).mpr hmem)

/-- Re-export: `absReplay` is SEC as a function of the op set
(`ExecRefine.kernel_derived_view_sec`). -/
theorem move_kernel_view_sec (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) (base Δ₁ Δ₂ : Array Op) :
    absReplay fp ((base ++ Δ₁) ++ Δ₂) = absReplay fp ((base ++ Δ₂) ++ Δ₁)
    ∧ absReplay fp ((base ++ Δ₁) ++ Δ₁) = absReplay fp (base ++ Δ₁)
    ∧ ∀ i, ¬ Reaches fp (absReplay fp ((base ++ Δ₁) ++ Δ₂)) i i :=
  kernel_derived_view_sec fp r hg base Δ₁ Δ₂

/-! ## §5. Grounded base ⇒ the invariant holds of every log

Direct reindexing of `absReplay_terminates` / `absReplay_acyclic`. Materialization
hypotheses are unused — the interpreter enforces the invariant by construction. -/

/-- **Every log terminates in the derived view**, given a grounded base. -/
theorem derivedTerminates_of_grounded (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) (log : MoveLog) :
    DerivedTerminates fp log :=
  fun ops _ => absReplay_terminates fp ops r hg

/-- **Every log is derived-view-acyclic**, given a grounded base. -/
theorem derivedAcyclic_of_grounded (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) (log : MoveLog) :
    DerivedAcyclic fp log :=
  fun ops _ => absReplay_acyclic fp ops r hg

/-! ## §6. I-confluence and local safety (immediate under grounded base)

Because the invariant holds of *all* logs, it holds of every join and every
post-insert state. Same conclusion as `Necessity.true_iconfluent` for a
constantly-true predicate; spelled with the grounded appeal so the chain to
`absReplay_acyclic` stays visible. -/

theorem derivedTerminates_iconfluent (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) :
    IConfluent (DerivedTerminates fp) :=
  fun x y _ _ => derivedTerminates_of_grounded fp r hg (x ⊔ y)

theorem derivedAcyclic_iconfluent (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) :
    IConfluent (DerivedAcyclic fp) :=
  fun x y _ _ => derivedAcyclic_of_grounded fp r hg (x ⊔ y)

theorem moveImpl_locally_safe_terminates (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) :
    LocallySafe moveImpl (DerivedTerminates fp) := by
  intro op s s' htry _hs
  cases htry
  exact derivedTerminates_of_grounded fp r hg _

theorem moveImpl_locally_safe_acyclic (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) :
    LocallySafe moveImpl (DerivedAcyclic fp) := by
  intro op s s' htry _hs
  cases htry
  exact derivedAcyclic_of_grounded fp r hg _

/-! ## §7. CFCS — embedding package

`IsCFCS` follows from constant truth of the invariant under a grounded base.
This is not a new confluence obligation; it certifies that the log-as-GSet
embedding is a well-formed CFCS inhabitant for derived-view acyclicity. -/

/-- The move kernel is CFCS for derived-view termination (immediate under
`absReplay_terminates` on a grounded base). -/
theorem move_kernel_terminates_cfcs (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) :
    IsCFCS moveImpl (DerivedTerminates fp) :=
  iconfluent_implies_cfcs
    (derivedTerminates_iconfluent fp r hg)
    (moveImpl_locally_safe_terminates fp r hg)

/-- The move kernel is CFCS for derived-view acyclicity. The proof is
`iconfluent_implies_cfcs` on an invariant that holds of every log under
`GroundedBase` — packaging the embedding, not a nontrivial confluence
argument. Cycle freedom is discharged by the interpreter
(`absReplay_acyclic`), not by local abort at `tryApply`. -/
theorem move_kernel_cfcs (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) :
    IsCFCS moveImpl (DerivedAcyclic fp) :=
  iconfluent_implies_cfcs
    (derivedAcyclic_iconfluent fp r hg)
    (moveImpl_locally_safe_acyclic fp r hg)

/-- Merge safety, read off CFCS (the partition-ok direction). -/
theorem move_kernel_merge_safe (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) :
    MergeSafe moveImpl (DerivedAcyclic fp) :=
  (move_kernel_cfcs fp r hg).2

/-- Empty log is legal under a grounded base. -/
theorem move_kernel_empty_ok (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) :
    DerivedAcyclic fp (fun _ => false) :=
  derivedAcyclic_of_grounded fp r hg _

/-! ## §8. Nontriviality

CFCS is not about a do-nothing system: insert actually extends the log. -/

/-- Inserting `op` into the empty log yields a log containing `op`. -/
theorem moveImpl_nontrivial (op : Op) :
    RunsTo moveImpl (fun _ => false) (fun b => decide (b = op)) [op] := by
  simp [RunsTo, run, moveImpl, gsetAddImpl]

/-! ## §9. View instability is real (not just a non-claim)

CFCS here is about **acyclicity** of every materialization's view. It is
**not** about views being monotone in the log. The Move miniature makes that
price concrete; we re-export it so the embedding file does not only wave at
`view_not_stable` in a bullet list.
-/

/-- Log growth can shrink a derived parent pointer — `Move.view_not_stable`,
cited in the kernel embedding's namespace so the residual square-edit price
is a theorem you can find next to `move_kernel_cfcs`. -/
theorem move_view_not_stable :
    ∃ l l' : GSet Move.MoveOp, Move.LogLe l l'
      ∧ Move.miniInterp l false = some true
      ∧ Move.miniInterp l' false ≠ some true :=
  Move.view_not_stable

/-- Same fact through the kernel encoding on the 2-node base: status block
reports `o₁` skipped when both ops are present (`absReplayFull_both_statuses`
in `Move.lean`). Acyclicity CFCS and view instability **coexist**. -/
theorem acyclicity_cfcs_does_not_imply_view_stability :
    (∀ (fp : Array Int) (r : Nat → Nat),
      GroundedBase r fp → IsCFCS moveImpl (DerivedAcyclic fp)) ∧
      (∃ l l' : GSet Move.MoveOp, Move.LogLe l l' ∧
        Move.miniInterp l false = some true ∧
        Move.miniInterp l' false ≠ some true) :=
  ⟨move_kernel_cfcs, Move.view_not_stable⟩

/-! ## §10. Boundary — what the embedding is not

  1. **Raw edge acyclicity under free insertion is not CFCS** —
     `Acyclicity.acyclicity_not_iconfluent`.
  2. **View stability is false in general** — `move_view_not_stable`.
  3. **Ungrounded bases void the grounded theorems**.
-/

/-- Contrast pin: edge-set acyclicity is not I-confluent under free insertion.
Cited from `Acyclicity` — the reason the embedding uses a log + derived view
rather than a graph CRDT. -/
theorem edge_acyclicity_not_iconfluent :
    ¬ IConfluent (S := Acyclicity.EdgeGraph) Acyclicity.Acyclic :=
  Acyclicity.acyclicity_not_iconfluent

end Uwueave.KernelCFCS
