/-
# Uwueave.Necessity — Bailis Theorem 3.1's necessity direction, in this repo's terms.

## What this file is

`Confluence.lean` defines `IConfluent` and deliberately refuses a
`CoordinationFree` synonym: the modal claim ("no coordination-free convergent
safe implementation exists") had no model to quantify over. This file builds
that model and proves the necessity direction of Bailis et al., *Coordination
Avoidance in Database Systems* (VLDB 2015 / arXiv:1402.2237), Theorem 1 /
§4.2, specialized to join-semilattice replicas (this library's substrate).

The companion *sufficiency* direction — "if `IConfluent`, a CFCS exists" — is
also proved, so the equivalence for this model is complete. Both directions
connect to this repo's `IConfluent`, not a private redefinition.

## The model (Bailis §3, miniaturized)

A **replica** holds a state of type `S` with a `MergeState` join `⊔` (sync).
An **operation** is drawn from a type `Op`. A replica applies ops **locally**
via a partial function `tryApply : Op → S → Option S`:

  * `some s'` — the op commits; the new local state is `s'`;
  * `none`    — the op aborts (explicit abort, or local invariant check fails).

**Coordination-free** is definitional: `tryApply` is a pure function of the op
and the *local* state only — no lock server, no quorum, no peek at a peer.
**Convergence** is join: after a partition, replicas sync by `⊔` (CvRDT /
set-union merge in Bailis's default model). **Safety** for invariant `I` is
global `I`-validity of every committed local state and every post-sync state.

A **CFCS** (coordination-free, convergent, safe) implementation for `I` is one
whose successful local steps preserve `I` and whose join of any two states
reachable by successful local runs from a common `I`-ancestor still satisfies
`I`. That second clause is Bailis's ℐ-confluence restricted to the
implementation's reachable set — and under lattice `IConfluent` it holds for
*all* pairs, reachable or not.

## Reachability is load-bearing

A bare `¬ IConfluent I` yields *some* clashing pair via `escalation_witness`,
but causal reachability of that pair depends on the protocol (see
`CausalReach.orset_reachability_depends_on_remove_shape`: tag-scoped rem ⇒
Live; element-wide rem after full observation ⇒ unreachable). Necessity of
coordination for *locally committed join-sync* systems requires a
**reachable clash**: two successful local runs from a common ancestor whose
join is illegal. That is the hypothesis of `reachable_clash_refutes_cfcs`
and of the packaged `necessity`.

## What this model does NOT capture

  * **Network nondeterminism / reordering** beyond "two partitions then join"
    (no multi-hop gossip schedules, no loss; `Delta.lean` covers join-fold
    indistinguishability separately).
  * **Liveness / fair delivery** — convergence is the equation `⊔`, not a
    temporal "eventually" over a network.
  * **Byzantine replicas, authenticated channels, hash collisions.**
  * **Op-based causal broadcast** as a delivery constraint: reachability here
    is "successful local `tryApply` sequences from a common ancestor." A
    LatticeOnly clash that no such sequences can produce does not fire
    necessity (by design — same axis as MAP).
  * **Interactive multi-round transactions** with mid-transaction reads of
    remote state (Bailis's richer transaction model); ops here are atomic
    local transformers.
  * **Sufficiency for arbitrary ADT merges** other than the ambient `MergeState`
    join — we stay inside this library's lattices.

Literature: Bailis et al., arXiv:1402.2237, Theorem 1 and Definitions 1–6.
-/
import Uwueave.Catalog

namespace Uwueave.Necessity

open Uwueave Uwueave.Catalog

universe u v

/-! ## §1. Implementations and local runs -/

/-- A **coordination-free state-based implementation** over carrier `S` with
operation alphabet `Op`. `tryApply op s = some s'` means `op` commits locally
at `s` producing `s'`; `none` means abort. There is no channel to other
replicas inside `tryApply` — that is the entire coordination-freedom content. -/
structure Impl (S : Type u) (Op : Type v) where
  /-- Partial local commit. -/
  tryApply : Op → S → Option S

/-- A finite successful local run: fold of committed ops. `none` if any step
aborts. -/
def run {S : Type u} {Op : Type v} (impl : Impl S Op) (base : S) : List Op → Option S
  | [] => some base
  | op :: ops =>
    match impl.tryApply op base with
    | none => none
    | some s' => run impl s' ops

@[simp] theorem run_nil {S : Type u} {Op : Type v} (impl : Impl S Op) (base : S) :
    run impl base ([] : List Op) = some base := rfl

theorem run_cons_some {S : Type u} {Op : Type v} (impl : Impl S Op) (base : S)
    (op : Op) (ops : List Op) {s' : S} (h : impl.tryApply op base = some s') :
    run impl base (op :: ops) = run impl s' ops := by
  simp [run, h]

theorem run_cons_none {S : Type u} {Op : Type v} (impl : Impl S Op) (base : S)
    (op : Op) (ops : List Op) (h : impl.tryApply op base = none) :
    run impl base (op :: ops) = none := by
  simp [run, h]

/-- Successful run: the whole sequence commits, landing at `s`. -/
def RunsTo {S : Type u} {Op : Type v} (impl : Impl S Op) (base s : S)
    (ops : List Op) : Prop :=
  run impl base ops = some s

/-! ## §2. Safety, CFCS, reachable clashes -/

/-- **Local safety**: every successful commit preserves `I`. (Aborted ops never
produce a state.) This is Bailis's "transactions that would violate the
invariant abort" folded into `tryApply`. -/
def LocallySafe {S : Type u} {Op : Type v} (impl : Impl S Op)
    (I : Invariant S) : Prop :=
  ∀ op s s', impl.tryApply op s = some s' → I s → I s'

/-- Successful runs from an `I`-state land in `I`. -/
theorem RunsTo.preserves {S : Type u} {Op : Type v} {impl : Impl S Op}
    {I : Invariant S} (hloc : LocallySafe impl I) {base s : S} {ops : List Op}
    (hr : RunsTo impl base s ops) (hb : I base) : I s := by
  induction ops generalizing base with
  | nil =>
    simp [RunsTo, run] at hr
    exact hr ▸ hb
  | cons op ops ih =>
    match htry : impl.tryApply op base with
    | none =>
      simp [RunsTo, run, htry] at hr
    | some s' =>
      have hr' : RunsTo impl s' s ops := by
        simpa [RunsTo, run, htry] using hr
      exact ih hr' (hloc op base s' htry hb)

/-- **Merge safety on the reachable set** (Bailis ℐ-confluence for this
implementation's transaction alphabet): any two successful runs from a common
`I`-ancestor join to an `I`-state. -/
def MergeSafe {S : Type u} {Op : Type v} [MergeState S] (impl : Impl S Op)
    (I : Invariant S) : Prop :=
  ∀ (base x y : S) (opsx opsy : List Op),
    I base →
    RunsTo impl base x opsx →
    RunsTo impl base y opsy →
    I (x ⊔ y)

/-- **CFCS**: coordination-free (by `Impl` shape) + convergent (sync = `⊔`) +
safe (local + merge on reachable pairs). -/
def IsCFCS {S : Type u} {Op : Type v} [MergeState S] (impl : Impl S Op)
    (I : Invariant S) : Prop :=
  LocallySafe impl I ∧ MergeSafe impl I

/-- A **reachable clash** for `I` under `impl`: common `I`-ancestor, two
successful local runs to `I`-states whose join is illegal. This is the
operational witness necessity needs — strictly stronger than a bare
`¬ IConfluent` lattice pair. -/
structure ReachableClash {S : Type u} {Op : Type v} [MergeState S]
    (impl : Impl S Op) (I : Invariant S) where
  base : S
  x : S
  y : S
  opsx : List Op
  opsy : List Op
  hbase : I base
  hx_run : RunsTo impl base x opsx
  hy_run : RunsTo impl base y opsy
  hx : I x
  hy : I y
  hbad : ¬ I (x ⊔ y)

/-! ## §3. Necessity — the Bailis partition argument -/

/-- **Reachable clash refutes CFCS** (necessity core). If two partitions can
each commit a legal local history from a common ancestor and their join is
illegal, the implementation is not merge-safe, hence not CFCS.

This is Bailis's partition argument (Theorem 1, necessity of ℐ-confluence)
specialized to join sync: coordination-freedom lets both runs complete without
consulting each other; convergence joins them; safety forbids the result. -/
theorem reachable_clash_refutes_cfcs {S : Type u} {Op : Type v} [MergeState S]
    {impl : Impl S Op} {I : Invariant S}
    (c : ReachableClash impl I) : ¬ IsCFCS impl I := by
  intro ⟨_, hmerge⟩
  exact c.hbad (hmerge c.base c.x c.y c.opsx c.opsy c.hbase c.hx_run c.hy_run)

/-- A reachable clash is in particular a lattice clash — so it refutes this
repo's `IConfluent`. The hypothesis is the *reachable* refinement the MAP
axis asks for; the conclusion is the judgement the catalog already uses. -/
theorem reachable_clash_not_iconfluent {S : Type u} {Op : Type v} [MergeState S]
    {impl : Impl S Op} {I : Invariant S}
    (c : ReachableClash impl I) : ¬ IConfluent I := by
  intro h
  exact c.hbad (h c.x c.y c.hx c.hy)

/-- **Packaged necessity.** From a reachable clash under any implementation:
(1) that implementation is not CFCS; (2) `I` is not I-confluent in this repo's
sense. Coordination-free convergent safety is impossible for any implementation
that can *perform* those two local runs — and the invariant itself fails the
catalog judgement. -/
theorem necessity {S : Type u} {Op : Type v} [MergeState S]
    {impl : Impl S Op} {I : Invariant S}
    (c : ReachableClash impl I) :
    ¬ IsCFCS impl I ∧ ¬ IConfluent I :=
  ⟨reachable_clash_refutes_cfcs c, reachable_clash_not_iconfluent c⟩

/-- CFCS implies joins of reachable runs are legal (direct reading of merge
safety). -/
theorem cfcs_implies_reachable_merge_ok {S : Type u} {Op : Type v} [MergeState S]
    {impl : Impl S Op} {I : Invariant S}
    (h : IsCFCS impl I) (base x y : S) (opsx opsy : List Op)
    (hb : I base) (hx : RunsTo impl base x opsx) (hy : RunsTo impl base y opsy) :
    I (x ⊔ y) :=
  h.2 base x y opsx opsy hb hx hy

/-! ## §4. Sufficiency — lattice I-confluence lifts every CFCS obligation -/

/-- **Sufficiency (lattice form).** If `I` is I-confluent, every locally safe
implementation is merge-safe — hence CFCS. Local commits never need to ask a
peer whether a peer-legal state will join legally: the lattice closes under
join for *all* `I`-pairs, reachable or not.

This is Bailis Theorem 1's ⇐ direction inside join-semilattice systems: the
coordination-free strategy is "check `I` locally, commit, sync by `⊔`." -/
theorem iconfluent_implies_cfcs {S : Type u} {Op : Type v} [MergeState S]
    {impl : Impl S Op} {I : Invariant S}
    (hI : IConfluent I) (hloc : LocallySafe impl I) : IsCFCS impl I := by
  refine ⟨hloc, ?_⟩
  intro base x y opsx opsy hb hx hy
  exact hI x y (hx.preserves hloc hb) (hy.preserves hloc hb)

/-- Corollary: under `IConfluent`, CFCS is exactly local safety — merge safety
is free. -/
theorem cfcs_iff_locally_safe_of_iconfluent {S : Type u} {Op : Type v}
    [MergeState S] {impl : Impl S Op} {I : Invariant S}
    (hI : IConfluent I) : IsCFCS impl I ↔ LocallySafe impl I := by
  constructor
  · exact And.left
  · exact iconfluent_implies_cfcs hI

/-! ## §5. Acceptance: the model is satisfiable -/

/-- G-Set implementation: ops are elements to insert; insert always commits. -/
def gsetAddImpl (α : Type) [DecidableEq α] : Impl (GSet α) α where
  tryApply := fun a s => some (fun b => s b || decide (b = a))

/-- The trivial invariant is I-confluent. -/
theorem true_iconfluent {S : Type u} [MergeState S] :
    IConfluent (fun _ : S => True) := fun _ _ _ _ => trivial

/-- Insert is locally safe for `True`. -/
theorem gsetAddImpl_locally_safe_true (α : Type) [DecidableEq α] :
    LocallySafe (gsetAddImpl α) (fun _ => True) := by
  intro _ _ _ _ _
  exact trivial

/-- **Satisfiability**: the G-Set add implementation is CFCS for the trivial
invariant — a nontrivial system (ops actually extend state) that is
coordination-free, convergent, and safe. Definitions are not vacuously
over-strong. -/
theorem gset_true_is_cfcs (α : Type) [DecidableEq α] :
    IsCFCS (gsetAddImpl α) (fun _ : GSet α => True) :=
  iconfluent_implies_cfcs true_iconfluent (gsetAddImpl_locally_safe_true α)

/-- Membership is I-confluent and add is locally safe for it once true. -/
theorem gsetAddImpl_locally_safe_mem {α : Type} [DecidableEq α] (a : α) :
    LocallySafe (gsetAddImpl α) (fun s : GSet α => s a = true) := by
  intro op s s' htry hs
  cases htry
  show (s a || decide (a = op)) = true
  simp [hs]

/-- Stronger satisfiability: G-Set membership is CFCS under add. -/
theorem gset_mem_is_cfcs {α : Type} [DecidableEq α] (a : α) :
    IsCFCS (gsetAddImpl α) (fun s : GSet α => s a = true) :=
  iconfluent_implies_cfcs (gset_mem_iconfluent a) (gsetAddImpl_locally_safe_mem a)

/-- Nontriviality: inserting `a` into the empty set yields a set containing `a`. -/
theorem gsetAddImpl_nontrivial {α : Type} [DecidableEq α] (a : α) :
    RunsTo (gsetAddImpl α) (fun _ => false) (fun b => decide (b = a)) [a] := by
  simp [RunsTo, run, gsetAddImpl]

/-! ## §6. Acceptance: the model is refutable (reachable clash under local checks) -/

/-- Two-element universe as a G-Set on `Bool` — fully decidable ceilings. -/
abbrev BitSet := GSet Bool

/-- At most one of the two bits is set — the uniqueness ceiling on a finite
carrier (same shape as `Catalog.gset_atMostOne_not_iconfluent`). -/
def AtMostOneBit : Invariant BitSet :=
  fun s => (s true && s false) = false

/-- Insert-or-abort for at-most-one: commit only when the result still has at
most one element. Local check is Bailis's abort-on-local-violation. -/
def bitAtMostOneImpl : Impl BitSet Bool where
  tryApply := fun e s =>
    let s' : BitSet := fun b => s b || decide (b = e)
    if (s' true && s' false) = false then some s' else none

theorem bitAtMostOneImpl_locally_safe :
    LocallySafe bitAtMostOneImpl AtMostOneBit := by
  intro op s s' htry _hs
  simp only [bitAtMostOneImpl] at htry
  split at htry
  · next hok =>
    injection htry with heq
    exact heq ▸ hok
  · contradiction

private def emptyBit : BitSet := fun _ => false
private def onlyTrue : BitSet := fun b => decide (b = true)
private def onlyFalse : BitSet := fun b => decide (b = false)

theorem emptyBit_ok : AtMostOneBit emptyBit := by
  simp [AtMostOneBit, emptyBit]

theorem onlyTrue_ok : AtMostOneBit onlyTrue := by
  simp [AtMostOneBit, onlyTrue]

theorem onlyFalse_ok : AtMostOneBit onlyFalse := by
  simp [AtMostOneBit, onlyFalse]

private theorem or_false_decide (e b : Bool) :
    (false || decide (b = e)) = decide (b = e) := by
  cases b <;> cases e <;> decide

theorem tryApply_true_empty :
    bitAtMostOneImpl.tryApply true emptyBit = some onlyTrue := by
  simp only [bitAtMostOneImpl, emptyBit]
  have hs' : (fun b => false || decide (b = true)) = onlyTrue := by
    funext b; exact or_false_decide true b
  have hok : ((fun b => false || decide (b = true)) true &&
      (fun b => false || decide (b = true)) false) = false := by decide
  -- force the if-true branch
  change (if ((fun b => false || decide (b = true)) true &&
              (fun b => false || decide (b = true)) false) = false
          then some (fun b => false || decide (b = true)) else none) = some onlyTrue
  rw [if_pos hok, hs']

theorem tryApply_false_empty :
    bitAtMostOneImpl.tryApply false emptyBit = some onlyFalse := by
  simp only [bitAtMostOneImpl, emptyBit]
  have hs' : (fun b => false || decide (b = false)) = onlyFalse := by
    funext b; exact or_false_decide false b
  have hok : ((fun b => false || decide (b = false)) true &&
      (fun b => false || decide (b = false)) false) = false := by decide
  change (if ((fun b => false || decide (b = false)) true &&
              (fun b => false || decide (b = false)) false) = false
          then some (fun b => false || decide (b = false)) else none) = some onlyFalse
  rw [if_pos hok, hs']

theorem runs_onlyTrue : RunsTo bitAtMostOneImpl emptyBit onlyTrue [true] := by
  simp [RunsTo, run, tryApply_true_empty]

theorem runs_onlyFalse : RunsTo bitAtMostOneImpl emptyBit onlyFalse [false] := by
  simp [RunsTo, run, tryApply_false_empty]

theorem join_both_bad : ¬ AtMostOneBit (onlyTrue ⊔ onlyFalse) := by
  simp [AtMostOneBit, onlyTrue, onlyFalse, gset_mem_merge]

/-- The reachable clash: empty ─add true→ `{true}`, empty ─add false→ `{false}`,
join has both. Both runs are locally legal (at-most-one holds at every commit);
only the merge breaks. -/
def atMostOneBitClash : ReachableClash bitAtMostOneImpl AtMostOneBit where
  base := emptyBit
  x := onlyTrue
  y := onlyFalse
  opsx := [true]
  opsy := [false]
  hbase := emptyBit_ok
  hx_run := runs_onlyTrue
  hy_run := runs_onlyFalse
  hx := onlyTrue_ok
  hy := onlyFalse_ok
  hbad := join_both_bad

/-- **Refutability**: the natural at-most-one implementation (insert-or-abort)
admits a reachable clash, so it is not CFCS — even though every *local* commit
preserved the invariant. Safety fails at merge, which is exactly the partition
scenario. Definitions are not vacuously under-strong. -/
theorem atMostOneBit_impl_not_cfcs : ¬ IsCFCS bitAtMostOneImpl AtMostOneBit :=
  reachable_clash_refutes_cfcs atMostOneBitClash

/-- Lattice `IConfluent` fails too — the reachable witness is a catalog-shaped
ceiling clash. -/
theorem atMostOneBit_not_iconfluent : ¬ IConfluent AtMostOneBit :=
  reachable_clash_not_iconfluent atMostOneBitClash

/-- Full packaged necessity on the finite-carrier ceiling. -/
theorem atMostOneBit_necessity :
    ¬ IsCFCS bitAtMostOneImpl AtMostOneBit ∧ ¬ IConfluent AtMostOneBit :=
  necessity atMostOneBitClash

/-- Directly: this impl *is* locally safe, so the CFCS failure is purely at the
merge clause — the interesting half of the partition argument. -/
theorem atMostOneBit_locally_safe_but_not_merge_safe :
    LocallySafe bitAtMostOneImpl AtMostOneBit ∧
      ¬ MergeSafe bitAtMostOneImpl AtMostOneBit := by
  refine ⟨bitAtMostOneImpl_locally_safe, ?_⟩
  intro hmerge
  exact join_both_bad
    (hmerge emptyBit onlyTrue onlyFalse [true] [false]
      emptyBit_ok runs_onlyTrue runs_onlyFalse)

/-! ## §7. Coordination is not vacuous: serial repair vs CF clash

`Impl` admits only coordination-free `tryApply` (local state only). A system
that *serializes* ops across replicas is intentionally outside that type —
its step function needs a shared schedule. This section makes that boundary
**computational**, not just a comment: the same insert-or-abort rule, run
**serially** on one site, preserves `AtMostOneBit` for every finite word,
while the CF two-partition run of those same two inserts is the clash above.
-/

/-- One serial step: apply if local check passes, else keep state (coordinator
refuses). Defined by the same predicate as `bitAtMostOneImpl`, inlined so
preservation is by construction of the `if`. -/
def serialStep (e : Bool) (s : BitSet) : BitSet :=
  let s' : BitSet := fun b => s b || decide (b = e)
  if (s' true && s' false) = false then s' else s

/-- **Serial (coordinated) execution** of a word: one site, one total order,
no peer merge mid-word. -/
def serialRun (ops : List Bool) : BitSet :=
  ops.foldl (fun s e => serialStep e s) emptyBit

@[simp] theorem serialRun_nil : serialRun [] = emptyBit := rfl

theorem serialStep_preserves (e : Bool) (s : BitSet) (hs : AtMostOneBit s) :
    AtMostOneBit (serialStep e s) := by
  simp only [serialStep, AtMostOneBit]
  split
  · next hok => exact hok
  · exact hs

theorem serialRun_preserves (ops : List Bool) : AtMostOneBit (serialRun ops) := by
  have go : ∀ (acc : BitSet) (l : List Bool), AtMostOneBit acc →
      AtMostOneBit (l.foldl (fun s e => serialStep e s) acc) := by
    intro acc l hacc
    induction l generalizing acc with
    | nil => exact hacc
    | cons x xs ih =>
      exact ih (serialStep x acc) (serialStep_preserves x acc hacc)
  exact go emptyBit ops emptyBit_ok

/-- Serial execution of either order of the two inserts stays legal. -/
theorem serial_both_orders_ok :
    AtMostOneBit (serialRun [true, false]) ∧ AtMostOneBit (serialRun [false, true]) :=
  ⟨serialRun_preserves _, serialRun_preserves _⟩

/-- **The residual job-spec criterion, discharged:** the same op alphabet and
local rule admit a **coordinating** strategy (serial fold) that always
preserves the invariant, while the **coordination-free** `Impl` strategy is
refuted by `atMostOneBit_impl_not_cfcs`. Coordination is not a vacuous
category — it is what you buy to escape the partition clash. -/
theorem coordination_repairs_what_cf_breaks :
    (∀ ops : List Bool, AtMostOneBit (serialRun ops)) ∧
      ¬ IsCFCS bitAtMostOneImpl AtMostOneBit :=
  ⟨serialRun_preserves, atMostOneBit_impl_not_cfcs⟩

/-- Every commit decision of a pure `Impl` is a function of `(op, local state)`
alone. -/
theorem tryApply_exhaustive {S : Type u} {Op : Type v} (impl : Impl S Op)
    (op : Op) (s : S) :
    (∃ s', impl.tryApply op s = some s') ∨ impl.tryApply op s = none := by
  match impl.tryApply op s with
  | none => exact Or.inr rfl
  | some s' => exact Or.inl ⟨s', rfl⟩

end Uwueave.Necessity
