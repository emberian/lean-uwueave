/-
# Uwueave.Recoverable — the positive converse: which resurrection clashes are actually repaired?

`Ancestral.lean` proved one half of a dichotomy and said so in its own §8:

> What is **not** proved here is the general converse: that every resurrection
> clash admits a repairing merge. It does not follow, and this file does not
> claim it. A merge sees states, not operations, and a state need not determine
> the operation that produced it, so the legal serialization may not be a
> function of the triple at all. […] closing it in general needs a delta-recovery
> hypothesis (states determine their deltas) and is left open.

The external reviewer (codex) who set that boundary named the missing work in one
line — *"the positive converse is where the real algebra begins"* — and listed the
ingredients: **(1)** delta recoverability, `(l, x)` determines the branch effect at
least up to contextual equivalence; **(2)** existence of a legal serialization;
**(3)** a symmetric deterministic chooser, so both replicas select the same one;
**(4)** fast-forward compatibility; **(5)** history coherence. This file builds
(1)–(4) and closes the converse at the resolution `Ancestral.Serializing` is
stated in. (5) is a sibling file's (`Uwueave/Histories.lean`, deliberately **not**
imported here — see the division of labour below).

## The answer, in one line

**Recoverability + a legal serialization + a symmetric tie-break is exactly
enough, and "exactly" is an iff:**

    faithful_stepConfluent_iff_legalSerialization :
      (∃ M, Serializing M g ∧ StepConfluent M g I) ↔ LegalSerialization g I

for every delta-recoverable `g` carrying a tie-break. (Plus decidable equality
on states and a decidable invariant — the construction uses them to stay a
computable function; `Classical.propDecidable` supplies both if you do not care
whether the merge runs.) Left-to-right is
`Ancestral`'s negative half re-derived (`serialization_clash_defeats_every_merge`
in iff clothing); right-to-left is the construction — a merge is **built**, not
assumed, from the recovery map and the chooser, and it is proved commutative,
fast-forwarding, effect-faithful and invariant-preserving. So the dichotomy of
`Ancestral.clash_dichotomy` is no longer two one-way results with a gap between
them: at one-operation resolution the two branches are the two sides of one
equivalence, and `LegalSerialization` is the whole content.

## What each ingredient does, and what breaks without it

  * **§1 Recoverability.** `DeltaRecoverableOn g` says two admitted operations
    agreeing at one state agree everywhere; `DeltaRecoveryOn g` is the
    *instrument* — a map `recover : S → S → (S → S)` with
    `recover l (eff a l) = eff a` for admitted `a` — and the two are equivalent
    (`deltaRecoveryOn_iff_deltaRecoverableOn`, the ⇐ direction by
    `Classical.choice`). The guard-free `DeltaRecoverable` and `DeltaRecovery`
    remain as strictly stronger variants. The condition is neither vacuous nor
    universal: the lock and bounded counter have **computable, choice-free**
    recoveries, and §1.4's always-admitted `Ghost` has none. That non-example
    carries a theorem rather than a shrug — `ambiguous_delta_defeats_faithfulness`
    shows an admitted ambiguous delta makes `Serializing` **unsatisfiable**:
    `ghost_no_faithful_merge` refutes it for *every* `AncestralMerge Nat` at
    once. Recoverability is not a convenience hypothesis, it is the precondition
    for effect-faithfulness to be a consistent demand on a function of states.
    `CostedDeltaRecoveryOn` adds an explicit step alphabet, recovery program,
    and work field tied to that program's length and execution. §4 transports
    the certificate into the constructed merge: fast-forward costs zero, the
    recovery branch is bounded by the larger of the two candidate recovery
    costs, and every uniform recovery bound becomes a merge bound.
  * **§2 A legal serialization.** `LegalSerialization` is the ∀-quantified
    resurrection branch of `clash_dichotomy`, and `legalSerialization_or_escalation`
    connects them by theorem: for any effect-faithful merge, either it holds or
    that merge escalates.
  * **§3 A symmetric chooser.** `AncestralMerge` demands `comm`, and
    `comm_forces_symmetric_chooser` proves the demand bites: at any triple whose
    two candidate serializations differ, a commutative merge's chooser *must*
    agree under argument swap. So "both replicas pick the same order" is not an
    engineering nicety bolted on — it is forced by the merge law. `TieBreak`
    (a total antisymmetric preference, e.g. `TieBreak.ofKey` from any injective
    key) supplies one, and `tieChooser` makes it **discerning**: it never picks
    an illegal order when a legal one exists. Note the shape of the difficulty —
    "prefer the left order when it is legal" is *not* symmetric when both orders
    are legal, which is exactly why a tie-break is an ingredient at all.
  * **§4 Fast-forward** is built into the merge (`x = l ⇒ y`), which is what
    makes `AncestralMerge.fastforward` hold on the nose and what discharges the
    ancestor cases of §5.

## The lock is an instance, and that is the test of content

`Ancestral.lock_ancestral_confluent` was hand-built. §6 re-proves **the same
statement about the same merge** — `lock_ancestral_confluent_is_an_instance :
AncestralConfluent lockAM lockImpl AtMostOne` — from the general construction
plus four checkable facts (`lockRecovery`, `lockTie`, `lock_legalSerialization`,
`lock_stepGenerated`). The bridge is `lockConstructed_eq_lockMerge`: on legal
replicas the constructed merge **is** `lockMerge`, computed. So `lockPriority`'s
"Alice over Bob over nobody" is not an invention of that file; it is the
tie-break `lockKey` fed through the general chooser, and the general construction
rediscovers it.

## The boundary is the same theorem, not a separate story (§7)

The bounded counter satisfies *every* hypothesis of the construction —
`spendRecovery` is a recovery, `natTie` a tie-break, both instances decidable —
so the iff applies to it in full, and `budget_not_legalSerialization` kills the
right-hand side. `budget_defeats_every_faithful_merge_again` then re-derives
`Ancestral`'s impossibility as a corollary of the equivalence. **Accumulation
fails at exactly one hypothesis, and it is `LegalSerialization`.** That is the
iff-shaped form of the dichotomy the two files together now have.

## Honest boundary — what is claimed and what is not

  * ⟨UNDONE, narrowed to endpoint-only reconstruction/generic merge synthesis⟩
    **This file's converse is proved at one-operation resolution**
    (`StepConfluent`), which is the resolution `Ancestral.Serializing` and
    `serialization_clash_defeats_every_merge` are stated in. §5 lifts it with
    `StepGenerated`, "every reachable branch is the ancestor or one admitted
    step from it". The lock satisfies that local bridge; the counter does not.
    The sibling `Uwueave.CompositeDelta` now closes the explicit-patch route for
    arbitrary finite runs: `Patch.admitted_of_runsTo` exposes successful runs,
    `LegalUnderComposition` is proved equivalent to full
    `AncestralConfluent`, and `Algebra` carries residual admission, commutation,
    merge execution, and legality. Its `stepConfluent_counter_fails_composite_law`
    preserves this file's length-two counter as a failure of that named law,
    while `cheapLockAlgebra` supplies a one-step positive instance. What remains
    genuinely open is a generic **state-only** constructor that reconstructs or
    residualizes an arbitrary run delta from endpoints and synthesizes the merge
    without a carried patch. Cyclic operations show why no such reconstruction
    follows from `DeltaRecoveryOn`; no theorem here or in `CompositeDelta`
    claims otherwise.
  * **Recoverability is guard-relative.** `DeltaRecoverableOn` is the exact
    hypothesis used by the construction: only deltas an implementation can
    actually commit need be recoverable. `DeltaRecoveryOn` is its equivalent
    proof instrument, and the original guard-free forms remain available as
    stronger sufficient conditions. This scope matches `Serializing`, which
    constrains exactly two operations admitted concurrently at their ancestor.
  * ⟨TERMINAL⟩ **"Up to contextual equivalence" is realised, and it is realised
    where it belongs.** §1.3 defines `DeltaRecoverableUpTo` and `SerializingUpTo`
    over `MinimalSummary.CtxEquiv` (with `obs` presenting the invariant as a
    `Bool`-valued query, since `CtxEquiv` ranges over `Type`-valued ones), and
    `legalSerialization_of_stepConfluent_upTo` proves the negative half survives
    the weakening: a merge landing merely *contextually equivalent* to a
    serialization is still enough to force `LegalSerialization`. The justification
    is `ctxEquiv_survives_history` — equivalence is preserved by every future
    gossip history, so nothing downstream can observe the difference. What is
    **not** done: the *construction* is stated with exact recovery, because
    `Serializing` as `Ancestral` defines it is an equation on states, and an
    up-to-equivalence recovery yields the invariant verdict but not that equation.
    That is a theorem of the model, not undone work: coarsening the recovery
    coarsens exactly the conclusion that mentions states.
  * ⟨TERMINAL⟩ **Nothing here says a repairing merge is unique, canonical, or
    good.** The chooser is a free parameter; different tie-breaks give different
    legal merges. `constant_merge_collapses` (Ancestral §1) already excludes the
    degenerate one, and that is all the pinning down there is.
  * ⟨TERMINAL⟩ **Recovery work is now explicit, not inferred from correctness.**
    `CostedDeltaRecoveryOn` certifies `recover` by a finite step program whose
    length is its declared `work`; `constructedMergeWork_le_max` and
    `constructedMergeWork_le_of_recovery_bound` transport recovery bounds to the
    constructed merge. `cheapLockRecovery` costs one step, while
    `lockRecovery_arbitrarily_expensive` pads the *same* semantic recovery with
    arbitrarily many certified identity steps. These are abstract step counts,
    not wall-clock time, allocation, or a multi-operation history cost. The
    one-operation boundary above is unchanged.

Literature: as `Ancestral.lean` (Kaki et al. OOPSLA 2019; Sal 2026 §2; Bailis et
al. VLDB 2015). The chooser is Sal's `rc` conflict-resolution policy with the two
laws it must satisfy for a three-way merge to be well defined at all, proved
rather than assumed; `TieBreak` is the deterministic-arbitration folklore
("compare replica ids") stated as the algebra it is.
-/
import Uwueave.Ancestral
import Uwueave.MinimalSummary

namespace Uwueave.Recoverable

open Uwueave Uwueave.Catalog Uwueave.Necessity Uwueave.Ancestral

universe u v w

variable {S : Type u} {Op : Type v}

/-! ## §1. Delta recoverability — the merge can tell what happened

A three-way merge is a function of `(l, x, y)`. To be effect-faithful it must
apply the operations that produced `x` and `y`; so it must be able to read those
operations off the states. That is the hypothesis `Ancestral` §8 named and did
not have. -/

/-- **Delta recoverability.** Two operations that agree at one state agree at
every state — so from the pair `(l, x)` the branch's *effect* is determined, even
though the operation itself may not be. This is the property a merge needs: it
never sees an `Op`, only the delta `(l, x)`, and it must be able to replay that
delta somewhere else. -/
def DeltaRecoverable (g : Guarded S Op) : Prop :=
  ∀ (l : S) (a b : Op), g.eff a l = g.eff b l → g.eff a = g.eff b

/-- The guard-relativized form: only deltas an implementation can actually
*commit* need be recoverable. This is the exact hypothesis of the construction,
via the equivalent instrument `DeltaRecoveryOn`. -/
def DeltaRecoverableOn (g : Guarded S Op) : Prop :=
  ∀ (l : S) (a b : Op), g.guard a l = true → g.guard b l = true →
    g.eff a l = g.eff b l → g.eff a = g.eff b

/-- Guard-free recoverability implies the guarded form. -/
theorem deltaRecoverable_on {g : Guarded S Op} (h : DeltaRecoverable g) :
    DeltaRecoverableOn g :=
  fun l a b _ _ hab => h l a b hab

/-- **A guard-relative recovery map.** `recover l x` is the effect replayed for
the branch from `l` to `x`. Its specification applies exactly when `x` was
produced by an operation admitted at `l`; no law is imposed on deltas that the
implementation aborts and therefore cannot commit. -/
structure DeltaRecoveryOn (g : Guarded S Op) where
  /-- The recovered effect of the delta from the ancestor to a branch state. -/
  recover : S → S → (S → S)
  /-- An admitted operation's delta recovers that operation's effect. -/
  spec : ∀ (l : S) (a : Op), g.guard a l = true → recover l (g.eff a l) = g.eff a

/-- A guarded recovery determines the effects of admitted operations that
produce the same delta. -/
theorem DeltaRecoveryOn.recoverableOn {g : Guarded S Op} (D : DeltaRecoveryOn g) :
    DeltaRecoverableOn g := by
  intro l a b hga hgb hab
  rw [← D.spec l a hga, ← D.spec l b hgb, hab]

open Classical in
/-- Guard-relative recoverability builds its recovery instrument by selecting
only among admitted operations that produced the observed delta. Values with no
such producer are irrelevant to the specification and use the identity fallback. -/
noncomputable def recoveryOfRecoverableOn (g : Guarded S Op)
    (h : DeltaRecoverableOn g) : DeltaRecoveryOn g where
  recover l x :=
    if hx : ∃ o : Op, g.guard o l = true ∧ g.eff o l = x then
      g.eff hx.choose
    else
      fun _ => x
  spec := by
    intro l a hga
    have hx : ∃ o : Op, g.guard o l = true ∧ g.eff o l = g.eff a l :=
      ⟨a, hga, rfl⟩
    rw [dif_pos hx]
    exact h l hx.choose a hx.choose_spec.1 hga hx.choose_spec.2

/-- **Guard-relative recoverability and its instrument are equivalent.** -/
theorem deltaRecoveryOn_iff_deltaRecoverableOn (g : Guarded S Op) :
    Nonempty (DeltaRecoveryOn g) ↔ DeltaRecoverableOn g :=
  ⟨fun ⟨D⟩ => D.recoverableOn, fun h => ⟨recoveryOfRecoverableOn g h⟩⟩

/-! ### §1.1 Costed guarded recovery — a program, not an ungrounded number -/

/-- Execute a finite recovery program. Each instruction transforms the current
state; the list order is execution order. -/
def runRecoverySteps {Step : Type w} (applyStep : Step → S → S) :
    S → List Step → S
  | s, [] => s
  | s, step :: steps => runRecoverySteps applyStep (applyStep step s) steps

/-- Recovery execution respects program concatenation. -/
theorem runRecoverySteps_append {Step : Type w} (applyStep : Step → S → S) :
    ∀ (before : S) (p q : List Step),
      runRecoverySteps applyStep before (p ++ q) =
        runRecoverySteps applyStep (runRecoverySteps applyStep before p) q := by
  intro before p
  induction p generalizing before with
  | nil => intro q; rfl
  | cons step steps ih =>
    intro q
    exact ih (applyStep step before) q

/-- **A proof-carrying work interface for guarded recovery.** It extends the
existing correctness instrument without changing it. `program l delta` is the
finite instruction sequence implementing the recovered effect for that branch;
`program_correct` connects its execution to `recover`, and
`work_eq_program_length` prevents the numeric cost from drifting away from the
certificate.

The program is attached to one recovered delta and implements the recovered
effect on every input state. It does not claim to represent a branch history. -/
structure CostedDeltaRecoveryOn (g : Guarded S Op) (Step : Type w)
    extends DeltaRecoveryOn g where
  /-- Semantics of one abstract recovery instruction. -/
  applyStep : Step → S → S
  /-- Certified program for the delta from `l` to the branch state. -/
  program : S → S → List Step
  /-- Declared abstract work for recovering that delta. -/
  work : S → S → Nat
  /-- Work is exactly program length, not a decorative annotation. -/
  work_eq_program_length : ∀ l x, work l x = (program l x).length
  /-- Executing the program computes the inherited recovery function. -/
  program_correct : ∀ l x s,
    runRecoverySteps applyStep s (program l x) = recover l x s

/-- Forgetting costs and programs recovers the original correctness interface
definitionally. -/
def CostedDeltaRecoveryOn.erase {g : Guarded S Op} {Step : Type w}
    (D : CostedDeltaRecoveryOn g Step) : DeltaRecoveryOn g :=
  D.toDeltaRecoveryOn

/-- **The recovery map — recoverability as an instrument rather than a
property.** `recover l x` is the effect the merge replays for the branch that
went from `l` to `x`, and `spec` is its only law: on a delta an operation really
produced, it returns that operation's effect. Everywhere else it may do as it
likes; the construction never looks. -/
structure DeltaRecovery (g : Guarded S Op) where
  /-- The recovered effect of the delta from the ancestor to a branch state. -/
  recover : S → S → (S → S)
  /-- On a delta an operation produced, the recovery is that operation's effect. -/
  spec : ∀ (l : S) (a : Op), recover l (g.eff a l) = g.eff a

/-- A guard-free recovery is, in particular, a guard-relative recovery. -/
def DeltaRecovery.toOn {g : Guarded S Op} (D : DeltaRecovery g) : DeltaRecoveryOn g where
  recover := D.recover
  spec := fun l a _ => D.spec l a

/-- A recovery map exists only if the deltas determine the effects: if `a` and
`b` agree at `l` the map must return the same function for both, and `spec`
identifies that function with each of their effects. -/
theorem DeltaRecovery.recoverable {g : Guarded S Op} (D : DeltaRecovery g) :
    DeltaRecoverable g := by
  intro l a b hab
  rw [← D.spec l a, ← D.spec l b, hab]

open Classical in
/-- …and conversely, recoverability builds one: read off any operation producing
the delta, and take its effect. `Classical.choice`, so this is a witness that a
recovery *exists*, not an algorithm — the lock and the counter both exhibit
computable ones (`lockRecovery`, `spendRecovery`), which is the better statement
wherever it is available. -/
noncomputable def recoveryOfRecoverable (g : Guarded S Op) (h : DeltaRecoverable g) :
    DeltaRecovery g where
  recover l x := if hx : ∃ o : Op, g.eff o l = x then g.eff hx.choose else fun _ => x
  spec := by
    intro l a
    have hx : ∃ o : Op, g.eff o l = g.eff a l := ⟨a, rfl⟩
    rw [dif_pos hx]
    exact h l hx.choose a hx.choose_spec

/-- **The hypothesis and the instrument are the same thing.** -/
theorem deltaRecovery_iff_deltaRecoverable (g : Guarded S Op) :
    Nonempty (DeltaRecovery g) ↔ DeltaRecoverable g :=
  ⟨fun ⟨D⟩ => D.recoverable, fun h => ⟨recoveryOfRecoverable g h⟩⟩

/-! ### §1.2 Two recoverable structures — the hypothesis is not vacuous. -/

/-- Every lock operation overwrites the holder state, so its effect does not
depend on where it is applied. -/
theorem lockEff_const (o : LockOp) (s t : Lock) : lockEff o s = lockEff o t := by
  cases o <;> rfl

/-- **The lock's recovery, computable and choice-free**: the branch state *is*
the effect, because every lock operation is a constant function. -/
def lockRecovery : DeltaRecovery lockOps where
  recover := fun _ q => fun _ => q
  spec := by
    intro l a
    funext s
    exact lockEff_const a l s

/-- **The bounded counter's recovery, computable and choice-free**: every spend
has the same effect, so the delta determines it trivially. Recoverability is
*not* what the counter lacks — §7. -/
def spendRecovery (B : Nat) : DeltaRecovery (spendOps B) where
  recover := fun _ _ => fun s => s + 1
  spec := fun _ _ => rfl

/-! #### A cheap recovery and the same recovery at arbitrary certified cost -/

/-- Abstract instructions for the lock recovery. `idle` is explicit padding;
`write q` performs the recovered constant effect. -/
inductive LockRecoveryStep where
  /-- One unit of work that preserves the current state. -/
  | idle
  /-- Replace the current lock state with the recovered branch state. -/
  | write (value : Lock)
  deriving DecidableEq, Repr

/-- Semantics of the lock recovery instructions. -/
def applyLockRecoveryStep : LockRecoveryStep → Lock → Lock
  | .idle, s => s
  | .write q, _ => q

/-- A lock recovery program with `padding` certified identity instructions
before its one real write. -/
def paddedLockProgram : Nat → Lock → List LockRecoveryStep
  | 0, q => [.write q]
  | n + 1, q => .idle :: paddedLockProgram n q

/-- Padding is counted: the program contains exactly `padding + 1` steps. -/
theorem paddedLockProgram_length (padding : Nat) (q : Lock) :
    (paddedLockProgram padding q).length = padding + 1 := by
  induction padding with
  | zero => rfl
  | succ n ih => simp [paddedLockProgram, ih]

/-- Padding is semantically inert and the final instruction computes the lock's
recovery function. -/
theorem paddedLockProgram_correct (padding : Nat) (q s : Lock) :
    runRecoverySteps applyLockRecoveryStep s (paddedLockProgram padding q) = q := by
  induction padding generalizing s with
  | zero => rfl
  | succ n ih => exact ih s

/-- The lock's semantic recovery with an explicit, certified amount of padding.
All values of `padding` erase to the same `lockRecovery.toOn`; only the program
and its honest work certificate differ. -/
def paddedLockRecovery (padding : Nat) :
    CostedDeltaRecoveryOn lockOps LockRecoveryStep where
  toDeltaRecoveryOn := lockRecovery.toOn
  applyStep := applyLockRecoveryStep
  program := fun _ q => paddedLockProgram padding q
  work := fun _ _ => padding + 1
  work_eq_program_length := fun _ q => (paddedLockProgram_length padding q).symm
  program_correct := fun _ q s => paddedLockProgram_correct padding q s

/-- A choice-free one-step recovery certificate for the lock. -/
def cheapLockRecovery : CostedDeltaRecoveryOn lockOps LockRecoveryStep :=
  paddedLockRecovery 0

/-- The cheap certificate really costs one abstract instruction. -/
theorem cheapLockRecovery_work (l x : Lock) : cheapLockRecovery.work l x = 1 := rfl

/-- Every padded certificate has exactly the advertised cost. -/
theorem paddedLockRecovery_work (padding : Nat) (l x : Lock) :
    (paddedLockRecovery padding).work l x = padding + 1 := rfl

/-- **The cost field is independent evidence, not a corollary of correctness.**
For every requested lower bound there is a certificate erasing to the exact same
semantic lock recovery whose explicit program costs at least that much. The
extra work consists of certified identity steps, so correctness is unchanged. -/
theorem lockRecovery_arbitrarily_expensive (n : Nat) :
    ∃ D : CostedDeltaRecoveryOn lockOps LockRecoveryStep,
      D.erase = lockRecovery.toOn ∧
        n ≤ D.work ⟨false, false⟩ ⟨true, false⟩ := by
  exact ⟨paddedLockRecovery n, rfl, by simp [paddedLockRecovery_work]⟩

/-- Both exhibited structures are delta-recoverable, so the hypothesis of every
theorem below is inhabited. -/
theorem lock_deltaRecoverable : DeltaRecoverable lockOps := lockRecovery.recoverable

theorem spend_deltaRecoverable (B : Nat) : DeltaRecoverable (spendOps B) :=
  (spendRecovery B).recoverable

/-! ### §1.3 "Up to contextual equivalence" — where the weakening is real.

Codex's ingredient (1) asks only that the effect be determined *up to contextual
equivalence*. `MinimalSummary.CtxEquiv` is that relation, and it is reused here
rather than re-invented. It ranges over `Type`-valued queries, so the invariant
is presented as the `Bool`-valued query `obs`. -/

/-- The invariant as a query, so `CtxEquiv` applies to it. -/
def obs (I : Invariant S) [DecidablePred I] : S → Bool := fun s => decide (I s)

/-- Equal decisions are equivalent propositions. -/
theorem iff_of_decide_eq {p q : Prop} [Decidable p] [Decidable q]
    (h : decide p = decide q) : p ↔ q := by
  constructor
  · intro hp
    exact of_decide_eq_true (by rw [← h]; exact decide_eq_true hp)
  · intro hq
    exact of_decide_eq_true (by rw [h]; exact decide_eq_true hq)

/-- Contextually equivalent states satisfy the invariant together. -/
theorem legal_of_ctxEquiv [MergeState S] {I : Invariant S} [DecidablePred I] {u v : S}
    (h : CtxEquiv (obs I) u v) (hu : I u) : I v :=
  (iff_of_decide_eq h.1).mp hu

/-- **Why "up to contextual equivalence" is the right coarseness**: the two
states are indistinguishable to the invariant not merely now, but after *every*
future gossip history — `MinimalSummary.ctxEquiv_history` applied to the
invariant's query. A merge that lands on an equivalent state has given up
nothing any later observer could recover. -/
theorem ctxEquiv_survives_history [MergeState S] {I : Invariant S} [DecidablePred I]
    {u v : S} (h : CtxEquiv (obs I) u v) (hist : List S) :
    I (Delta.joinAll u hist) ↔ I (Delta.joinAll v hist) :=
  iff_of_decide_eq (ctxEquiv_history h hist)

/-- **Recoverability, weakened to codex's exact phrasing**: the delta determines
the effect *up to contextual equivalence for the invariant*. -/
def DeltaRecoverableUpTo [MergeState S] (g : Guarded S Op) (I : Invariant S)
    [DecidablePred I] : Prop :=
  ∀ (l : S) (a b : Op), g.eff a l = g.eff b l →
    ∀ s : S, CtxEquiv (obs I) (g.eff a s) (g.eff b s)

/-- Exact recoverability is the strict version of it. -/
theorem deltaRecoverable_upTo [MergeState S] {g : Guarded S Op} {I : Invariant S}
    [DecidablePred I] (h : DeltaRecoverable g) : DeltaRecoverableUpTo g I := by
  intro l a b hab s
  rw [h l a b hab]
  exact ctxEquiv_refl _ _

/-- **What the weakening buys, exactly.** Under up-to recoverability the merge's
*verdict* is well defined even where its *state* is not: two operations the delta
cannot distinguish give serializations that are legal together or illegal
together, at every continuation. That is the precise sense in which contextual
equivalence is enough — and the precise thing `Ghost` (§1.4) violates. -/
theorem legality_wellDefined_of_upTo [MergeState S] {g : Guarded S Op}
    {I : Invariant S} [DecidablePred I] (h : DeltaRecoverableUpTo g I)
    (l : S) (a b c : Op) (hab : g.eff a l = g.eff b l) :
    I (g.eff a (g.eff c l)) ↔ I (g.eff b (g.eff c l)) :=
  iff_of_decide_eq (h l a b hab (g.eff c l)).1

/-- **Effect-faithfulness weakened the same way**: for two operations admitted
at their common ancestor, the merge lands on a state contextually equivalent to
one of the two serializations, rather than on it. `Ancestral.Serializing` is the
special case where the equivalence is equality. -/
def SerializingUpTo [MergeState S] (M : AncestralMerge S) (g : Guarded S Op)
    (I : Invariant S) [DecidablePred I] : Prop :=
  ∀ (l : S) (a b : Op),
    g.guard a l = true → g.guard b l = true →
    CtxEquiv (obs I) (M.merge3 l (g.eff a l) (g.eff b l)) (g.eff b (g.eff a l)) ∨
    CtxEquiv (obs I) (M.merge3 l (g.eff a l) (g.eff b l)) (g.eff a (g.eff b l))

/-- An effect-faithful merge is faithful up to equivalence. -/
theorem serializing_upTo [MergeState S] {M : AncestralMerge S} {g : Guarded S Op}
    {I : Invariant S} [DecidablePred I] (h : Serializing M g) : SerializingUpTo M g I := by
  intro l a b hga hgb
  rcases h l a b hga hgb with h' | h'
  · exact Or.inl (by rw [h']; exact ctxEquiv_refl _ _)
  · exact Or.inr (by rw [h']; exact ctxEquiv_refl _ _)

/-! ### §1.4 A NON-recoverable structure — the hypothesis is not universal,
and its failure is not a technicality.

Four total, individually harmless arithmetic operations. Two of them collide at
`0`, and so do the other two; the collisions are invisible in the state and the
serializations disagree. No merge — no *possible* merge — is effect-faithful for
them. -/

/-- **An admitted ambiguous delta makes effect-faithfulness unsatisfiable.** If
all four operations are admitted at `l`, `a` and `c` produce the same branch
state there, and so do `b` and `d`, then the merge of that one producible triple
has to be a serialization of `a,b` *and* a serialization of `c,d`. Four
disequations say those two two-element sets are disjoint, and the merge has
nowhere to land. The quantifier is over *every* `AncestralMerge`, so this is not
about a bad choice of merge. -/
theorem ambiguous_delta_defeats_faithfulness (M : AncestralMerge S)
    (g : Guarded S Op) (l : S) (a b c d : Op)
    (hga : g.guard a l = true) (hgb : g.guard b l = true)
    (hgc : g.guard c l = true) (hgd : g.guard d l = true)
    (hac : g.eff a l = g.eff c l) (hbd : g.eff b l = g.eff d l)
    (h₁ : g.eff b (g.eff a l) ≠ g.eff d (g.eff c l))
    (h₂ : g.eff b (g.eff a l) ≠ g.eff c (g.eff d l))
    (h₃ : g.eff a (g.eff b l) ≠ g.eff d (g.eff c l))
    (h₄ : g.eff a (g.eff b l) ≠ g.eff c (g.eff d l))
    (hser : Serializing M g) : False := by
  have hcong : M.merge3 l (g.eff a l) (g.eff b l) = M.merge3 l (g.eff c l) (g.eff d l) := by
    rw [hac, hbd]
  rcases hser l a b hga hgb with hp | hp
  · rcases hser l c d hgc hgd with hq | hq
    · exact h₁ (hp.symm.trans (hcong.trans hq))
    · exact h₂ (hp.symm.trans (hcong.trans hq))
  · rcases hser l c d hgc hgd with hq | hq
    · exact h₃ (hp.symm.trans (hcong.trans hq))
    · exact h₄ (hp.symm.trans (hcong.trans hq))

/-- Four operations on `Nat`, pairwise colliding at `0`. -/
inductive Ghost where
  /-- `s ↦ s + 1`. -/
  | inc
  /-- `s ↦ 2s + 1` — agrees with `inc` at `0` and nowhere else. -/
  | dbl
  /-- `s ↦ s + 2`. -/
  | add2
  /-- `s ↦ 3s + 2` — agrees with `add2` at `0` and nowhere else. -/
  | tri
  deriving DecidableEq, Repr

/-- The effects: `inc`/`dbl` both send `0` to `1`, `add2`/`tri` both send `0` to
`2`, and they part company immediately afterwards. -/
def ghostEff : Ghost → Nat → Nat
  | .inc, s => s + 1
  | .dbl, s => 2 * s + 1
  | .add2, s => s + 2
  | .tri, s => 3 * s + 2

/-- The ambiguous implementation: every operation is always admitted, so no
guard is hiding the problem. -/
def ghostOps : Guarded Nat Ghost where
  eff := ghostEff
  guard := fun _ _ => true

/-- ⚠ **Recoverability fails**: `inc` and `dbl` agree at `0` and disagree at `2`,
so the delta `(0, 1)` does not determine the effect. -/
theorem ghost_not_deltaRecoverable : ¬ DeltaRecoverable ghostOps := by
  intro h
  have heq : ghostEff Ghost.inc = ghostEff Ghost.dbl := h 0 Ghost.inc Ghost.dbl rfl
  exact absurd (congrFun heq 2) (by decide)

/-- ⚠ **…and with it, effect-faithfulness itself.** The triple `(0, 1, 2)` is
produced by `inc,add2` — whose serializations both give `3` — and by `dbl,tri` —
whose serializations both give `5`. No `AncestralMerge Nat` whatsoever is
`Serializing` for these operations.

This is what recoverability is *for*: without it, `Ancestral`'s standing
hypothesis on merges is not a restriction, it is an empty class, and every
∀-quantified impossibility about faithful merges becomes vacuous. -/
theorem ghost_no_faithful_merge (M : AncestralMerge Nat) : ¬ Serializing M ghostOps := by
  intro hser
  exact ambiguous_delta_defeats_faithfulness M ghostOps 0
    Ghost.inc Ghost.add2 Ghost.dbl Ghost.tri rfl rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) hser

/-! ## §2. A legal serialization exists — the resurrection branch, ∀-quantified

`Ancestral.clash_dichotomy` splits a single triple into "some serialization is
legal" (resurrection) or "the merge escalates" (accumulation). `LegalSerialization`
is the first branch demanded everywhere at once — and it is exactly the negation
of the accumulation condition that `serialization_clash_defeats_every_merge`
needs. -/

/-- **Some order of the two recovered effects is legal.** For every legal
ancestor and every pair of locally-admitted operations that are each legal there,
one of the two serializations preserves the invariant. -/
def LegalSerialization (g : Guarded S Op) (I : Invariant S) : Prop :=
  ∀ (l : S) (a b : Op), I l → g.guard a l = true → g.guard b l = true →
    I (g.eff a l) → I (g.eff b l) →
    I (g.eff b (g.eff a l)) ∨ I (g.eff a (g.eff b l))

/-- Failure of `LegalSerialization` *is* a serialization clash in the sense of
`Ancestral.serialization_clash_defeats_every_merge` — the hypothesis bundle that
theorem takes, extracted. (Classical: a `¬∀` becomes an `∃`, exactly as in
`Confluence.escalation_witness`.) -/
theorem exists_clash_of_not_legalSerialization {g : Guarded S Op} {I : Invariant S}
    (h : ¬ LegalSerialization g I) :
    ∃ (l : S) (a b : Op), I l ∧ g.guard a l = true ∧ g.guard b l = true ∧
      I (g.eff a l) ∧ I (g.eff b l) ∧
      ¬ I (g.eff b (g.eff a l)) ∧ ¬ I (g.eff a (g.eff b l)) := by
  apply Classical.byContradiction
  intro hcon
  apply h
  intro l a b hl hga hgb ha hb
  by_cases h1 : I (g.eff b (g.eff a l))
  · exact Or.inl h1
  · by_cases h2 : I (g.eff a (g.eff b l))
    · exact Or.inr h2
    · exact absurd ⟨l, a, b, hl, hga, hgb, ha, hb, h1, h2⟩ hcon

/-- **The dichotomy, ∀-quantified.** For any effect-faithful merge: either every
clash has a legal serialization, or that merge is not ancestrally confluent. This
is `Ancestral.clash_dichotomy` lifted from one triple to the whole
implementation, and it is the sense in which `LegalSerialization` is *exactly*
the negation of accumulation. -/
theorem legalSerialization_or_escalation {g : Guarded S Op} {I : Invariant S}
    (M : AncestralMerge S) (hser : Serializing M g) :
    LegalSerialization g I ∨ ¬ AncestralConfluent M g.impl I := by
  by_cases h : LegalSerialization g I
  · exact Or.inl h
  · obtain ⟨l, a, b, hl, hga, hgb, ha, hb, h1, h2⟩ := exists_clash_of_not_legalSerialization h
    exact Or.inr (serialization_clash_defeats_every_merge M g I l a b hser hl hga hgb ha hb h1 h2)

/-! ## §3. A symmetric chooser — and why the merge law forces it

A chooser orders the two branches: which recovered effect is applied last. Both
replicas run it on the same triple, so it must not depend on which of them is
calling — and that is not a design preference, it is `AncestralMerge.comm`. -/

/-- **A symmetric deterministic chooser.** `sel l x y` returns the two branch
states in the order their effects will be applied. Two laws: the ordering is one
of the two orderings of the inputs, and it does not depend on which replica
asked. -/
structure SymmetricChooser (S : Type u) where
  /-- The chosen ordering: first component's effect is already in place, the
  second component's effect is applied on top of it. -/
  sel : S → S → S → S × S
  /-- The chooser reorders and does not invent. -/
  choice : ∀ l x y, sel l x y = (x, y) ∨ sel l x y = (y, x)
  /-- Both replicas choose the same order from the same triple. -/
  symm : ∀ l x y, sel l x y = sel l y x

/-- **A deterministic tie-break**: a total, antisymmetric preference on states.
This is the "compare replica identifiers" of every real merge procedure, stated
as the algebra it is — and §3.2 shows some such input is *needed*, because
legality alone does not order two orders that are both legal. -/
structure TieBreak (S : Type u) where
  /-- `prefers x y` — `x`'s effect goes first. -/
  prefers : S → S → Bool
  /-- Any two states are comparable. -/
  total : ∀ x y, prefers x y = true ∨ prefers y x = true
  /-- Mutual preference means the states coincide. -/
  antisymm : ∀ x y, prefers x y = true → prefers y x = true → x = y

/-- The ordering a tie-break induces. -/
def TieBreak.pair (T : TieBreak S) (x y : S) : S × S :=
  if T.prefers x y = true then (x, y) else (y, x)

/-- The tie-break reorders and does not invent. -/
theorem TieBreak.pair_choice (T : TieBreak S) (x y : S) :
    T.pair x y = (x, y) ∨ T.pair x y = (y, x) := by
  unfold TieBreak.pair
  by_cases h : T.prefers x y = true
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

/-- **The tie-break is symmetric** — the point of antisymmetry. When both
replicas prefer each other's state the states are equal and there is nothing to
choose; otherwise exactly one preference holds and both sides read it the same
way. -/
theorem TieBreak.pair_comm (T : TieBreak S) (x y : S) : T.pair x y = T.pair y x := by
  unfold TieBreak.pair
  by_cases h : T.prefers x y = true
  · by_cases h' : T.prefers y x = true
    · have hxy : x = y := T.antisymm x y h h'
      rw [hxy]
    · rw [if_pos h, if_neg h']
  · have h' : T.prefers y x = true := (T.total x y).resolve_left h
    rw [if_neg h, if_pos h']

/-- Any injective key into `Nat` gives a tie-break — the standard construction
("order by replica id"), so the hypothesis is cheap wherever states are
enumerable. -/
def TieBreak.ofKey (key : S → Nat) (hinj : ∀ x y : S, key x = key y → x = y) :
    TieBreak S where
  prefers x y := decide (key x ≤ key y)
  total x y := by
    rcases Nat.le_total (key x) (key y) with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true h)
  antisymm x y hxy hyx :=
    hinj x y (Nat.le_antisymm (of_decide_eq_true hxy) (of_decide_eq_true hyx))

/-- `Nat` is its own tie-break. -/
def natTie : TieBreak Nat := TieBreak.ofKey (fun n => n) (fun _ _ h => h)

/-! ## §4. The construction

Fast-forward past a replica that did not move; otherwise order the two branches
with the chooser and replay the second one's recovered effect on top of the
first. Three laws come out: `comm`, `fastforward`, and `Serializing`. -/

/-- The merge induced by a recovery and a raw ordering function. Stated with a
bare `sel` (no laws) so §4.4 can ask what the laws are *for*. -/
def mergeOfSel [DecidableEq S] {g : Guarded S Op} (D : DeltaRecoveryOn g)
    (sel : S → S → S → S × S) (l x y : S) : S :=
  if x = l then y else if y = l then x else D.recover l (sel l x y).2 (sel l x y).1

/-- The merge induced by a symmetric chooser. -/
def mergeOfChooser [DecidableEq S] {g : Guarded S Op} (D : DeltaRecoveryOn g)
    (C : SymmetricChooser S) : S → S → S → S :=
  mergeOfSel D C.sel

/-- The merge is symmetric — **because the chooser is**. The two fast-forward
branches are symmetric by inspection; the third is symmetric exactly when
`C.symm` holds. -/
theorem mergeOfChooser_comm [DecidableEq S] {g : Guarded S Op} (D : DeltaRecoveryOn g)
    (C : SymmetricChooser S) (l x y : S) :
    mergeOfChooser D C l x y = mergeOfChooser D C l y x := by
  unfold mergeOfChooser mergeOfSel
  by_cases hx : x = l
  · by_cases hy : y = l
    · rw [if_pos hx, if_pos hy, hx, hy]
    · rw [if_pos hx, if_neg hy, if_pos hx]
  · by_cases hy : y = l
    · rw [if_neg hx, if_pos hy, if_pos hy]
    · rw [if_neg hx, if_neg hy, if_neg hy, if_neg hx, C.symm l x y]

/-- Fast-forward holds on the nose: it is the merge's first branch. -/
theorem mergeOfChooser_fastforward [DecidableEq S] {g : Guarded S Op}
    (D : DeltaRecoveryOn g) (C : SymmetricChooser S) (l y : S) :
    mergeOfChooser D C l l y = y := by
  unfold mergeOfChooser mergeOfSel
  rw [if_pos rfl]

/-- **The constructed three-way merge.** -/
def ancestralMergeOf [DecidableEq S] {g : Guarded S Op} (D : DeltaRecoveryOn g)
    (C : SymmetricChooser S) : AncestralMerge S where
  merge3 := mergeOfChooser D C
  comm := mergeOfChooser_comm D C
  fastforward := mergeOfChooser_fastforward D C

/-! ### §4.1 Transporting recovery work into the constructed merge -/

/-- The existing construction fed by the semantic projection of a costed
recovery. Its merge function and correctness obligations are unchanged. -/
def costedAncestralMergeOf [DecidableEq S] {g : Guarded S Op} {Step : Type w}
    (D : CostedDeltaRecoveryOn g Step) (C : SymmetricChooser S) : AncestralMerge S :=
  ancestralMergeOf D.erase C

/-- The recovery program executed by the constructed merge. Fast-forwarding
needs no recovery instructions; otherwise the chooser's second branch supplies
the delta program replayed on its first branch. -/
def constructedMergeProgram [DecidableEq S] {g : Guarded S Op} {Step : Type w}
    (D : CostedDeltaRecoveryOn g Step) (C : SymmetricChooser S)
    (l x y : S) : List Step :=
  if x = l then []
  else if y = l then []
  else D.program l (C.sel l x y).2

/-- Work of the constructed merge. It is zero in either fast-forward branch and
the certified recovery work in the replay branch. -/
def constructedMergeWork [DecidableEq S] {g : Guarded S Op} {Step : Type w}
    (D : CostedDeltaRecoveryOn g Step) (C : SymmetricChooser S)
    (l x y : S) : Nat :=
  if x = l then 0
  else if y = l then 0
  else D.work l (C.sel l x y).2

/-- Execute the costed construction directly from its program. This is the
operational witness paired with `costedAncestralMergeOf`; it does not replace the
existing pure merge. -/
def executeConstructedMerge [DecidableEq S] {g : Guarded S Op} {Step : Type w}
    (D : CostedDeltaRecoveryOn g Step) (C : SymmetricChooser S)
    (l x y : S) : S :=
  if x = l then y
  else if y = l then x
  else runRecoverySteps D.applyStep (C.sel l x y).1
    (D.program l (C.sel l x y).2)

/-- The transported program computes exactly the pre-existing constructed merge.
Thus adding the work interface changes no recovery or merge correctness claim. -/
theorem executeConstructedMerge_eq [DecidableEq S] {g : Guarded S Op}
    {Step : Type w} (D : CostedDeltaRecoveryOn g Step) (C : SymmetricChooser S)
    (l x y : S) :
    executeConstructedMerge D C l x y = (costedAncestralMergeOf D C).merge3 l x y := by
  show executeConstructedMerge D C l x y = mergeOfChooser D.erase C l x y
  unfold executeConstructedMerge mergeOfChooser mergeOfSel
  by_cases hx : x = l
  · rw [if_pos hx, if_pos hx]
  · by_cases hy : y = l
    · rw [if_neg hx, if_pos hy, if_neg hx, if_pos hy]
    · rw [if_neg hx, if_neg hy, if_neg hx, if_neg hy]
      exact D.program_correct l (C.sel l x y).2 (C.sel l x y).1

/-- The merge work is exactly the length of the transported program. -/
theorem constructedMergeProgram_length [DecidableEq S] {g : Guarded S Op}
    {Step : Type w} (D : CostedDeltaRecoveryOn g Step) (C : SymmetricChooser S)
    (l x y : S) :
    (constructedMergeProgram D C l x y).length = constructedMergeWork D C l x y := by
  unfold constructedMergeProgram constructedMergeWork
  by_cases hx : x = l
  · rw [if_pos hx, if_pos hx]
    rfl
  · by_cases hy : y = l
    · rw [if_neg hx, if_pos hy, if_neg hx, if_pos hy]
      rfl
    · rw [if_neg hx, if_neg hy, if_neg hx, if_neg hy]
      exact (D.work_eq_program_length l (C.sel l x y).2).symm

/-- Fast-forwarding an unmoved left replica performs no recovery work. -/
theorem constructedMergeWork_fastforward_left [DecidableEq S]
    {g : Guarded S Op} {Step : Type w} (D : CostedDeltaRecoveryOn g Step)
    (C : SymmetricChooser S) (l y : S) :
    constructedMergeWork D C l l y = 0 := by
  simp [constructedMergeWork]

/-- Fast-forwarding an unmoved right replica also performs no recovery work. -/
theorem constructedMergeWork_fastforward_right [DecidableEq S]
    {g : Guarded S Op} {Step : Type w} (D : CostedDeltaRecoveryOn g Step)
    (C : SymmetricChooser S) (l x : S) :
    constructedMergeWork D C l x l = 0 := by
  by_cases hx : x = l <;> simp [constructedMergeWork, hx]

/-- **Per-triple upper bound.** The chooser only reorders `x` and `y`, so the
constructed merge performs at most the larger of their two certified recovery
costs. Fast-forward branches are cheaper still. -/
theorem constructedMergeWork_le_max [DecidableEq S] {g : Guarded S Op}
    {Step : Type w} (D : CostedDeltaRecoveryOn g Step) (C : SymmetricChooser S)
    (l x y : S) :
    constructedMergeWork D C l x y ≤ Nat.max (D.work l x) (D.work l y) := by
  unfold constructedMergeWork
  by_cases hx : x = l
  · rw [if_pos hx]
    exact Nat.zero_le _
  · by_cases hy : y = l
    · rw [if_neg hx, if_pos hy]
      exact Nat.zero_le _
    · rw [if_neg hx, if_neg hy]
      rcases C.choice l x y with h | h
      · rw [h]
        exact Nat.le_max_right _ _
      · rw [h]
        exact Nat.le_max_left _ _

/-- A uniform recovery bound transports unchanged to every constructed merge
triple. -/
theorem constructedMergeWork_le_of_recovery_bound [DecidableEq S]
    {g : Guarded S Op} {Step : Type w} (D : CostedDeltaRecoveryOn g Step)
    (C : SymmetricChooser S) (B : Nat) (hB : ∀ l x, D.work l x ≤ B)
    (l x y : S) : constructedMergeWork D C l x y ≤ B := by
  exact Nat.le_trans (constructedMergeWork_le_max D C l x y)
    (Nat.max_le.mpr ⟨hB l x, hB l y⟩)

/-- The bound specialized to the file's honest resolution: one admitted
operation per branch. It deliberately says nothing about recovering composite
run deltas. -/
theorem constructedMerge_single_step_work_le_max [DecidableEq S]
    {g : Guarded S Op} {Step : Type w} (D : CostedDeltaRecoveryOn g Step)
    (C : SymmetricChooser S) (l : S) (a b : Op) :
    constructedMergeWork D C l (g.eff a l) (g.eff b l) ≤
      Nat.max (D.work l (g.eff a l)) (D.work l (g.eff b l)) :=
  constructedMergeWork_le_max D C l (g.eff a l) (g.eff b l)

/-- **The constructed merge is effect-faithful.** For two admitted operations,
each of the three branches is a serialization: an unmoved side makes the other
side's state the serialization outright, and otherwise the guarded recovery
replays the second operation's effect on the first one's state. `D.spec` is the
only recovery law used, and each use is discharged by that operation's guard. -/
theorem ancestralMergeOf_serializing [DecidableEq S] {g : Guarded S Op}
    (D : DeltaRecoveryOn g) (C : SymmetricChooser S) :
    Serializing (ancestralMergeOf D C) g := by
  intro l a b hga hgb
  show mergeOfSel D C.sel l (g.eff a l) (g.eff b l) = g.eff b (g.eff a l) ∨
       mergeOfSel D C.sel l (g.eff a l) (g.eff b l) = g.eff a (g.eff b l)
  unfold mergeOfSel
  by_cases hx : g.eff a l = l
  · refine Or.inl ?_
    rw [if_pos hx, hx]
  · by_cases hy : g.eff b l = l
    · refine Or.inr ?_
      rw [if_neg hx, if_pos hy, hy]
    · rcases C.choice l (g.eff a l) (g.eff b l) with h | h
      · refine Or.inl ?_
        rw [if_neg hx, if_neg hy, h]
        show D.recover l (g.eff b l) (g.eff a l) = g.eff b (g.eff a l)
        rw [D.spec l b hgb]
      · refine Or.inr ?_
        rw [if_neg hx, if_neg hy, h]
        show D.recover l (g.eff a l) (g.eff b l) = g.eff a (g.eff b l)
        rw [D.spec l a hga]

/-- Cost instrumentation preserves the construction's existing
effect-faithfulness theorem by semantic projection. -/
theorem costedAncestralMergeOf_serializing [DecidableEq S] {g : Guarded S Op}
    {Step : Type w} (D : CostedDeltaRecoveryOn g Step) (C : SymmetricChooser S) :
    Serializing (costedAncestralMergeOf D C) g :=
  ancestralMergeOf_serializing D.erase C

/-! ### §4.2 Invariant preservation needs the chooser to *choose legally*. -/

/-- **Ancestral confluence at one-operation resolution.** The merge of two
concurrently-admitted operations, each legal at a legal ancestor, is legal. This
is the resolution `Ancestral.Serializing` and
`serialization_clash_defeats_every_merge` are stated in; §5 lifts it. -/
def StepConfluent (M : AncestralMerge S) (g : Guarded S Op) (I : Invariant S) : Prop :=
  ∀ (l : S) (a b : Op), I l → g.guard a l = true → g.guard b l = true →
    I (g.eff a l) → I (g.eff b l) → I (M.merge3 l (g.eff a l) (g.eff b l))

/-- Full ancestral confluence restricts to it: a single admitted operation is a
run of length one. -/
theorem stepConfluent_of_ancestralConfluent {g : Guarded S Op} {I : Invariant S}
    (M : AncestralMerge S) (h : AncestralConfluent M g.impl I) : StepConfluent M g I :=
  fun l a b hl hga hgb ha hb =>
    h l (g.eff a l) (g.eff b l) hl ha hb (g.reachable_step hga) (g.reachable_step hgb)

/-- **A discerning chooser**: when either order is legal, the one it picks is.
Note what this does *not* demand — no preference between two legal orders, which
is precisely the freedom the tie-break is needed to resolve. -/
def Discerning {g : Guarded S Op} (D : DeltaRecoveryOn g) (C : SymmetricChooser S)
    (I : Invariant S) : Prop :=
  ∀ l x y : S, (I (D.recover l y x) ∨ I (D.recover l x y)) →
    I (D.recover l (C.sel l x y).2 (C.sel l x y).1)

/-- **The constructed merge preserves the invariant.** The two fast-forward
branches return a replica's own legal state; the third is handed the disjunction
`LegalSerialization` supplies — transported through `D.spec` from *operations* to
*recovered deltas* — and a discerning chooser keeps it. -/
theorem ancestralMergeOf_stepConfluent [DecidableEq S] {g : Guarded S Op}
    {I : Invariant S} (D : DeltaRecoveryOn g) (C : SymmetricChooser S)
    (hdisc : Discerning D C I) (hleg : LegalSerialization g I) :
    StepConfluent (ancestralMergeOf D C) g I := by
  intro l a b hl hga hgb ha hb
  show I (mergeOfSel D C.sel l (g.eff a l) (g.eff b l))
  unfold mergeOfSel
  by_cases hx : g.eff a l = l
  · rw [if_pos hx]
    exact hb
  · by_cases hy : g.eff b l = l
    · rw [if_neg hx, if_pos hy]
      exact ha
    · rw [if_neg hx, if_neg hy]
      refine hdisc l (g.eff a l) (g.eff b l) ?_
      rcases hleg l a b hl hga hgb ha hb with h | h
      · refine Or.inl ?_
        rw [D.spec l b hgb]
        exact h
      · refine Or.inr ?_
        rw [D.spec l a hga]
        exact h

/-- Cost instrumentation likewise preserves the existing one-operation
correctness theorem; no history-general claim is added. -/
theorem costedAncestralMergeOf_stepConfluent [DecidableEq S]
    {g : Guarded S Op} {Step : Type w} {I : Invariant S}
    (D : CostedDeltaRecoveryOn g Step) (C : SymmetricChooser S)
    (hdisc : Discerning D.erase C I) (hleg : LegalSerialization g I) :
    StepConfluent (costedAncestralMergeOf D C) g I :=
  ancestralMergeOf_stepConfluent D.erase C hdisc hleg

/-! ### §4.3 A discerning symmetric chooser exists — the tie-break supplies it.

The naive rule "take the left order when it is legal" is *not* symmetric: when
both orders are legal it prefers whichever replica is asking. The fix is to
consult the tie-break exactly in that case (and in the hopeless case, where the
choice is irrelevant). -/

/-- The chooser built from a tie-break: legality decides when it can, and the
tie-break decides when legality cannot. -/
def tieSel (I : Invariant S) [DecidablePred I] {g : Guarded S Op}
    (D : DeltaRecoveryOn g) (T : TieBreak S) (l x y : S) : S × S :=
  if I (D.recover l y x) then
    (if I (D.recover l x y) then T.pair x y else (x, y))
  else
    (if I (D.recover l x y) then (y, x) else T.pair x y)

theorem tieSel_choice (I : Invariant S) [DecidablePred I] {g : Guarded S Op}
    (D : DeltaRecoveryOn g) (T : TieBreak S) (l x y : S) :
    tieSel I D T l x y = (x, y) ∨ tieSel I D T l x y = (y, x) := by
  unfold tieSel
  by_cases hA : I (D.recover l y x)
  · by_cases hB : I (D.recover l x y)
    · rw [if_pos hA, if_pos hB]
      exact T.pair_choice x y
    · rw [if_pos hA, if_neg hB]
      exact Or.inl rfl
  · by_cases hB : I (D.recover l x y)
    · rw [if_neg hA, if_pos hB]
      exact Or.inr rfl
    · rw [if_neg hA, if_neg hB]
      exact T.pair_choice x y

/-- **Symmetry, case by case.** Swapping the replicas swaps the two legality
tests, so the one-legal cases are symmetric by construction; the both-legal and
neither-legal cases fall to `TieBreak.pair_comm`. -/
theorem tieSel_symm (I : Invariant S) [DecidablePred I] {g : Guarded S Op}
    (D : DeltaRecoveryOn g) (T : TieBreak S) (l x y : S) :
    tieSel I D T l x y = tieSel I D T l y x := by
  unfold tieSel
  by_cases hA : I (D.recover l y x)
  · by_cases hB : I (D.recover l x y)
    · simp only [if_pos hA, if_pos hB]
      exact T.pair_comm x y
    · simp only [if_pos hA, if_neg hB]
  · by_cases hB : I (D.recover l x y)
    · simp only [if_neg hA, if_pos hB]
    · simp only [if_neg hA, if_neg hB]
      exact T.pair_comm x y

/-- **The chooser the construction uses.** -/
def tieChooser (I : Invariant S) [DecidablePred I] {g : Guarded S Op}
    (D : DeltaRecoveryOn g) (T : TieBreak S) : SymmetricChooser S where
  sel := tieSel I D T
  choice := tieSel_choice I D T
  symm := tieSel_symm I D T

/-- **…and it is discerning.** -/
theorem tieChooser_discerning (I : Invariant S) [DecidablePred I] {g : Guarded S Op}
    (D : DeltaRecoveryOn g) (T : TieBreak S) : Discerning D (tieChooser I D T) I := by
  intro l x y h
  show I (D.recover l (tieSel I D T l x y).2 (tieSel I D T l x y).1)
  unfold tieSel
  by_cases hA : I (D.recover l y x)
  · by_cases hB : I (D.recover l x y)
    · rw [if_pos hA, if_pos hB]
      rcases T.pair_choice x y with hp | hp
      · rw [hp]
        exact hA
      · rw [hp]
        exact hB
    · rw [if_pos hA, if_neg hB]
      exact hA
  · by_cases hB : I (D.recover l x y)
    · rw [if_neg hA, if_pos hB]
      exact hB
    · rcases h with h' | h'
      · exact absurd h' hA
      · exact absurd h' hB

/-! ### §4.4 ⚠ The chooser's symmetry is not a taste — `comm` forces it. -/

/-- **A commutative merge has a symmetric chooser.** At any triple where both
replicas moved and the two candidate serializations differ, the merge law
`AncestralMerge.comm` *implies* the ordering function agrees under argument swap.
So `SymmetricChooser.symm` is not an extra assumption bolted onto the
construction; drop it and `AncestralMerge` cannot be built.

(Where the two candidates coincide there is nothing to force, and the chooser
may do as it likes — which is why the hypothesis `hne` is there and is not
removable.) -/
theorem comm_forces_symmetric_chooser [DecidableEq S] {g : Guarded S Op}
    (D : DeltaRecoveryOn g) (sel : S → S → S → S × S)
    (hchoice : ∀ l x y, sel l x y = (x, y) ∨ sel l x y = (y, x))
    (l x y : S) (hx : x ≠ l) (hy : y ≠ l)
    (hne : D.recover l y x ≠ D.recover l x y)
    (hcomm : mergeOfSel D sel l x y = mergeOfSel D sel l y x) :
    sel l x y = sel l y x := by
  have hL : mergeOfSel D sel l x y = D.recover l (sel l x y).2 (sel l x y).1 := by
    unfold mergeOfSel
    rw [if_neg hx, if_neg hy]
  have hR : mergeOfSel D sel l y x = D.recover l (sel l y x).2 (sel l y x).1 := by
    unfold mergeOfSel
    rw [if_neg hy, if_neg hx]
  rw [hL, hR] at hcomm
  rcases hchoice l x y with h1 | h1
  · rcases hchoice l y x with h2 | h2
    · rw [h1, h2] at hcomm
      exact absurd hcomm hne
    · rw [h1, h2]
  · rcases hchoice l y x with h2 | h2
    · rw [h1, h2]
    · rw [h1, h2] at hcomm
      exact absurd hcomm.symm hne

/-! ## §5. THE CONVERSE

Everything assembled. Then the iff, which is the statement this file exists for. -/

/-- **THE CONSTRUCTION.** From a recovery map, a tie-break, and the existence of
a legal serialization, an effect-faithful three-way merge that repairs *every*
resurrection clash — commutative, fast-forwarding, and invariant-preserving on
every admitted concurrent pair. Not "some clash is repairable": the merge is one
function and it is legal at every triple the hypothesis covers. -/
theorem exists_faithful_stepConfluent_merge [DecidableEq S] {g : Guarded S Op}
    (I : Invariant S) [DecidablePred I] (D : DeltaRecoveryOn g) (T : TieBreak S)
    (hleg : LegalSerialization g I) :
    ∃ M : AncestralMerge S, Serializing M g ∧ StepConfluent M g I :=
  ⟨ancestralMergeOf D (tieChooser I D T),
   ancestralMergeOf_serializing D _,
   ancestralMergeOf_stepConfluent D _ (tieChooser_discerning I D T) hleg⟩

/-- The other direction, and it needs no hypothesis at all: a faithful merge that
keeps the invariant *exhibits* the legal serialization, because the state it
lands on is one. This is `serialization_clash_defeats_every_merge`
contraposed. -/
theorem legalSerialization_of_stepConfluent {g : Guarded S Op} {I : Invariant S}
    (M : AncestralMerge S) (hser : Serializing M g) (hst : StepConfluent M g I) :
    LegalSerialization g I := by
  intro l a b hl hga hgb ha hb
  have hm := hst l a b hl hga hgb ha hb
  rcases hser l a b hga hgb with h | h
  · exact Or.inl (h ▸ hm)
  · exact Or.inr (h ▸ hm)

/-- **The same direction, with faithfulness weakened to contextual
equivalence.** A merge that lands merely *indistinguishable* from a serialization
— not on it — still forces a legal serialization to exist. This is where
`CtxEquiv` earns its place: the negative half of the dichotomy is robust to the
coarsening codex's ingredient (1) proposed. -/
theorem legalSerialization_of_stepConfluent_upTo [MergeState S] {g : Guarded S Op}
    {I : Invariant S} [DecidablePred I] (M : AncestralMerge S)
    (hser : SerializingUpTo M g I) (hst : StepConfluent M g I) :
    LegalSerialization g I := by
  intro l a b hl hga hgb ha hb
  have hm := hst l a b hl hga hgb ha hb
  rcases hser l a b hga hgb with h | h
  · exact Or.inl (legal_of_ctxEquiv h hm)
  · exact Or.inr (legal_of_ctxEquiv h hm)

/-- ⚑ **THE CONVERSE, AS AN IFF.** For a guard-relatively delta-recoverable
implementation with a tie-break: an effect-faithful ancestral merge that repairs
every resurrection clash **exists exactly when some serialization is always
legal**.

Read against `Ancestral`: `clash_dichotomy` said *either* a serialization is
legal *or* the merge escalates, and left open whether the first branch is ever
enough. It is, and it is the only thing that matters — the whole question
collapses onto `LegalSerialization`, with recoverability and the chooser as the
machinery that turns it into a merge rather than as further conditions on the
invariant. -/
theorem faithful_stepConfluent_iff_legalSerialization [DecidableEq S]
    {g : Guarded S Op} {I : Invariant S} [DecidablePred I]
    (D : DeltaRecoveryOn g) (T : TieBreak S) :
    (∃ M : AncestralMerge S, Serializing M g ∧ StepConfluent M g I)
      ↔ LegalSerialization g I :=
  ⟨fun ⟨M, hser, hst⟩ => legalSerialization_of_stepConfluent M hser hst,
   fun hleg => exists_faithful_stepConfluent_merge I D T hleg⟩

/-! ### §5.1 From one operation to a whole run — the state-only boundary and
the cheapest local bridge.

`AncestralConfluent` quantifies over branches that are *runs*. A run's composite
delta is not an `Op`, so `Serializing` — which speaks only of single operations —
says nothing about it, and this file's endpoint-only construction cannot see it.
`Uwueave.CompositeDelta` now supplies the explicit-patch alternative: admitted
finite patches, residual/commutation laws, an exact
`LegalUnderComposition ↔ AncestralConfluent` transport, and a minimal
patch-labelled history-edge adapter. The remaining gap is narrower: generically
recovering those composite patches from states alone, or synthesizing the merge
without carrying them, is neither assumed nor proved.

`StepGenerated` is the cheapest sufficient stand-in: the state space itself
collapses runs to steps. The lock satisfies it; the counter does not. -/

/-- **Every reachable branch is the ancestor or one admitted step from it.** True
of replacement-style operations (the lock: each op overwrites, so a run's end
state is its last op's effect), false whenever operations accumulate. -/
def StepGenerated (g : Guarded S Op) (I : Invariant S) : Prop :=
  ∀ l x : S, I l → Reachable g.impl l x →
    x = l ∨ ∃ a : Op, g.guard a l = true ∧ g.eff a l = x

/-- **Step confluence lifts to full ancestral confluence** under step generation.
The two ancestor cases are discharged by `fastforward` and `fastforward_left` —
which is ingredient (4) doing its work: a merge without fast-forward would have
nothing to say about a branch that did not move. -/
theorem stepConfluent_implies_ancestralConfluent {g : Guarded S Op} {I : Invariant S}
    (M : AncestralMerge S) (hsg : StepGenerated g I) (hst : StepConfluent M g I) :
    AncestralConfluent M g.impl I := by
  intro l x y hl hx hy hrx hry
  rcases hsg l x hl hrx with hxl | ⟨a, hga, hax⟩
  · subst hxl
    rw [M.fastforward]
    exact hy
  · rcases hsg l y hl hry with hyl | ⟨b, hgb, hby⟩
    · subst hyl
      rw [M.fastforward_left]
      exact hx
    · subst hax
      subst hby
      exact hst l a b hl hga hgb hx hy

/-- **The converse, at the resolution `AncestralConfluent` is stated in** — the
construction plus the step-generation bridge. -/
theorem exists_faithful_ancestralConfluent_merge [DecidableEq S] {g : Guarded S Op}
    (I : Invariant S) [DecidablePred I] (D : DeltaRecoveryOn g) (T : TieBreak S)
    (hleg : LegalSerialization g I) (hsg : StepGenerated g I) :
    ∃ M : AncestralMerge S, Serializing M g ∧ AncestralConfluent M g.impl I := by
  obtain ⟨M, hser, hst⟩ := exists_faithful_stepConfluent_merge I D T hleg
  exact ⟨M, hser, stepConfluent_implies_ancestralConfluent M hsg hst⟩

/-- ⚠ **The gap is real, and here it is.** The counter MRDT at budget `2` under
the ceiling `n ≤ 3`: `counterAM` is effect-faithful (`Ancestral.counter_serializing`)
and **step-confluent** — the guard admits an operation only at `0` and `1`, and
both one-operation merges land on `2` and `3` — yet two branches that each spend
twice reach `2` and merge to `4`.

So `stepConfluent_implies_ancestralConfluent` cannot drop `StepGenerated`, and a
repair complete at one operation per branch can fail at two. `CompositeDelta`
does not erase this witness: `stepConfluent_counter_fails_composite_law` proves
that the same merge fails `LegalUnderComposition`. Note also what this does
**not** say — a different merge may be ancestrally confluent here. The remaining
open construction problem is the generic endpoint-only synthesis named above,
not the now-formal explicit-patch residual law. -/
theorem stepConfluent_does_not_imply_ancestralConfluent :
    Serializing counterAM (spendOps 2)
      ∧ StepConfluent counterAM (spendOps 2) (fun n => n ≤ 3)
      ∧ ¬ AncestralConfluent counterAM (spendOps 2).impl (fun n => n ≤ 3) := by
  refine ⟨counter_serializing 2, ?_, ?_⟩
  · intro l a b _ hga _ _ _
    have hl2 : l + 1 ≤ 2 := by simpa [spendOps] using hga
    show counterMerge l (l + 1) (l + 1) ≤ 3
    unfold counterMerge
    omega
  · intro hac
    have hr : Reachable (spendOps 2).impl 0 2 :=
      ⟨[(), ()], by show run (spendOps 2).impl 0 [(), ()] = some 2; decide⟩
    have hm := hac 0 2 2 (by omega) (by omega) (by omega) hr hr
    have hval : counterAM.merge3 0 2 2 = 4 := by
      show counterMerge 0 2 2 = 4
      unfold counterMerge
      omega
    rw [hval] at hm
    omega

/-- **And the missing ingredient is not the legal serialization.** The same
implementation *has* one everywhere — the guard keeps every admitted ancestor at
`1` or below, so both spends fit under the ceiling — hence by §5's iff a faithful
step-confluent merge exists for it, and the run-level failure above is exactly
the failure of `CompositeDelta.LegalUnderComposition` for `counterAM`. This is
the cleanest available description of what the composite law adds. -/
theorem step_repair_does_not_lift :
    LegalSerialization (spendOps 2) (fun n => n ≤ 3)
      ∧ ∃ M : AncestralMerge Nat, Serializing M (spendOps 2) ∧
          StepConfluent M (spendOps 2) (fun n => n ≤ 3) := by
  have hleg : LegalSerialization (spendOps 2) (fun n => n ≤ 3) := by
    intro l a b _ hga _ _ _
    refine Or.inl ?_
    have hl2 : l + 1 ≤ 2 := by simpa [spendOps] using hga
    show l + 1 + 1 ≤ 3
    omega
  exact ⟨hleg, exists_faithful_stepConfluent_merge _ (spendRecovery 2).toOn natTie hleg⟩

/-! ## §6. The lock is an instance — the test of whether the converse has content

`Ancestral` §5 built `lockMerge`, `lockPriority` and the proof by hand. Here the
same theorem about the same merge falls out of the general construction from four
checkable facts. -/

/-- The lock's tie-break key: nobody `<` Bob `<` Alice. This is `lockPriority`'s
preference, written as an order rather than as a nest of `if`s. -/
def lockKey (s : Lock) : Nat := (if s.alice then 2 else 0) + (if s.bob then 1 else 0)

/-- The key is injective on the four lock states, so it is a tie-break. -/
def lockTie : TieBreak Lock :=
  TieBreak.ofKey lockKey (by
    intro x y h
    obtain ⟨xa, xb⟩ := x
    obtain ⟨ya, yb⟩ := y
    cases xa <;> cases xb <;> cases ya <;> cases yb <;>
      first
        | rfl
        | exact absurd h (by decide))

/-- **The lock always has a legal serialization** — trivially, because every lock
operation lands on a legal state whatever it is applied to. This is the
resurrection branch of `clash_dichotomy` holding everywhere. -/
theorem lock_legalSerialization : LegalSerialization lockOps AtMostOne := by
  intro l a b _ _ _ _ _
  refine Or.inl ?_
  show AtMostOne (lockEff b (lockEff a l))
  rw [lockEff_const b (lockEff a l) l]
  cases b
  · show AtMostOne ⟨true, false⟩
    decide
  · show AtMostOne ⟨false, true⟩
    decide
  · show AtMostOne ⟨false, false⟩
    decide

/-- A lock run ends at its last operation's effect — because each operation
overwrites the holder state, the intermediate states are invisible. -/
theorem lock_run_is_one_step : ∀ (ops : List LockOp) (l x : Lock),
    RunsTo lockImpl l x ops → x = l ∨ ∃ a : LockOp, lockEff a l = x
  | [], l, x, h => Or.inl (by simp [RunsTo, run] at h; exact h.symm)
  | op :: ops, l, x, h => by
      have hstep : lockImpl.tryApply op l = some (lockEff op l) := rfl
      have h' : RunsTo lockImpl (lockEff op l) x ops := by
        rw [RunsTo, run_cons_some lockImpl l op ops hstep] at h
        exact h
      rcases lock_run_is_one_step ops (lockEff op l) x h' with hx | ⟨a, ha⟩
      · exact Or.inr ⟨op, hx.symm⟩
      · refine Or.inr ⟨a, ?_⟩
        rw [lockEff_const a l (lockEff op l)]
        exact ha

/-- **The lock is step-generated**, so §5.1's bridge applies to it. -/
theorem lock_stepGenerated : StepGenerated lockOps AtMostOne := by
  intro l x _ hr
  obtain ⟨ops, hrun⟩ := hr
  rcases lock_run_is_one_step ops l x hrun with h | ⟨a, ha⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, rfl, ha⟩

/-- The merge the general construction produces for the lock. -/
def lockConstructedMerge : AncestralMerge Lock :=
  ancestralMergeOf lockRecovery.toOn (tieChooser AtMostOne lockRecovery.toOn lockTie)

/-- The same constructed lock merge, now carrying the cheap one-step recovery
certificate. Erasing its cost data gives `lockConstructedMerge` definitionally. -/
def cheapCostedLockConstructedMerge : AncestralMerge Lock :=
  costedAncestralMergeOf cheapLockRecovery
    (tieChooser AtMostOne cheapLockRecovery.erase lockTie)

/-- Cost instrumentation does not change the constructed lock merge. -/
theorem cheapCostedLockConstructedMerge_eq :
    cheapCostedLockConstructedMerge = lockConstructedMerge := rfl

/-- Every triple of the cheaply instrumented lock merge costs at most one
recovery instruction; either fast-forward costs zero or the one write runs. -/
theorem cheapLockConstructedMerge_work_le_one (l x y : Lock) :
    constructedMergeWork cheapLockRecovery
      (tieChooser AtMostOne cheapLockRecovery.erase lockTie) l x y ≤ 1 := by
  apply constructedMergeWork_le_of_recovery_bound cheapLockRecovery
    (tieChooser AtMostOne cheapLockRecovery.erase lockTie) 1
  intro l' x'
  exact Nat.le_of_eq (cheapLockRecovery_work l' x')

/-- On the genuine both-moved lock triple, padding reaches the constructed merge
unchanged: `n` certified identity steps plus the write cost exactly `n + 1`.
This is the merge-level witness that recovery correctness alone does not fix a
cost. -/
theorem paddedLockConstructedMerge_both_moved_work (n : Nat) :
    constructedMergeWork (paddedLockRecovery n)
      (tieChooser AtMostOne (paddedLockRecovery n).erase lockTie)
      ⟨false, false⟩ ⟨true, false⟩ ⟨false, true⟩ = n + 1 := by
  simp [constructedMergeWork, paddedLockRecovery_work]

/-- ⚑ **The construction rediscovers `lockMerge`.** On legal replicas — which is
every triple `AncestralConfluent` quantifies over — the merge built from
`lockRecovery` and the `lockKey` tie-break **is** `Ancestral`'s hand-written
`lockMerge`. Computed: the four-state space gives 64 triples, the 28 with an
illegal replica are discharged by the hypotheses and the remaining 36 are
evaluated on both sides. `lockPriority`'s "Alice over Bob over
nobody" was not a free invention: it is the tie-break, and the general chooser
finds it. -/
theorem lockConstructed_eq_lockMerge : ∀ l x y : Lock, AtMostOne x → AtMostOne y →
    lockConstructedMerge.merge3 l x y = lockMerge l x y := by
  intro ⟨la, lb⟩ ⟨xa, xb⟩ ⟨ya, yb⟩ hx hy
  cases la <;> cases lb <;> cases xa <;> cases xb <;> cases ya <;> cases yb <;>
    first
      | exact absurd hx (by decide)
      | exact absurd hy (by decide)
      | decide

/-- The constructed merge on the exact triple that busts the two-way join —
ancestor "Alice holds", one replica handed off to Bob, the other did nothing.
Set beside `Ancestral.lock_clash_triple_merges_legally`: same triple, same
answer, built rather than written. -/
theorem lockConstructed_clash_triple :
    lockConstructedMerge.merge3 ⟨true, false⟩ ⟨false, true⟩ ⟨true, false⟩
      = ⟨false, true⟩ := by decide

/-- **The chooser branch really fires.** From "nobody holds it", one replica
grants to Alice and the other to Bob — neither fast-forward branch applies, so
the verdict is the tie-break's, and it is Alice. The identification with
`lockMerge` is therefore not carried by the fast-forward cases alone. -/
theorem lockConstructed_both_moved :
    lockConstructedMerge.merge3 ⟨false, false⟩ ⟨true, false⟩ ⟨false, true⟩
      = ⟨true, false⟩ := by decide

/-- **The prize, re-proved.** `Ancestral.lock_ancestral_confluent` — the same
statement about the same merge `lockAM` — is an instance of the general
construction: recovery + tie-break + a legal serialization + step generation, all
four checked above, and no hand-built merge argument anywhere. That is the test
of whether the converse has content, and it passes. -/
theorem lock_ancestral_confluent_is_an_instance :
    AncestralConfluent lockAM lockImpl AtMostOne := by
  have hst : StepConfluent lockConstructedMerge lockOps AtMostOne :=
    ancestralMergeOf_stepConfluent lockRecovery.toOn _
      (tieChooser_discerning AtMostOne lockRecovery.toOn lockTie) lock_legalSerialization
  have hac : AncestralConfluent lockConstructedMerge lockOps.impl AtMostOne :=
    stepConfluent_implies_ancestralConfluent lockConstructedMerge lock_stepGenerated hst
  intro l x y hl hx hy hrx hry
  show AtMostOne (lockMerge l x y)
  rw [← lockConstructed_eq_lockMerge l x y hx hy]
  exact hac l x y hl hx hy hrx hry

/-- The lock's own instance of the existence theorem, stated the way §5 states
it — with the merge quantified existentially rather than named. -/
theorem lock_faithful_merge_exists :
    ∃ M : AncestralMerge Lock, Serializing M lockOps ∧
      AncestralConfluent M lockImpl AtMostOne :=
  exists_faithful_ancestralConfluent_merge AtMostOne lockRecovery.toOn lockTie
    lock_legalSerialization lock_stepGenerated

/-! ## §7. The boundary: accumulation fails at exactly one hypothesis

The bounded counter satisfies everything the construction asks for **except**
`LegalSerialization`, and the iff of §5 applies to it in full — same theorem,
other data type, other verdict. -/

/-- ⚠ **The counter has no legal serialization.** From one unit below the budget
both replicas legally spend it, and both orders spend two. This is the *only*
hypothesis of the construction the counter fails: `spendRecovery` is a recovery
map, `natTie` is a tie-break, equality and the invariant are decidable. -/
theorem budget_not_legalSerialization (B : Nat) :
    ¬ LegalSerialization (spendOps (B + 1)) (fun n => n ≤ B + 1) := by
  intro h
  have hg : (spendOps (B + 1)).guard () B = true := by simp [spendOps]
  have hstep : (fun n => n ≤ B + 1) ((spendOps (B + 1)).eff () B) := by simp [spendOps]
  rcases h B () () (by omega) hg hg hstep hstep with hbad | hbad
  · exact absurd hbad (by simp only [spendOps]; omega)
  · exact absurd hbad (by simp only [spendOps]; omega)

/-- ⚑ **The boundary, as one statement.** Every hypothesis of the construction
holds for the bounded counter, `LegalSerialization` fails, and — by the iff, not
by a separate argument — no effect-faithful merge repairs it. The dichotomy of
`Ancestral` §8 is now an equivalence with a witness on each side: the lock
satisfies the right-hand side and gets a merge, the counter refutes it and gets
the impossibility. -/
theorem budget_boundary (B : Nat) :
    Nonempty (DeltaRecoveryOn (spendOps (B + 1))) ∧ Nonempty (TieBreak Nat)
      ∧ ¬ LegalSerialization (spendOps (B + 1)) (fun n => n ≤ B + 1)
      ∧ ¬ ∃ M : AncestralMerge Nat, Serializing M (spendOps (B + 1)) ∧
            StepConfluent M (spendOps (B + 1)) (fun n => n ≤ B + 1) :=
  ⟨⟨(spendRecovery (B + 1)).toOn⟩, ⟨natTie⟩, budget_not_legalSerialization B,
   fun hex => budget_not_legalSerialization B
     ((faithful_stepConfluent_iff_legalSerialization (spendRecovery (B + 1)).toOn natTie).mp hex)⟩

/-- **`Ancestral.budget_defeats_every_faithful_merge`, re-derived from the iff.**
Not a second proof of the same fact by the same route: there the impossibility
was primitive, here it is the failing side of the equivalence, which is what
makes "the LCA neutralizes resurrection and never accumulation" a single theorem
rather than a slogan over two. -/
theorem budget_defeats_every_faithful_merge_again (B : Nat) (M : AncestralMerge Nat)
    (hser : Serializing M (spendOps (B + 1))) :
    ¬ AncestralConfluent M (spendOps (B + 1)).impl (fun n => n ≤ B + 1) := by
  intro hac
  exact (budget_boundary B).2.2.2
    ⟨M, hser, stepConfluent_of_ancestralConfluent M hac⟩

/-! ## §8. The verdict

`Ancestral.clash_dichotomy` gave a design rule with a hole in it: *when the
operations can be run in some legal order, the LCA is the fix* — but nothing said
the fix exists. It does, under exactly three conditions, and the conditions are
the ones codex named:

  * the merge must be able to tell what each admitted branch did
    (`DeltaRecoveryOn`),
    without which effect-faithfulness is not merely hard but **unsatisfiable**
    (`ghost_no_faithful_merge`);
  * some order of the two deltas must be legal (`LegalSerialization`), which the
    iff shows is the whole content;
  * both replicas must choose the same order (`SymmetricChooser`), which the
    merge law `comm` forces (`comm_forces_symmetric_chooser`) and a tie-break
    supplies.

What is left open is stated where it lives, and the first is left open *with a
counterexample rather than a caveat*: multi-operation branches
(§5.1 — `stepConfluent_does_not_imply_ancestralConfluent` shows a step-complete
repair failing at length two, and `step_repair_does_not_lift` shows the missing
ingredient is history coherence and not legality; sibling file), the general
compositional form of guard-relative recovery beyond one operation (§1 and
§5.1), and any claim about *which* legal merge is the right one (§4.3, a free
parameter). -/

end Uwueave.Recoverable
