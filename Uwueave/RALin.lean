/-
# Uwueave.RALin — replication-aware linearizability in miniature, and the reason
a verified data type is still not a verified application.

Everything else in this library asks one question about a merge: *may this
application invariant be enforced without coordination?* There is a second,
entirely different question a merge can be asked: *is this merge a correct
implementation of the data type at all?* — is the state it produces explicable
as some sequential execution of the updates that were concurrent?

That second question is **replication-aware (RA) linearizability** (Wang, Enea,
Mutluergil, Petri, PLDI 2019), and it is the question **Sal** answers:

> Pranav Ramesh, Vimala Soundarapandian, KC Sivaramakrishnan (IIT Madras),
> *Sal: Multi-modal Verification of Replicated Data Types*, arXiv:2603.27202,
> 28 Mar 2026.

Sal is very good work and this file is a composition with it, not a rebuttal.
It verifies state-based CRDT and MRDT *implementations* in Lean against the
RA-linearizability verification conditions of Neem (Soundarapandian, Nagar,
Rastogi, Sivaramakrishnan, OOPSLA 2025), which reduces RA-linearizability for
those classes to a finite set of 24 VCs over `do`, `merge` and the conflict
resolution policy `rc`. Its contribution is a staged tactic that tries
kernel-checkable automation first (`dsimp`+`grind`, 69.1% of 311 VCs across 13
RDTs), falls back to SMT (`lean-blaster`/Z3) only when it must, and to
AI-assisted interactive proof last — plus, when a VC is *false*, Plausible
counterexamples and a ProofWidgets trace visualizer that turns an opaque proof
failure into a runnable execution you can read. It rediscovers the enable-wins
flag anomaly that way. Keeping SMT out of the trusted computing base while
still discharging most obligations automatically is exactly the right shape for
this problem.

## The thesis this file proves

**The two questions are orthogonal, and correctness needs both answered.**

  * `ra_linearizable_but_unsafe` — a merge that **is** RA-linearizable, on a data
    type whose implementation is beyond reproach, carrying an application
    invariant that **is not** I-confluent. Every replica is legal at every step
    it takes; the merged state is explicable as a sequential execution of the
    two spends; and the balance is negative. Sal's checker is *right* and the
    money is *gone*.
  * `maxctr_not_ra_linearizable` with `maxctr_every_invariant_iconfluent` — the
    converse: a counter that silently loses updates (not RA-linearizable, and
    Sal's counterexample generator is precisely the tool that finds this) over
    which **every** invariant whatsoever is I-confluent. The data type is wrong;
    no application invariant can ever be broken by a merge.
  * `quadrants` — all four cells inhabited, each by a proof. Not "here is one
    example each way": the two predicates are independent at miniature scale.

And the two are not merely independent, they are **entangled**, which is the
part worth carrying away:

  * `ra_lin_preserves_inductive_invariants` — what RA-linearizability *does* buy
    you, stated positively: any invariant preserved by every single `do` step
    survives every RA-linearizable merge. That is a real theorem and a real
    gift.
  * `guarding_moves_the_bug` — and its edge. The standard repair for
    `ra_linearizable_but_unsafe` is to guard the operation so the invariant
    *becomes* inductive (refuse to spend what you do not have). Do that and the
    **same merge — the same function, proved unchanged** — stops being
    RA-linearizable, as a corollary of the bridge theorem rather than a second
    hand computation. The two verdicts do not move together: I-confluence's is
    unchanged, because nothing it depends on changed, and it was reporting the
    overdraft the whole time; RA-linearizability's flips, in response to a
    precondition on an operation. A verdict that can flip while the merge holds
    still is not a verdict about the merge alone — and the cell where it reads
    *fine* is exactly the cell where the money goes missing.

## What is modeled, and what is not — read this before citing the file

This is a **miniature**. The fidelity boundary, stated flat:

1. **One merge, two branches, one fork point.** `RALinearizable R lca opsL opsR`
   says: the state `merge3 lca (run lca opsL) (run lca opsR)` is reproduced by
   running *some* interleaving of `opsL` and `opsR` sequentially from `lca`.
   Sal's and Neem's VCs cover arbitrary execution DAGs with nested merges, via
   the bottom-up linearization the paper describes (peel the last event off a
   branch, apply it after the merge, recurse). A single merge node is the base
   case of that induction and nothing more. Lifting this to DAGs is undone and
   doable: it needs a history type with merge nodes, and the peeling step as a
   recursive predicate over it — `Uwueave.CausalReach`'s `FinHistory`/`Cut` is
   the right carrier to build it on.
2. **Not Neem's 24 VCs.** I model the semantic condition directly. I do not
   model the reduction to VCs, and nothing here claims my condition is
   equivalent to the conjunction of theirs. A `¬ RALinearizable` result in this
   file means "this merge has no sequential explanation *in this miniature*",
   which is evidence of the same shape as a failing VC, not the same object.
3. **`do`'s timestamp and replica arguments are folded into the op type.** The
   paper's `do : Σ × T × R × O → Σ`; here an `Op` value *is* the triple, so the
   information is present and the signature is one argument shorter.
4. **`rc` is modeled as a precedence constraint on the linearization** between
   cross-branch pairs (`rcOK`), which is its operational content for a single
   merge. It is load-bearing rather than decorative:
   `orset_rc_selects_the_linearization` exhibits the paper's own add-wins OR-Set
   where of the two interleavings, exactly one respects `rc` *and* explains the
   merge, and the other does neither.
5. **Both merge shapes are expressible; the exhibits use both.** `merge3` takes
   the LCA, so MRDT three-way merges fit (the OR-Set exhibit uses the paper's
   own three-way formula verbatim). The counter exhibits ignore the LCA, i.e.
   they are the state-based CRDT case where `merge3 lca x y = x ⊔ y` is the
   semilattice join — which is the half of the paper that meets this library's
   `MergeState`, and the only half where an `IConfluent` verdict is even
   stated.
6. **The model is satisfiable and refutable** — `ra_model_is_falsifiable`. A
   condition nothing can fail is not a condition, and three exhibits here fail
   it (`maxctr_not_ra_linearizable`, `pn_shared_slot_not_ra_linearizable`,
   `guarding_moves_the_bug`) — the last by an argument that never computes an
   interleaving. `rcOK` is falsifiable too, and is falsified, in §3.

## Literature

  * Ramesh, Soundarapandian, Sivaramakrishnan — *Sal: Multi-modal Verification
    of Replicated Data Types*, arXiv:2603.27202, 2026.
  * Wang, Enea, Mutluergil, Petri — *Replication-aware linearizability*, PLDI
    2019. (The condition itself.)
  * Soundarapandian, Nagar, Rastogi, Sivaramakrishnan — *Certified Mergeable
    Replicated Data Types* / Neem, OOPSLA 2025. (The reduction to VCs.)
  * Kaki, Priya, Sivaramakrishnan, Jagannathan — *Mergeable Replicated Data
    Types*, OOPSLA 2019. (MRDTs, the three-way merge.)
  * Bailis, Fekete, Franklin, Ghodsi, Hellerstein, Stoica — *Coordination
    Avoidance in Database Systems*, VLDB 2015. (I-confluence — the other axis.)
-/
import Uwueave.Catalog

namespace Uwueave.RALin

open Uwueave Uwueave.Catalog

/-! ## §1. The model

An RDT in the paper's shape, cut down to what a single merge needs. -/

/-- **A replicated data type**, in the shape of the paper's
`D_τ = ⟨Σ, σ₀, do, merge, rc⟩` minus the initial state (every statement here
starts from an explicit fork point instead):

  * `doOp` — the paper's `do`, with `T × R` folded into `Op`;
  * `merge3 lca x y` — the paper's three-way `merge`; a state-based CRDT is the
    case that ignores `lca` and returns the semilattice join;
  * `rcBefore o o' = true` — the paper's `(o, o') ∈ rc`: when `o` and `o'` are
    concurrent and conflicting, `o` is ordered *before* `o'`. -/
structure RDT (S : Type) (Op : Type) where
  /-- The update function: apply one operation to one replica's state. -/
  doOp : S → Op → S
  /-- Three-way merge: lowest common ancestor, then the two branch states. -/
  merge3 : S → S → S → S
  /-- Conflict resolution policy, as a precedence on operations. -/
  rcBefore : Op → Op → Bool

variable {S Op : Type}

/-- Run a sequence of operations from a state. This is the *sequential*
semantics — the thing a linearization has to reproduce. -/
def runFrom (R : RDT S Op) (s : S) (ops : List Op) : S := ops.foldl R.doOp s

@[simp] theorem runFrom_nil (R : RDT S Op) (s : S) : runFrom R s [] = s := rfl

@[simp] theorem runFrom_cons (R : RDT S Op) (s : S) (o : Op) (l : List Op) :
    runFrom R s (o :: l) = runFrom R (R.doOp s o) l := rfl

theorem runFrom_append (R : RDT S Op) (s : S) (l₁ l₂ : List Op) :
    runFrom R s (l₁ ++ l₂) = runFrom R (runFrom R s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons o l ih => exact ih (R.doOp s o)

/-- The right-hand half of `interleavings`: every order-preserving interleaving
of `a :: l` with the second branch, given `f = interleavings l` for the tail.
Split out so both recursions are *structural* — which is what lets `decide`
evaluate an interleaving set inside the kernel, and hence what lets a
`¬ RALinearizable` result be checked rather than argued. -/
def mergeWith (f : List Op → List (List Op)) (a : Op) (l : List Op) :
    List Op → List (List Op)
  | [] => [a :: l]
  | b :: r => (f (b :: r)).map (a :: ·) ++ (mergeWith f a l r).map (b :: ·)

/-- Every order-preserving interleaving of two branches: the candidate
linearizations. Each branch's own order is causal and must survive; only the
cross-branch order is free, and `rcOK` below constrains even that. -/
def interleavings : List Op → List Op → List (List Op)
  | [], r => [r]
  | a :: l, r => mergeWith (interleavings l) a l r

/-- Concatenation is always one of the interleavings — "everything the left
replica did, then everything the right one did". This is the witness every
positive result in this file uses. -/
theorem append_mem_interleavings (l r : List Op) : (l ++ r) ∈ interleavings l r := by
  induction l with
  | nil => simp [interleavings]
  | cons a l ih =>
    cases r with
    | nil => simp [interleavings, mergeWith]
    | cons b r =>
      show (a :: (l ++ b :: r)) ∈ _
      rw [interleavings, mergeWith]
      exact List.mem_append_left _ (List.mem_map_of_mem ih)

/-- `occursBefore a b l` — of the two operations, `a` is the one the sequence
reaches first. (First occurrence; the exhibits give every operation a distinct
timestamp, so there is nothing ambiguous to resolve.) -/
def occursBefore [DecidableEq Op] (a b : Op) : List Op → Bool
  | [] => false
  | x :: xs => if x = a then true else if x = b then false else occursBefore a b xs

/-- **The `rc` obligation on a linearization.** For every cross-branch pair the
policy orders, the linearization must place them that way round. With `rc = ∅`
this is vacuously satisfied and every interleaving is admissible; with the
OR-Set's `rc = {(rem_e, add_e)}` it is what "adds win" *means* once you are
reading the merge as a sequential execution. -/
def rcOK [DecidableEq Op] (R : RDT S Op) (opsL opsR l : List Op) : Bool :=
  opsL.all fun a => opsR.all fun b =>
    (!R.rcBefore a b || occursBefore a b l) && (!R.rcBefore b a || occursBefore b a l)

/-- `l` reproduces the merged state by running sequentially from the fork
point. This is the equation the whole condition is about. -/
def Explains (R : RDT S Op) (lca : S) (opsL opsR l : List Op) : Prop :=
  runFrom R lca l = R.merge3 lca (runFrom R lca opsL) (runFrom R lca opsR)

/-- `l` is a legal linearization of the two branches: it respects the conflict
policy, and it explains the merged state. -/
def Linearizes [DecidableEq Op] (R : RDT S Op) (lca : S) (opsL opsR l : List Op) : Prop :=
  rcOK R opsL opsR l = true ∧ Explains R lca opsL opsR l

/-- **RA-linearizability of one merge, in miniature.** The merged state is
explicable as *some* sequential execution of the two branches' updates, taken in
an order that preserves each branch and respects the conflict policy.

Read the fidelity boundary in the header before citing this as "the paper's
definition": it is the single-merge base case of it, and it is stated against
the implementation's own `do` rather than against a separate abstract
specification. -/
def RALinearizable [DecidableEq Op] (R : RDT S Op) (lca : S) (opsL opsR : List Op) : Prop :=
  ∃ l ∈ interleavings opsL opsR, Linearizes R lca opsL opsR l

instance [DecidableEq Op] [DecidableEq S] (R : RDT S Op) (lca : S) (opsL opsR l : List Op) :
    Decidable (Linearizes R lca opsL opsR l) := by
  unfold Linearizes Explains; infer_instance

instance [DecidableEq Op] [DecidableEq S] (R : RDT S Op) (lca : S) (opsL opsR : List Op) :
    Decidable (RALinearizable R lca opsL opsR) := by
  unfold RALinearizable; infer_instance

/-- Every intermediate state of a branch is legal, not just its endpoints. This
is what a replica enforcing an invariant locally actually guarantees, and it is
the hypothesis that makes `ra_linearizable_but_unsafe` sting: nobody cheated
anywhere. -/
def SafeRun (R : RDT S Op) (I : Invariant S) : S → List Op → Prop
  | s, [] => I s
  | s, o :: l => I s ∧ SafeRun R I (R.doOp s o) l

/-! ### The bridge — what RA-linearizability is worth

Stated positively and first, because it is a real guarantee and the rest of the
file is about its edge. -/

/-- An invariant preserved by one step is preserved by any run of steps. -/
theorem runFrom_preserves {R : RDT S Op} {I : Invariant S}
    (hstep : ∀ s o, I s → I (R.doOp s o)) :
    ∀ (s : S) (l : List Op), I s → I (runFrom R s l) := by
  intro s l
  induction l generalizing s with
  | nil => exact id
  | cons o l ih => exact fun hs => ih (R.doOp s o) (hstep s o hs)

/-- **What an RA-linearizable merge does guarantee.** If the invariant holds at
the fork point and is preserved by *every* single operation — an *inductive*
invariant of the sequential data type — then it holds of the merged state, for
free, because the merged state is a state the sequential type can reach.

This is the theorem that makes RA-linearizability worth verifying, and it is the
reason `guarding_moves_the_bug` below is a corollary rather than a coincidence.
The premise is the whole story: `hstep` must hold at *every* state and *every*
operation, with no precondition. -/
theorem ra_lin_preserves_inductive_invariants [DecidableEq Op] {R : RDT S Op}
    {I : Invariant S} (hstep : ∀ s o, I s → I (R.doOp s o))
    {lca : S} {opsL opsR : List Op} (hlca : I lca)
    (h : RALinearizable R lca opsL opsR) :
    I (R.merge3 lca (runFrom R lca opsL) (runFrom R lca opsR)) := by
  obtain ⟨l, _, _, heq⟩ := h
  rw [← heq]
  exact runFrom_preserves hstep lca l hlca

/-! ## §2. The headline: a correct counter, a legal merge, a negative balance.

The PN-counter of `Catalog.lean` — increments and decrements kept as per-replica
grow-only counters, merged by per-key max, observed through `net`. This is not a
strawman: it is the textbook state-based CRDT, its merge is the semilattice
join, and (§2.2) every merge of it is RA-linearizable. `Catalog.lean` already
proved that `net ≥ 0` is not I-confluent. Putting the two facts in one theorem
is the point of this file. -/

/-- Increment or decrement. -/
inductive Kind
  | inc
  | dec
  deriving DecidableEq, Repr

/-- An operation *event*: what, by whom, when. The paper's `(t, r, o)` triple —
`do`'s timestamp and replica arguments live here. -/
structure CtrOp where
  /-- Increment or decrement. -/
  kind : Kind
  /-- Which replica issued it. Two replicas, so `Bool`. -/
  replica : Bool
  /-- A distinct timestamp per event. -/
  ts : Nat
  deriving DecidableEq, Repr

/-- Credit one replica's increment counter. -/
def bumpP (c : PNCounter Bool) (r : Bool) : PNCounter Bool :=
  (fun b => if b = r then c.1 b + 1 else c.1 b, c.2)

/-- Credit one replica's decrement counter. -/
def bumpN (c : PNCounter Bool) (r : Bool) : PNCounter Bool :=
  (c.1, fun b => if b = r then c.2 b + 1 else c.2 b)

/-- The counter's `do`: an operation touches only its own replica's slot, which
is exactly the discipline that makes the max-merge correct. -/
def pnDo (c : PNCounter Bool) (o : CtrOp) : PNCounter Bool :=
  match o.kind with
  | .inc => bumpP c o.replica
  | .dec => bumpN c o.replica

/-- The PN-counter as an RDT. `merge3` ignores the LCA and returns the
semilattice join — the state-based CRDT case — so this really is `Catalog`'s
`MergeState (PNCounter Bool)` and not a second merge that happens to agree.
`rc = ∅`: increments and decrements never conflict. -/
def pnRDT : RDT (PNCounter Bool) CtrOp where
  doOp := pnDo
  merge3 _ x y := x ⊔ y
  rcBefore _ _ := false

/-- The merge really is the library's join, definitionally. -/
theorem pnRDT_merge_is_join (lca x y : PNCounter Bool) :
    pnRDT.merge3 lca x y = x ⊔ y := rfl

/-- The non-negative balance invariant. Bailis's motivating example, and this
library's: `Catalog.pncounter_nonneg_not_iconfluent`. -/
def NonNeg (c : PNCounter Bool) : Prop := 0 ≤ net c

instance (c : PNCounter Bool) : Decidable (NonNeg c) := by unfold NonNeg; infer_instance

/-! ### §2.1 What a run of the counter does

Every operation adds one to one slot, so a run is the fork point plus a vector
of counts. Everything in §2.2 is arithmetic on top of this. -/

/-- How many operations of kind `k` by replica `r` a branch contains. -/
def cnt (k : Kind) (r : Bool) : List CtrOp → Nat
  | [] => 0
  | o :: l => (if o.kind = k ∧ o.replica = r then 1 else 0) + cnt k r l

/-- A branch issued entirely by the *other* replica contributes nothing to this
replica's slots. This is the only place the replica-ownership discipline is
used, and it is where it is indispensable. -/
theorem cnt_eq_zero {k : Kind} {r : Bool} {l : List CtrOp}
    (h : ∀ o ∈ l, o.replica ≠ r) : cnt k r l = 0 := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    have ho : o.replica ≠ r := h o (by simp)
    have hrest : cnt k r l = 0 := ih fun x hx => h x (by simp [hx])
    rw [cnt, if_neg (fun hc => ho hc.2), hrest]

/-- Pointwise state equality, without `funext` noise at every use site. -/
theorem pn_ext {x y : PNCounter Bool} (h1 : ∀ b, x.1 b = y.1 b) (h2 : ∀ b, x.2 b = y.2 b) :
    x = y := by
  cases x; cases y
  simp only [Prod.mk.injEq]
  exact ⟨funext h1, funext h2⟩

/-- **A run is the fork point plus a count vector** — increments. -/
theorem pn_run_inc (c : PNCounter Bool) (l : List CtrOp) (b : Bool) :
    (runFrom pnRDT c l).1 b = c.1 b + cnt .inc b l := by
  induction l generalizing c with
  | nil => simp [cnt]
  | cons o l ih =>
    rw [runFrom_cons, ih]
    show (pnDo c o).1 b + cnt Kind.inc b l = c.1 b + cnt Kind.inc b (o :: l)
    cases hk : o.kind <;> cases b <;> cases hr : o.replica <;>
      simp [pnDo, bumpP, bumpN, cnt, hk, hr] <;> omega

/-- **A run is the fork point plus a count vector** — decrements. -/
theorem pn_run_dec (c : PNCounter Bool) (l : List CtrOp) (b : Bool) :
    (runFrom pnRDT c l).2 b = c.2 b + cnt .dec b l := by
  induction l generalizing c with
  | nil => simp [cnt]
  | cons o l ih =>
    rw [runFrom_cons, ih]
    show (pnDo c o).2 b + cnt Kind.dec b l = c.2 b + cnt Kind.dec b (o :: l)
    cases hk : o.kind <;> cases b <;> cases hr : o.replica <;>
      simp [pnDo, bumpP, bumpN, cnt, hk, hr] <;> omega

/-! ### §2.2 The counter's merge is RA-linearizable -/

/-- The discipline a state-based counter runs on: each replica's operations
touch that replica's slots. Violate it and the max-merge silently loses updates
(`pn_shared_slot_not_ra_linearizable`) — which is exactly the bug class Sal's
counterexample generator exists to catch. -/
def ReplicaOwned (opsL opsR : List CtrOp) : Prop :=
  (∀ o ∈ opsL, o.replica = true) ∧ (∀ o ∈ opsR, o.replica = false)

/-- **Every replica-owned merge of the PN-counter is RA-linearizable**, from any
fork point, for any two branches of any length. The witness is "left branch,
then right branch": max-of-disjoint-slots is exactly sequential application,
because each branch leaves the other's slots alone.

∀-general in the fork point and both branches. No `decide`, no fixed sizes. -/
theorem pn_ra_linearizable (c : PNCounter Bool) {opsL opsR : List CtrOp}
    (h : ReplicaOwned opsL opsR) : RALinearizable pnRDT c opsL opsR := by
  obtain ⟨hL, hR⟩ := h
  refine ⟨opsL ++ opsR, append_mem_interleavings _ _, ?_, ?_⟩
  · simp [rcOK, pnRDT]
  · show runFrom pnRDT c (opsL ++ opsR) = _
    rw [runFrom_append]
    refine pn_ext (fun b => ?_) (fun b => ?_)
    · show (runFrom pnRDT (runFrom pnRDT c opsL) opsR).1 b
        = Nat.max ((runFrom pnRDT c opsL).1 b) ((runFrom pnRDT c opsR).1 b)
      simp only [pn_run_inc, nat_max_def]
      cases b
      · rw [cnt_eq_zero (k := Kind.inc) (r := false) (l := opsL) fun o ho => by simp [hL o ho]]
        split <;> omega
      · rw [cnt_eq_zero (k := Kind.inc) (r := true) (l := opsR) fun o ho => by simp [hR o ho]]
        split <;> omega
    · show (runFrom pnRDT (runFrom pnRDT c opsL) opsR).2 b
        = Nat.max ((runFrom pnRDT c opsL).2 b) ((runFrom pnRDT c opsR).2 b)
      simp only [pn_run_dec, nat_max_def]
      cases b
      · rw [cnt_eq_zero (k := Kind.dec) (r := false) (l := opsL) fun o ho => by simp [hL o ho]]
        split <;> omega
      · rw [cnt_eq_zero (k := Kind.dec) (r := true) (l := opsR) fun o ho => by simp [hR o ho]]
        split <;> omega

/-! ### §2.3 The story, and the headline -/

/-- The fork point: one credit on replica `true`'s books. `net = 1`. -/
def lcaStory : PNCounter Bool := (fun b => if b then 1 else 0, fun _ => 0)

/-- Replica `true` spends the credit. -/
def spendT : CtrOp := ⟨.dec, true, 1⟩

/-- Replica `false`, concurrently, spends the same credit. -/
def spendF : CtrOp := ⟨.dec, false, 2⟩

/-- The left branch: one spend, by the replica that owns the left slots. -/
def branchL : List CtrOp := [spendT]

/-- The right branch: one spend, by the other replica. -/
def branchR : List CtrOp := [spendF]

theorem story_replicaOwned : ReplicaOwned branchL branchR := by
  constructor <;> intro o ho <;> simp [branchL, branchR, spendT, spendF] at ho <;> simp [ho]

/-- ⚠ **THE HEADLINE. An RA-linearizable merge that breaks the application.**

Five facts about one two-phone story, each proved:

1. the merged state **is** explicable as a sequential execution of the two
   spends — `[spendT, spendF]` run from the fork point *is* the merged state,
   to the last bit;
2. and that is no fluke of this witness: **every** replica-owned merge of this
   counter, from any fork point, at any length, is RA-linearizable;
3. each replica was legal at **every step it took**, not merely at its
   endpoint — `SafeRun` checks the whole run;
4. the merged state is illegal: `net = -1`, one credit spent twice;
5. and that is not an artifact of the witness pair either — `net ≥ 0` is not
   I-confluent at all, so no choice of states escapes it.

The modal step — "therefore *no* coordination-free convergent implementation
exists" — is Bailis's Theorem 3.1, cited here and modeled in-repo as
`Uwueave.Necessity.necessity`, whose hypothesis is a **reachable** clash. The
clash in (3)+(4) is reachable by construction: both states are runs from one
fork point, which is what "two phones and one credit" means. Discharging
`Necessity.ReachableClash` from this exhibit is undone and doable — it needs
this file to import `Necessity` and present the two runs as its `Impl` steps;
nothing here claims it has been done.

Read (1)+(4) together: the sequential execution that explains the merge is a
sequential execution that overdraws the account. The linearization is not a
fiction the checker was tricked into accepting — it is real, and it is the
problem. RA-linearizability asks whether the merge is a legal *execution*; it
never asks whether the execution is one the application would have permitted.
`do` has no preconditions, so nothing in the data type's specification knows
that spending below zero was forbidden.

Sal would verify this counter and be right to — the PN-counter CRDT is in its
evaluation suite (Table 2), at 16 VCs discharged by `grind`, 2 by SMT and 6 by
interactive proof. Nothing in that column is wrong. -/
theorem ra_linearizable_but_unsafe :
    RALinearizable pnRDT lcaStory branchL branchR
  ∧ (∀ c opsL opsR, ReplicaOwned opsL opsR → RALinearizable pnRDT c opsL opsR)
  ∧ SafeRun pnRDT NonNeg lcaStory branchL
  ∧ SafeRun pnRDT NonNeg lcaStory branchR
  ∧ ¬ NonNeg (pnRDT.merge3 lcaStory (runFrom pnRDT lcaStory branchL)
        (runFrom pnRDT lcaStory branchR))
  ∧ ¬ IConfluent (S := PNCounter Bool) NonNeg := by
  refine ⟨pn_ra_linearizable _ story_replicaOwned,
          fun c _ _ h => pn_ra_linearizable c h,
          ?_, ?_, by decide, Catalog.pncounter_nonneg_not_iconfluent⟩
  · show NonNeg lcaStory ∧ NonNeg (pnDo lcaStory spendT)
    exact ⟨by decide, by decide⟩
  · show NonNeg lcaStory ∧ NonNeg (pnDo lcaStory spendF)
    exact ⟨by decide, by decide⟩

/-- The explicit sequential explanation, spelled out so the story is readable
without unfolding anything: run both spends from the fork point in that order
and you land on the merged state exactly. -/
theorem story_linearization :
    runFrom pnRDT lcaStory [spendT, spendF]
      = pnRDT.merge3 lcaStory (runFrom pnRDT lcaStory branchL)
          (runFrom pnRDT lcaStory branchR) := by
  refine pn_ext (fun b => ?_) (fun b => ?_) <;> cases b <;> rfl

/-! ## §3. `rc` is load-bearing: the add-wins OR-Set

The paper's OR-Set MRDT, verbatim (§2 of Sal): states are sets of `(element,
tag)` pairs, `merge(σ_lca, σ₁, σ₂) = (σ_lca ∩ σ₁ ∩ σ₂) ∪ (σ₁ ∖ σ_lca) ∪
(σ₂ ∖ σ_lca)`, and `rc = {(rem_e, add_e)}` — remove ordered before add, "hence
adds win over concurrent removes".

This section exists to show the `rc` component of the model is doing work rather
than sitting inert (both counter RDTs have `rc = ∅`). Of the two interleavings
of a concurrent add and remove, exactly one respects `rc`, and it is exactly the
one that explains the merge. Add-wins, read as a linearization condition, *is*
that ordering constraint. -/

/-- OR-Set state: the observed `(element, tag)` pairs — the paper's `P(T × E)`,
as a `GSet`. -/
abbrev Tagged := GSet (Nat × Nat)

/-- The paper's OR-Set operations, with the add's timestamp as its tag. -/
inductive OrOp
  | add (e t : Nat)
  | rem (e : Nat)
  deriving DecidableEq, Repr

/-- `do`: an add observes one tagged pair; a remove drops every pair of that
element this replica has observed. -/
def orDo (s : Tagged) (o : OrOp) : Tagged :=
  match o with
  | .add e t => fun p => s p || (p == (e, t))
  | .rem e => fun p => s p && !(p.1 == e)

/-- The paper's three-way merge: pairs surviving in all three versions, plus
everything either branch added since the LCA. -/
def orMerge3 (lca s₁ s₂ : Tagged) : Tagged :=
  fun p => (lca p && s₁ p && s₂ p) || (s₁ p && !lca p) || (s₂ p && !lca p)

/-- The add-wins OR-Set. Note this one genuinely uses the LCA: it is an MRDT
merge, not a join. -/
def orRDT : RDT Tagged OrOp where
  doOp := orDo
  merge3 := orMerge3
  rcBefore o o' :=
    match o, o' with
    | .rem e, .add e' _ => e == e'
    | _, _ => false

/-- The empty fork point. -/
def orEmpty : Tagged := fun _ => false

/-- An add of element `0` under tag `1`. -/
def addA : OrOp := .add 0 1

/-- A concurrent remove of element `0`. -/
def remA : OrOp := .rem 0

/-- **`rc` picks the linearization, and it picks the right one.** With the left
replica adding `0` and the right replica concurrently removing it:

  * `[remA, addA]` respects `rc` **and** explains the merge — the element is
    present afterwards, which is what add-wins promises;
  * `[addA, remA]` does neither: it fails the `rc` obligation, and running it
    lands on the empty set while the merge holds `(0,1)`.

So the merge is RA-linearizable, and the conflict policy is not decoration: it
is the reason the *surviving* order is the one the merge implements. -/
theorem orset_rc_selects_the_linearization :
    RALinearizable orRDT orEmpty [addA] [remA]
  ∧ Linearizes orRDT orEmpty [addA] [remA] [remA, addA]
  ∧ rcOK orRDT [addA] [remA] [addA, remA] = false
  ∧ ¬ Explains orRDT orEmpty [addA] [remA] [addA, remA] := by
  have hlin : Linearizes orRDT orEmpty [addA] [remA] [remA, addA] := by
    refine ⟨by decide, ?_⟩
    show runFrom orRDT orEmpty [remA, addA] = _
    funext p
    simp [runFrom, orRDT, orDo, orMerge3, orEmpty, addA, remA]
  refine ⟨⟨[remA, addA], by decide, hlin⟩, hlin, by decide, ?_⟩
  intro h
  have h' := congrFun h (0, 1)
  simp [runFrom, orRDT, orDo, orMerge3, orEmpty, addA, remA] at h'

/-! ## §4. The converse: a broken counter that no invariant can catch

The other direction, and it is not a curiosity. Take the counter every
distributed-systems course opens with as the *wrong* one: replicate a single
number and merge by `max`. Concurrent increments annihilate — the merge is not
RA-linearizable, and this is precisely the bug Sal's Plausible-driven
counterexample generation is built to surface.

Now ask this library's question about it. `Nat` under `max` is a *selection*
lattice: the merge always returns one of its two arguments, so by
`Catalog.selection_iconfluent`, **every invariant over it is I-confluent** —
including the ceiling shapes that escalate over every structure which actually
combines what its replicas did (`Catalog.pncounter_nonneg_not_iconfluent`; the
general statement is `Uwueave.Ceiling.uniqueness_ceiling`).

The data type is wrong. Because it is wrong — because it throws updates away —
no application invariant can ever be broken by one of its merges. Safety bought
by data loss is still safety, and that is the shape of the whole converse. -/

/-- An increment event, distinguished only by when it happened. -/
structure IncOp where
  /-- A distinct timestamp per event. -/
  ts : Nat
  deriving DecidableEq, Repr

/-- The naive replicated counter: one number, merged by `max`. -/
def maxRDT : RDT Nat IncOp where
  doOp s _ := s + 1
  merge3 _ x y := Nat.max x y
  rcBefore _ _ := false

/-- Its merge is the library's `Nat`-max join, definitionally — so the
`IConfluent` verdict below is a verdict about *this* merge. -/
theorem maxRDT_merge_is_join (lca x y : Nat) : maxRDT.merge3 lca x y = x ⊔ y := rfl

/-- `max` returns one of its arguments. -/
theorem maxctr_selects (x y : Nat) : x ⊔ y = x ∨ x ⊔ y = y := by
  show Nat.max x y = x ∨ Nat.max x y = y
  rw [nat_max_def]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Every invariant over the broken counter is I-confluent** — every ceiling,
every bound, every mutual exclusion, including `net ≥ 0`'s shape, which
`Catalog.pncounter_nonneg_not_iconfluent` refutes over the counter that keeps
what it is told. This one never has to escalate because it never has to
combine: its merge discards one side, so the merged state is a state some
replica legally held already. -/
theorem maxctr_every_invariant_iconfluent (I : Invariant Nat) : IConfluent I :=
  selection_iconfluent maxctr_selects I

/-- ⚠ **And its merge is not RA-linearizable.** Two replicas each increment
once from `0`; every interleaving of the two increments reaches `2`; the merge
reaches `max 1 1 = 1`. An update was lost, so no sequential execution of the
concurrent updates explains the result. -/
theorem maxctr_not_ra_linearizable : ¬ RALinearizable maxRDT 0 [⟨1⟩] [⟨2⟩] := by
  decide

/-- ⚠ **The PN-counter fails the same way when the replica discipline is
broken**: two branches incrementing the *same* slot. The max-merge keeps one of
the two increments and the other is gone. This is the same lost-update defect as
`maxctr_not_ra_linearizable`, now on the type that §2 proved correct — which is
the point: RA-linearizability is a property of the *merge against the
executions*, not a badge the type wears. -/
theorem pn_shared_slot_not_ra_linearizable :
    ¬ RALinearizable pnRDT lcaStory [⟨.inc, true, 1⟩] [⟨.inc, true, 2⟩] := by
  intro ⟨l, hmem, _, heq⟩
  have hl : l = [⟨.inc, true, 1⟩, ⟨.inc, true, 2⟩] ∨ l = [⟨.inc, true, 2⟩, ⟨.inc, true, 1⟩] := by
    simpa [interleavings, mergeWith] using hmem
  have hbad := congrFun (congrArg Prod.fst heq) true
  rcases hl with rfl | rfl <;> exact absurd hbad (by decide)

/-- **The model is satisfiable and refutable.** A condition that nothing can
fail is not a condition; a condition nothing can satisfy is not one either. Both
halves are exhibited, on the *same* data type, so neither is an artifact of a
type chosen to make its side easy. -/
theorem ra_model_is_falsifiable :
    RALinearizable pnRDT lcaStory branchL branchR
  ∧ ¬ RALinearizable pnRDT lcaStory [⟨.inc, true, 1⟩] [⟨.inc, true, 2⟩] :=
  ⟨pn_ra_linearizable _ story_replicaOwned, pn_shared_slot_not_ra_linearizable⟩

/-! ## §5. Independence: all four quadrants inhabited -/

/-- A grow-only lower bound: replica `true` has credited at least once. Same
fact as `Catalog.gcounter_lowerBound_iconfluent`, restated on the increment
component of the pair — two lines is cheaper than a product lift for one
field. -/
def CreditedOnce (c : PNCounter Bool) : Prop := 1 ≤ c.1 true

theorem creditedOnce_iconfluent : IConfluent (S := PNCounter Bool) CreditedOnce := by
  intro x y hx _
  show 1 ≤ Nat.max (x.1 true) (y.1 true)
  exact Nat.le_trans hx (Nat.le_max_left _ _)

/-- **The two conditions are independent.** Four cells, four proofs:

| | I-confluent | not I-confluent |
|---|---|---|
| **RA-linearizable** | PN-counter, `CreditedOnce` | PN-counter, `net ≥ 0` ⚠ |
| **not RA-linearizable** | max-counter, *every* invariant | PN-counter shared-slot, `net ≥ 0` |

The diagonal is the interesting part. Top-right is `ra_linearizable_but_unsafe`:
Sal's checker passes, your users lose money. Bottom-left is the max-counter:
Sal's checker fails, and no application invariant is at risk from a merge
because the merge discards rather than combines. Neither verdict predicts the
other; a tool that reports one of them has reported one of them.

Note what makes the top row honest: it is the **same data type and the same
merge**, differing only in the invariant. RA-linearizability cannot distinguish
those two rows *in principle* — it is not a statement about the invariant, and
the invariant is not mentioned in it. -/
theorem quadrants :
    (RALinearizable pnRDT lcaStory branchL branchR
      ∧ IConfluent (S := PNCounter Bool) CreditedOnce)
  ∧ (RALinearizable pnRDT lcaStory branchL branchR
      ∧ ¬ IConfluent (S := PNCounter Bool) NonNeg)
  ∧ (¬ RALinearizable maxRDT 0 [⟨1⟩] [⟨2⟩]
      ∧ ∀ I : Invariant Nat, IConfluent I)
  ∧ (¬ RALinearizable pnRDT lcaStory [⟨.inc, true, 1⟩] [⟨.inc, true, 2⟩]
      ∧ ¬ IConfluent (S := PNCounter Bool) NonNeg) :=
  ⟨⟨pn_ra_linearizable _ story_replicaOwned, creditedOnce_iconfluent⟩,
   ⟨pn_ra_linearizable _ story_replicaOwned, Catalog.pncounter_nonneg_not_iconfluent⟩,
   ⟨maxctr_not_ra_linearizable, maxctr_every_invariant_iconfluent⟩,
   ⟨pn_shared_slot_not_ra_linearizable, Catalog.pncounter_nonneg_not_iconfluent⟩⟩

/-! ## §6. Entanglement: guarding the operation moves the bug

Independent is not the same as unrelated. Here is the relation, and it is the
most practically useful thing in the file.

Confronted with §2, the obvious repair is to make the replica refuse: don't
apply a decrement that would take the balance below zero. That makes `net ≥ 0`
an *inductive* invariant of the sequential type — true at the start, preserved
by every operation, with no precondition left over. Which, by
`ra_lin_preserves_inductive_invariants`, has a consequence the repair did not
intend. -/

/-- The guarded `do`: a decrement below zero is refused. Note that the guard
reads only local state — this is still a coordination-free implementation, and
the refusal is exactly what a real bounded counter does. -/
def guardedDo (c : PNCounter Bool) (o : CtrOp) : PNCounter Bool :=
  match o.kind with
  | .inc => bumpP c o.replica
  | .dec => if 0 < net c then bumpN c o.replica else c

/-- The guarded counter: same state, same merge, refusing `do`. -/
def guardedRDT : RDT (PNCounter Bool) CtrOp where
  doOp := guardedDo
  merge3 _ x y := x ⊔ y
  rcBefore _ _ := false

theorem net_bumpP (c : PNCounter Bool) (r : Bool) : net (bumpP c r) = net c + 1 := by
  cases r <;> simp [net, bumpP] <;> omega

theorem net_bumpN (c : PNCounter Bool) (r : Bool) : net (bumpN c r) = net c - 1 := by
  cases r <;> simp [net, bumpN] <;> omega

/-- **The guard makes the invariant inductive**: every operation of the guarded
counter preserves `net ≥ 0`, unconditionally, from any state. -/
theorem guarded_nonneg_step (c : PNCounter Bool) (o : CtrOp) (h : NonNeg c) :
    NonNeg (guardedDo c o) := by
  unfold NonNeg at h ⊢
  unfold guardedDo
  cases hk : o.kind
  · show 0 ≤ net (bumpP c o.replica)
    rw [net_bumpP]
    omega
  · show 0 ≤ net (if 0 < net c then bumpN c o.replica else c)
    split
    · rw [net_bumpN]; omega
    · exact h

/-- ⚠ **And so the guarded counter's merge is no longer RA-linearizable.**

Neither replica refused anything — each had a positive balance when it spent —
so both branches run exactly as before, the merge is **the same function** (third
conjunct, by `rfl`), and the merged state is the same overdrawn state: `net =
-1`. But `net ≥ 0` is now an inductive invariant of the sequential type, and
`ra_lin_preserves_inductive_invariants` says an RA-linearizable merge cannot
leave one of those false. So this merge has no sequential explanation — and the
proof below never enumerates an interleaving, it is the bridge theorem run
backwards.

**The defect did not go away when we guarded, and the two checkers did not move
together.** In `quadrants` terms, the guard walked the system from the top-right
cell to the bottom-right one:

  * I-confluence's verdict is **unchanged**, and could not have changed: same
    merge, same invariant, same refutation (second conjunct, `Catalog`'s theorem
    verbatim). It was reporting the overdraft before the guard and it reports it
    after.
  * RA-linearizability's verdict **flipped**, on a merge that did not change, in
    response to a *precondition on an operation*. That is not a criticism of the
    condition — it is what it means for a merge to be explicable as a sequential
    execution *of that type's operations*, and narrowing the operations narrows
    the explanations. It is a warning about reading its verdict as a property of
    the merge alone.

Same overdraft, same two phones. Guarded, a Sal-shaped tool reports a failing VC
and hands you a counterexample trace; unguarded, it reports nothing and is
right. In neither case is the money safe, and in only one of them does the
data-type checker say so.

Which is the synthesis: Sal's stack answers the question this library does not
ask, this library answers the question Sal does not ask, and a bounded resource
under concurrent spend is *always* somebody's bug — you do not get to choose
whether, only which checker finds it. -/
theorem guarding_moves_the_bug :
    ¬ RALinearizable guardedRDT lcaStory branchL branchR
  ∧ ¬ IConfluent (S := PNCounter Bool) NonNeg
  ∧ (∀ lca x y : PNCounter Bool, guardedRDT.merge3 lca x y = pnRDT.merge3 lca x y) := by
  refine ⟨?_, Catalog.pncounter_nonneg_not_iconfluent, fun _ _ _ => rfl⟩
  intro h
  have hmerge :=
    ra_lin_preserves_inductive_invariants (I := NonNeg) guarded_nonneg_step (by decide) h
  exact absurd hmerge (by decide)

end Uwueave.RALin
