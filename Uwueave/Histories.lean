/-
# Uwueave.Histories — merging more than once.

## Why this file exists

`Ancestral.lean` asks whether a lowest common ancestor buys invariant safety and
answers it — but for **one fork and one join**. codex's second review flagged
that we had been quoting `Ancestral.clash_dichotomy` past that scope: it is
proved for *a supplied common ancestor, one operation per branch, one
fork-and-join*, and it establishes nothing about repeated merging, merge-base
selection, criss-cross histories, or convergence over a version DAG.
`Ancestral.lean`'s own §"Honest scope" and `MergeModel.lean`'s last ⟨UNDONE⟩ say
the same thing in the other direction ("Repeated/criss-cross merging needs Kaki
et al.'s further conditions and gets no verdict here"). The flag was right. This
file is the frontier it named.

## The four verdicts, up front

  * **A version DAG, and base selection is honestly three-valued** (§1–§3). The
    minidregg shape, simplified: a strictly increasing `rank` along parent edges
    makes `Ancestry` acyclic and `Reaches` antisymmetric by construction.
    `lowestCommonBase_unique` and `ambiguous_excludes_lowest` are proved, so
    `ambiguous` is a *theorem-backed* third case: two distinct maximal common
    bases **refute** the existence of a lowest one.

  * ⚠ **Repeated merge: `AncestralConfluent` does NOT survive it** (§5). The
    witness is the literature's own object — Sal §2's counter MRDT
    (`Ancestral.counterAM`) under `spendOps 2`, with the ceiling `n ≤ 4` read as
    an escrow: a shared budget of 4, two units per replica.
    `counter_ceiling4_ancestral` proves the one-fork-one-join judgement **holds**
    (and `counter_ceiling3_not_ancestral` that four is the tight ceiling, so the
    judgement had something to prove). `repeated_merge_breaks_the_invariant` then
    exhibits a coherent history — every merge against a genuine common ancestor
    of its two parents — with a legal root and an **illegal node**. The invariant
    is not repaired by a better merge-base procedure: §6 shows it is broken under
    the *maximal* base too.

  * ⚠ **Criss-cross: it diverges, and the divergence decides the invariant**
    (§6). In the same DAG the two merge nodes have exactly two maximal common
    bases, `left` and `right`, which are distinct and incomparable — so there is
    no LCA (`cc_no_lowest`) and a merge-base procedure must answer *ambiguous*.
    Merging the same pair against the first base yields `5`; against the second,
    `4`. The ceiling is `4`. **Two equally legitimate base choices, one legal
    result and one illegal one, for the same two versions.** This is exactly the
    failure D-0005 declines to rule out, made concrete.

  * **A coherence condition that repairs it, satisfiable and refutable** (§7).
    `MergeClosedFrom M impl ρ` — the merge of states reachable from the root is
    itself reachable from the root — plus `AncestralConfluentFrom` (confluence
    on the *root's* reachable set, not each base's) makes every node of every
    coherent history legal (`Coherent.sound`). The lock of `Ancestral` §5
    **satisfies** it (`lock_mergeClosed`), so its repeated criss-cross merges are
    certified; the counter **refutes** it (`counter_not_mergeClosed`) at exactly
    the step where §5's history goes wrong. The condition is therefore doing the
    work rather than decorating it.

## The one-line diagnosis, which is the real deliverable

`AncestralConfluent M impl I` restricts its two replicas to states **reachable
from the base by local operation runs** (`Ancestral.Reachable`). *A merge result
is not such a state.* One merge and you have left the region the judgement
quantifies over — so a second merge is not "the same theorem applied twice", it
is outside the theorem. That is why the counter is safe once and unsafe twice,
and it is why the repair (§7) is a **closure** condition rather than a stronger
merge law.

That the fault is the closure and not the merge is itself proved, not asserted:
`counter_ancestralConfluentFrom` shows the counter is legal on *every* triple
drawn from the root's reachable set, and `counter_not_mergeClosed` shows that set
is not closed under merging. §5's history does not break because the merge is
wrong somewhere it was asked about — it breaks because the merge produced a state
nothing was ever asked about. The same split reappears at the graph: the lock's
history is `RunRealized` (`lockHistory_runRealized`) and the counter's is not
(`ccHistory_not_runRealized`), which is why §4's bridge to `MergeModel` reaches
the one and not the other.

The same crack shows up as a mismatch between two ancestries that look alike
(§4.3), and both directions are witnessed:

  * `dag_ancestry_is_not_run_reachable` — `left` is a parent of `mergeL` in the
    DAG, and `left`'s state does not op-reach `mergeL`'s;
  * `state_validity_is_not_dag_ancestry` — `MergeModel.BaseDecision.selected 3`
    is `Valid` for the pair `(3, 3)` while **no** common ancestor of those two
    versions carries the state `3`;
  * `dag_absence_does_not_license_unavailable` — a DAG with no common ancestor at
    all does not license `BaseDecision.unavailable`, whose refutation is about
    states.

So `MergeModel.BaseDecision.Valid` is a condition on *states*, and a version DAG
is a structure on *versions*; §4 supplies the bridge (`selected_valid`,
`ambiguous_valid`) and is explicit that it needs `RunRealized`, which
`ccHistory_not_runRealized` shows no merge-bearing history has.

## Prior art next door, cited precisely, imported not at all

`~/dev/minidregg` (sibling Lean repo, same author; uwueave stays self-contained
and depends on none of it):

  * `Theory/CausalVersionAncestry.lean` **built**: `AdmittedParent` (a direct
    edge extracted from an actual append certificate, not a digest coincidence),
    `Ancestry` with `semanticVersion_lt`/`acyclic`, `Reaches` with `antisymm`,
    `CommonAncestor`, `LowestCommonBase` with `selected_unique`,
    `MaximalCommonBase`, `AmbiguousCommonBases.excludes_lowest`, and
    `BaseSelection` as a conservative merge-base procedure's honest output. §1–§2
    here are that shape with the proof-relevance dropped (our `Ancestry` is a
    `Prop`, our edges are a `Bool`-valued relation, our monotone measure is a
    bare `rank` rather than a semantic version carried by a verified event).
  * `Kernel/HyperdocumentMerge.lean` **built**: the three-valued `BaseDecision`
    with `unavailableOfAbsent` making absence a proof obligation, and the honest
    negative `raw_pair_order_observable` — full parent-order commutativity is
    **false** there because the codec commits parent order.
  * `docs/decisions/D-0005`, "Patch and merge claim ceiling", **declined**: it
    reserves *isomorphism, pushout, I-confluence, binding, refinement* for exact
    proved definitions and names two acceptable routes — (1) proved
    residual/commutation/join laws over the canonical operation semantics, or
    (2) a justified contextual-equivalence quotient with congruence — and says
    **neither has been done**. It then says the merge deliberately takes the
    conservative option, that a common base is absent unless ancestry proves it,
    and that base selection may be ambiguous.

This file attempts route (1) over a version DAG and **returns a negative**: the
join law that would be needed does not hold for the MRDT counter, and the
ambiguity D-0005 reserves is not merely a bookkeeping case — it decides an
invariant verdict (§6). The conservative option is vindicated rather than
replaced.

## Exactly how much of `Ancestral.lean`'s scope this generalizes

  * `Ancestral.lean`: one base `l`, two replicas each reachable from `l` by a
    local run, one merge, no version identity.
  * Here: an arbitrary finite version DAG; merges are **nodes**, so a merge
    result can be an input to another merge; bases are selected from the DAG's
    common ancestors, three-valued; the invariant is asked of **every node**.
  * **Not** generalized: the operation model is still `Ancestral.Guarded`/
    `Necessity.Impl` (atomic local transformers, no network), the merge is still
    an `Ancestral.AncestralMerge` with its two laws, and `Serializing` /
    effect-faithfulness plays no role here — §5's counterexample needs no
    hypothesis on the merge beyond the two laws, which is what makes it strong.

## Non-claims

⟨TERMINAL⟩ = a theorem of this model; ⟨UNDONE⟩ = work wearing a caveat's clothes.

  * ⟨TERMINAL⟩ **The negative is a counterexample, not an impossibility.** §5
    exhibits one merge (the counter MRDT) and one history where repeated merging
    escalates. It does **not** say every three-way merge escalates under
    repetition — §7's lock is a proved counter-instance to that reading.
  * ⟨TERMINAL⟩ **`rank` is a hypothesis, not a discovery.** Acyclicity here is
    bought by a strictly increasing measure supplied with the DAG, exactly as
    minidregg buys it from `semanticVersion`. A graph without such a measure is
    not modeled; nothing here *checks* a DAG for acyclicity.
  * ⟨TERMINAL⟩ **Convergence is not proved anywhere in this file.**
    `Coherent.sound` concludes *invariant preservation* and *reachability*, and
    says nothing about two replicas agreeing. §6 and §7.3 are the two witnesses
    that they need not: `base_accident_decides_the_invariant` (results 5 vs 4)
    and `swap_never_converges` (an eternal two-cycle under a state-level base
    policy `MergeModel.BaseDecision.Valid` fully licenses).
  * ⟨UNDONE⟩ **No merge-base *procedure*.** `BaseSelection` is the honest output
    type and all three cases are inhabited, but nothing here computes one from a
    DAG — minidregg does not either ("a concrete bounded search **may** return").
    A procedure would need a decidable reachability, which our `Prop`-valued
    `Ancestry` does not carry.
  * ⟨UNDONE⟩ **`Type 0` only**, matching `MergeModel`'s own ⟨UNDONE⟩: the bridge
    theorems in §4 target `MergeModel.BaseDecision.Valid`, which is fixed at
    `Type`. Universe-polymorphising §1–§3 alone would buy nothing.
  * ⟨UNDONE⟩ **`MergeClosedFrom` is sufficient, not necessary.** §7 proves it
    closes the hole and that it separates the two examples; it does not prove a
    coherent history violating it must break. A necessity direction (the analogue
    of `Necessity.reachable_clash_refutes_cfcs` for iterated merging) is open.
  * ⟨UNDONE⟩ **No delta/patch algebra.** D-0005's route (1) wants residual and
    commutation laws over the operation semantics. This file works with states
    and a merge, as `Ancestral` does; the negative it returns is about that
    setting and does not close the residual question either way.

Literature: Kaki, Priya, Sivaramakrishnan, Jagannathan, "Mergeable Replicated
Data Types", OOPSLA 2019 (the version-store/LCA model whose *repeated* merge is
the subject here); Sal, "Multi-modal Verification of Replicated Data Types",
2026, §2 (the counter MRDT used as the counterexample); Bailis et al.,
"Coordination Avoidance in Database Systems", VLDB 2015 (I-confluence).
-/
import Uwueave.MergeModel

namespace Uwueave.Histories

open Uwueave Uwueave.Ancestral Uwueave.Necessity

/-! ## §0. Two missing lemmas about local runs

`Necessity.run` folds a word of operations; `Ancestral.Reachable` is the
existential over words. Composing two runs needs the fold to split, which
`Necessity` never needed and this file needs everywhere. -/

/-- A successful run splits: reaching `m` by `l₁` and continuing with `l₂` is the
run of the concatenation. -/
theorem run_append {S Op : Type} (impl : Impl S Op) (base m : S) (l₁ l₂ : List Op)
    (h : run impl base l₁ = some m) :
    run impl base (l₁ ++ l₂) = run impl m l₂ := by
  induction l₁ generalizing base with
  | nil =>
    have : base = m := Option.some.inj h
    subst this
    rfl
  | cons op ops ih =>
    match htry : impl.tryApply op base with
    | none =>
      rw [run_cons_none impl base op ops htry] at h
      exact absurd h (by simp)
    | some s' =>
      rw [run_cons_some impl base op ops htry] at h
      show run impl base (op :: (ops ++ l₂)) = run impl m l₂
      rw [run_cons_some impl base op (ops ++ l₂) htry]
      exact ih s' h

/-- **Reachability is transitive** — the composite word is the concatenation. -/
theorem Reachable.trans {S Op : Type} {impl : Impl S Op} {a b c : S}
    (h₁ : Reachable impl a b) (h₂ : Reachable impl b c) : Reachable impl a c := by
  obtain ⟨o₁, r₁⟩ := h₁
  obtain ⟨o₂, r₂⟩ := h₂
  exact ⟨o₁ ++ o₂, by rw [RunsTo, run_append impl a b o₁ o₂ r₁]; exact r₂⟩

/-! ## §1. The version DAG

A node set, a parent relation, and a **strictly increasing measure along edges**.
That measure is where acyclicity comes from — the same trick minidregg's
`Ancestry.semanticVersion_lt` plays with a verified event's semantic version,
with the proof-relevant certificate machinery dropped. It is a *hypothesis*
about the DAG, not a check performed on it. -/

/-- **A version DAG.** `parent p c` is a direct edge; `rank` strictly increases
along every edge, which is the entire content of "this graph is acyclic". -/
structure VersionDag (V : Type) where
  /-- Direct-parent edges. -/
  parent : V → V → Bool
  /-- A measure that strictly increases along every edge. -/
  rank : V → Nat
  /-- The measure's obligation. -/
  rank_lt : ∀ p c, parent p c = true → rank p < rank c

/-- **Strict ancestry**: a nonempty path of direct-parent edges. -/
inductive Ancestry {V : Type} (D : VersionDag V) : V → V → Prop where
  /-- One edge. -/
  | direct {p c : V} : D.parent p c = true → Ancestry D p c
  /-- One more edge on the end of a path. -/
  | extend {a p c : V} : Ancestry D a p → D.parent p c = true → Ancestry D a c

/-- Rank strictly increases along every ancestry path. -/
theorem Ancestry.rank_lt {V : Type} {D : VersionDag V} {a b : V}
    (h : Ancestry D a b) : D.rank a < D.rank b := by
  induction h with
  | direct e => exact D.rank_lt _ _ e
  | extend _ e ih => exact Nat.lt_trans ih (D.rank_lt _ _ e)

/-- Ancestry paths compose. -/
theorem Ancestry.trans {V : Type} {D : VersionDag V} {a b c : V}
    (h₁ : Ancestry D a b) (h₂ : Ancestry D b c) : Ancestry D a c := by
  induction h₂ with
  | direct e => exact .extend h₁ e
  | extend _ e ih => exact .extend ih e

/-- **No version is its own strict ancestor.** -/
theorem Ancestry.irrefl {V : Type} {D : VersionDag V} (a : V) :
    ¬ Ancestry D a a := fun h => Nat.lt_irrefl _ h.rank_lt

/-- **The DAG is acyclic**: two opposed ancestry paths are impossible. -/
theorem Ancestry.acyclic {V : Type} {D : VersionDag V} {a b : V}
    (h₁ : Ancestry D a b) (h₂ : Ancestry D b a) : False :=
  Nat.lt_irrefl _ (Nat.lt_trans h₁.rank_lt h₂.rank_lt)

/-- **Reflexive reachability**: identity, or a strict ancestry path. -/
def Reaches {V : Type} (D : VersionDag V) (a b : V) : Prop := a = b ∨ Ancestry D a b

/-- Every version reaches itself. -/
theorem Reaches.refl {V : Type} (D : VersionDag V) (a : V) : Reaches D a a := Or.inl rfl

/-- A reachability step is either identity or a strict rank increase — the
working form of every negative fact about a concrete DAG below. -/
theorem Reaches.eq_or_rank_lt {V : Type} {D : VersionDag V} {a b : V}
    (h : Reaches D a b) : a = b ∨ D.rank a < D.rank b := by
  rcases h with rfl | ha
  · exact Or.inl rfl
  · exact Or.inr ha.rank_lt

/-- Reachability never decreases rank. -/
theorem Reaches.rank_le {V : Type} {D : VersionDag V} {a b : V}
    (h : Reaches D a b) : D.rank a ≤ D.rank b := by
  rcases h.eq_or_rank_lt with rfl | hr
  · exact Nat.le_refl _
  · exact Nat.le_of_lt hr

/-- Reachability composes. -/
theorem Reaches.trans {V : Type} {D : VersionDag V} {a b c : V}
    (h₁ : Reaches D a b) (h₂ : Reaches D b c) : Reaches D a c := by
  rcases h₁ with rfl | ha
  · exact h₂
  · rcases h₂ with rfl | hb
    · exact Or.inr ha
    · exact Or.inr (ha.trans hb)

/-- **Reachability is antisymmetric** — minidregg's `Reaches.antisymm`, bought
from the same monotone measure. -/
theorem Reaches.antisymm {V : Type} {D : VersionDag V} {a b : V}
    (h₁ : Reaches D a b) (h₂ : Reaches D b a) : a = b := by
  rcases h₁.eq_or_rank_lt with heq | hlt
  · exact heq
  · rcases h₂.eq_or_rank_lt with heq' | hlt'
    · exact heq'.symm
    · exact absurd (Nat.lt_trans hlt hlt') (Nat.lt_irrefl _)

/-- **A common ancestor** of two versions: one version reaching both. -/
def CommonAncestor {V : Type} (D : VersionDag V) (x y b : V) : Prop :=
  Reaches D b x ∧ Reaches D b y

/-- Common ancestry does not care which replica is which. -/
theorem CommonAncestor.symm {V : Type} {D : VersionDag V} {x y b : V}
    (h : CommonAncestor D x y b) : CommonAncestor D y x b := ⟨h.2, h.1⟩

/-! ## §2. Base selection, honestly three-valued

The merge-base layer, and the theorem that makes `ambiguous` a real case rather
than an implementation excuse: two distinct maximal common bases **refute** the
existence of a lowest one. -/

/-- **A lowest common base**: a common ancestor that every common ancestor
reaches. Strictly stronger than "some maximal candidate", and therefore need not
exist in a general DAG — §3's criss-cross is the witness. -/
def LowestCommonBase {V : Type} (D : VersionDag V) (x y b : V) : Prop :=
  CommonAncestor D x y b ∧ ∀ c, CommonAncestor D x y c → Reaches D c b

/-- **A maximal common base**: no common ancestor lies strictly beyond it.
Several incomparable ones may exist. -/
def MaximalCommonBase {V : Type} (D : VersionDag V) (x y b : V) : Prop :=
  CommonAncestor D x y b ∧ ∀ c, CommonAncestor D x y c → Reaches D b c → c = b

/-- **Uniqueness when it exists** — minidregg's `LowestCommonBase.selected_unique`,
by antisymmetry of reachability. Two merge-base procedures that both certify a
lowest base agree on the node. -/
theorem lowestCommonBase_unique {V : Type} {D : VersionDag V} {x y b₁ b₂ : V}
    (h₁ : LowestCommonBase D x y b₁) (h₂ : LowestCommonBase D x y b₂) : b₁ = b₂ :=
  Reaches.antisymm (h₂.2 b₁ h₁.1) (h₁.2 b₂ h₂.1)

/-- A lowest common base is in particular maximal. -/
theorem LowestCommonBase.maximal {V : Type} {D : VersionDag V} {x y b : V}
    (h : LowestCommonBase D x y b) : MaximalCommonBase D x y b :=
  ⟨h.1, fun c hc hbc => Reaches.antisymm (h.2 c hc) hbc⟩

/-- ⚠ **Two distinct maximal common bases exclude a lowest one.** This is the
theorem that makes the three-valued answer honest: `ambiguous` is not "we did not
look hard enough", it is a *proof* that no `selected` answer exists. minidregg's
`AmbiguousCommonBases.excludes_lowest`, restated over our DAG. -/
theorem ambiguous_excludes_lowest {V : Type} {D : VersionDag V} {x y b₁ b₂ : V}
    (h₁ : MaximalCommonBase D x y b₁) (h₂ : MaximalCommonBase D x y b₂)
    (hne : b₁ ≠ b₂) : ¬ ∃ b, LowestCommonBase D x y b := by
  rintro ⟨b, hb⟩
  have e₁ : b = b₁ := h₁.2 b hb.1 (hb.2 b₁ h₁.1)
  have e₂ : b = b₂ := h₂.2 b hb.1 (hb.2 b₂ h₂.1)
  exact hne (e₁.symm.trans e₂)

/-- **What a merge-base procedure may honestly return.** Not `Option V`: two
maximal bases is a different answer from none, and §6 shows the difference is
observable in the invariant verdict. Every constructor carries its evidence —
`unavailable` carries a **refutation**, not a flag. -/
inductive BaseSelection {V : Type} (D : VersionDag V) (x y : V) where
  /-- A certified lowest common base. -/
  | selected (b : V) (h : LowestCommonBase D x y b)
  /-- Two distinct maximal common bases; by `ambiguous_excludes_lowest` no lowest
  one exists. -/
  | ambiguous (b₁ b₂ : V) (h₁ : MaximalCommonBase D x y b₁)
      (h₂ : MaximalCommonBase D x y b₂) (hne : b₁ ≠ b₂)
  /-- No common ancestor at all, proved. -/
  | unavailable (h : ∀ b, ¬ CommonAncestor D x y b)

/-- The three answers are mutually exclusive, and the exclusion is a theorem
rather than a convention: a selection cannot be both `selected` and `ambiguous`
(that is `ambiguous_excludes_lowest`), and `unavailable` refutes both. -/
theorem BaseSelection.exclusive {V : Type} {D : VersionDag V} {x y : V} :
    (∀ b₁ b₂, MaximalCommonBase D x y b₁ → MaximalCommonBase D x y b₂ → b₁ ≠ b₂ →
        ¬ ∃ b, LowestCommonBase D x y b)
      ∧ (∀ (_ : ∀ b, ¬ CommonAncestor D x y b) b, ¬ LowestCommonBase D x y b) :=
  ⟨fun _ _ h₁ h₂ hne => ambiguous_excludes_lowest h₁ h₂ hne,
   fun hno b hb => hno b hb.1⟩

/-! ## §3. The criss-cross DAG

The classic shape, and the one this whole file turns on:

```
              root                     rank 0
             /    \
          left    right                rank 1
           | \    / |
           |  \  /  |
           |   \/   |
           |   /\   |
        mergeL    mergeR               rank 2      (two replicas merged the pair)
           | \    / |
      joinLeft   joinRight             rank 3      (…and merged the merges)
```

`mergeL` and `mergeR` are two *versions* of the same reconciliation — what
happens whenever two peers merge the same pair independently, which is ordinary.
Their common ancestors are `root`, `left` and `right`; the maximal ones are
`left` and `right`, incomparable, so **no lowest common base exists**.
`joinLeft` and `joinRight` are the two merges a procedure may then legitimately
perform, one against each maximal base. §5 and §6 read the states off. -/

/-- The seven versions of the criss-cross. -/
inductive Ver where
  /-- The fork point. -/
  | root
  /-- One branch. -/
  | left
  /-- The other branch. -/
  | right
  /-- One replica's merge of `left` and `right`. -/
  | mergeL
  /-- The other replica's merge of the same pair. -/
  | mergeR
  /-- The merge of the merges, against the base `left`. -/
  | joinLeft
  /-- The merge of the merges, against the base `right`. -/
  | joinRight
  deriving DecidableEq, Repr

/-- The criss-cross edges. -/
def ccParent : Ver → Ver → Bool
  | .root, .left => true
  | .root, .right => true
  | .left, .mergeL => true
  | .right, .mergeL => true
  | .left, .mergeR => true
  | .right, .mergeR => true
  | .mergeL, .joinLeft => true
  | .mergeR, .joinLeft => true
  | .mergeL, .joinRight => true
  | .mergeR, .joinRight => true
  | _, _ => false

/-- Depth in the DAG. Note it is *version* depth: `right` has rank 1 and carries
the state `2`, and nothing ties the two numbers together. -/
def ccRank : Ver → Nat
  | .root => 0
  | .left => 1
  | .right => 1
  | .mergeL => 2
  | .mergeR => 2
  | .joinLeft => 3
  | .joinRight => 3

/-- The criss-cross version DAG. -/
def ccDag : VersionDag Ver where
  parent := ccParent
  rank := ccRank
  rank_lt := by intro p c; cases p <;> cases c <;> decide

/-! ### §3.1 The common ancestors, enumerated -/

/-- The common ancestors of the two merge versions are exactly `root`, `left`
and `right`. Every other version fails by rank. -/
theorem cc_commonAncestors (v : Ver) (h : CommonAncestor ccDag .mergeL .mergeR v) :
    v = .root ∨ v = .left ∨ v = .right := by
  cases v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · rcases h.2.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)

/-- `left` is a common ancestor of the two merge versions — it is a direct parent
of both. -/
theorem cc_left_common : CommonAncestor ccDag .mergeL .mergeR .left :=
  ⟨Or.inr (.direct (by decide)), Or.inr (.direct (by decide))⟩

/-- …and so is `right`. -/
theorem cc_right_common : CommonAncestor ccDag .mergeL .mergeR .right :=
  ⟨Or.inr (.direct (by decide)), Or.inr (.direct (by decide))⟩

/-- `left` is **maximal**: no common ancestor of the two merges lies strictly
beyond it. -/
theorem cc_left_maximal : MaximalCommonBase ccDag .mergeL .mergeR .left := by
  refine ⟨cc_left_common, ?_⟩
  intro c hc hreach
  rcases cc_commonAncestors c hc with rfl | rfl | rfl
  · rcases hreach.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rfl
  · rcases hreach.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)

/-- …and so is `right`. -/
theorem cc_right_maximal : MaximalCommonBase ccDag .mergeL .mergeR .right := by
  refine ⟨cc_right_common, ?_⟩
  intro c hc hreach
  rcases cc_commonAncestors c hc with rfl | rfl | rfl
  · rcases hreach.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases hreach.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rfl

/-- ⚠ **The criss-cross has no lowest common base.** Two distinct maximal ones,
so by `ambiguous_excludes_lowest` a merge-base procedure *must* answer
`ambiguous` for this pair — there is no node it could honestly select. -/
theorem cc_no_lowest : ¬ ∃ b, LowestCommonBase ccDag .mergeL .mergeR b :=
  ambiguous_excludes_lowest cc_left_maximal cc_right_maximal (by decide)

/-- The ambiguous answer, as a `BaseSelection` value. -/
def ccAmbiguous : BaseSelection ccDag .mergeL .mergeR :=
  .ambiguous .left .right cc_left_maximal cc_right_maximal (by decide)

/-! ### §3.2 All three answers are inhabited

A case nothing can satisfy is a case a reader trusts for nothing. `ambiguous` is
`ccAmbiguous`; `selected` and `unavailable` are below. -/

/-- The common ancestors of the two *branches* are just the root. -/
theorem cc_branch_commonAncestors (v : Ver) (h : CommonAncestor ccDag .left .right v) :
    v = .root := by
  cases v
  · rfl
  · rcases h.2.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)

/-- **`selected` is inhabited**: the fork point is the lowest common base of the
two branches. -/
theorem cc_root_lowest : LowestCommonBase ccDag .left .right .root := by
  refine ⟨⟨Or.inr (.direct (by decide)), Or.inr (.direct (by decide))⟩, ?_⟩
  intro c hc
  rcases cc_branch_commonAncestors c hc with rfl
  exact Reaches.refl _ _

/-- The selected answer, as a `BaseSelection` value. -/
def ccSelected : BaseSelection ccDag .left .right := .selected .root cc_root_lowest

/-- Two versions with no edges at all. -/
inductive Two where
  /-- One. -/
  | x
  /-- The other. -/
  | y
  deriving DecidableEq, Repr

/-- The edgeless DAG. -/
def twoDag : VersionDag Two where
  parent := fun _ _ => false
  rank := fun _ => 0
  rank_lt := by intro p c; cases p <;> cases c <;> decide

/-- **`unavailable` is inhabited, the hard way** — with a refutation of every
common ancestor rather than a flag. -/
theorem two_no_common : ∀ b, ¬ CommonAncestor twoDag .x .y b := by
  intro b h
  rcases h.1.eq_or_rank_lt with rfl | hr
  · rcases h.2.eq_or_rank_lt with he | hr'
    · exact absurd he (by decide)
    · exact absurd hr' (Nat.lt_irrefl 0)
  · exact absurd hr (Nat.lt_irrefl 0)

/-- The unavailable answer, as a `BaseSelection` value. -/
def twoUnavailable : BaseSelection twoDag .x .y := .unavailable two_no_common

/-! ## §4. Labelled histories: versions carry states, and merges are versions

A version DAG on its own is a graph exercise. What makes it a *merge* question is
the labelling: each version carries a state, and each version's `Origin` says
what produced it — a local run from one parent, or a three-way merge of two
parents against a base that is a common ancestor of both.

`Origin` is the piece `Ancestral.lean` has no room for. Its `AncestralConfluent`
sees a base and two replicas and stops; here a merge result is a node with
children, which is the whole subject. -/

/-- **What a version is.** -/
inductive Origin (V : Type) where
  /-- The history's root. -/
  | root
  /-- Produced by a local run from one parent. -/
  | ran (parent : V)
  /-- Produced by a three-way merge of two parents against a base. -/
  | merged (base left right : V)

/-- **A labelled version history.** -/
structure History (V S Op : Type) where
  /-- The version graph. -/
  dag : VersionDag V
  /-- What each version holds. -/
  state : V → S
  /-- How each version came to be. -/
  origin : V → Origin V
  /-- The distinguished root. -/
  root : V

/-- **The obligation attached to one version's origin.** A `ran` node's state is
op-reachable from its parent's; a `merged` node's parents are its DAG parents,
its base is a genuine common ancestor **of those two parents**, and its state is
literally the three-way merge of the three states.

The root carries no obligation here — `History.Coherent.root_unique` is what
pins it. -/
def OriginOK {V S Op : Type} (H : History V S Op) (M : AncestralMerge S)
    (impl : Impl S Op) (v : V) : Prop :=
  match H.origin v with
  | .root => True
  | .ran p => H.dag.parent p v = true ∧ Reachable impl (H.state p) (H.state v)
  | .merged l x y =>
      H.dag.parent x v = true ∧ H.dag.parent y v = true ∧
        CommonAncestor H.dag x y l ∧
        H.state v = M.merge3 (H.state l) (H.state x) (H.state y)

/-- **A coherent history**: at most one version claims to be a root, and every
version discharges its origin's obligation. This is the generalization of
`Ancestral.AncestralConfluent`'s hypothesis block from one triple to a whole DAG.

Two omissions are deliberate:

  * it never asks that a merged version's state be op-reachable from its base —
    that is §5's whole point, and §7 is where the demand is finally made;
  * it does not demand `H.origin H.root = .root`. `Coherent.sound` does not need
    it, and a hypothesis a theorem does not use makes the theorem weaker for
    nothing. What `sound` needs is the *converse* — that nothing else claims to
    be a root — which is `root_unique`. -/
structure History.Coherent {V S Op : Type} (H : History V S Op) (M : AncestralMerge S)
    (impl : Impl S Op) : Prop where
  /-- Nothing but the root claims to be one. -/
  root_unique : ∀ v, H.origin v = Origin.root → v = H.root
  /-- Every version discharges its origin. -/
  nodes : ∀ v, OriginOK H M impl v

/-! ### §4.1 The bridge to `MergeModel.BaseDecision`

`MergeModel.BaseDecision.Valid` demands `Ancestral.Reachable` between **states**.
A version DAG gives `Reaches` between **versions**. The bridge is
`RunRealized`, and §4.3 is the honest accounting of when it holds. -/

/-- **The history's edges are realized by local runs**: a direct parent's state
op-reaches its child's. -/
def RunRealized {V S Op : Type} (H : History V S Op) (impl : Impl S Op) : Prop :=
  ∀ p c, H.dag.parent p c = true → Reachable impl (H.state p) (H.state c)

/-- Under `RunRealized`, DAG ancestry transports to state reachability. -/
theorem ancestry_reachable {V S Op : Type} {H : History V S Op} {impl : Impl S Op}
    (hrr : RunRealized H impl) {p c : V} (h : Ancestry H.dag p c) :
    Reachable impl (H.state p) (H.state c) := by
  induction h with
  | direct e => exact hrr _ _ e
  | extend _ e ih => exact Reachable.trans ih (hrr _ _ e)

/-- …and so does reflexive reachability. -/
theorem reaches_reachable {V S Op : Type} {H : History V S Op} {impl : Impl S Op}
    (hrr : RunRealized H impl) {p c : V} (h : Reaches H.dag p c) :
    Reachable impl (H.state p) (H.state c) := by
  rcases h with rfl | ha
  · exact Reachable.refl _ _
  · exact ancestry_reachable hrr ha

/-- **A DAG common ancestor licenses `BaseDecision.selected`** — in a
run-realized history. This is the connection that makes §1–§3 more than a graph
exercise: a merge-base procedure's answer becomes the *context* of
`MergeModel`'s decision model, with its validity obligation discharged from
ancestry rather than asserted. -/
theorem selected_valid {V S Op : Type} {H : History V S Op} {impl : Impl S Op}
    (hrr : RunRealized H impl) {x y b : V} (h : CommonAncestor H.dag x y b) :
    (MergeModel.BaseDecision.selected (H.state b)).Valid impl (H.state x) (H.state y) :=
  ⟨reaches_reachable hrr h.1, reaches_reachable hrr h.2⟩

/-- **Two distinct maximal bases license `BaseDecision.ambiguous`** — provided
their *states* differ, which is a genuinely extra hypothesis (§4.2). -/
theorem ambiguous_valid {V S Op : Type} {H : History V S Op} {impl : Impl S Op}
    (hrr : RunRealized H impl) {x y b₁ b₂ : V}
    (h₁ : MaximalCommonBase H.dag x y b₁) (h₂ : MaximalCommonBase H.dag x y b₂)
    (hne : H.state b₁ ≠ H.state b₂) :
    (MergeModel.BaseDecision.ambiguous (H.state b₁) (H.state b₂)).Valid impl
      (H.state x) (H.state y) :=
  ⟨⟨reaches_reachable hrr h₁.1.1, reaches_reachable hrr h₁.1.2⟩,
   ⟨reaches_reachable hrr h₂.1.1, reaches_reachable hrr h₂.1.2⟩, hne⟩

/-! ### §4.2 ⚠ Version-level ambiguity need not be state-level ambiguity

`MergeModel.BaseDecision.ambiguous b₁ b₂` demands `b₁ ≠ b₂` **as states**. Two
distinct maximal common *versions* may carry the same state, in which case the
DAG is ambiguous and the decision type cannot say so. §5's history is exactly
that situation and §6 is the one where the states differ and the ambiguity
becomes load-bearing — the two cases are worth telling apart deliberately. -/

/-- The edgeless DAG, labelled: two unrelated versions holding the same state. -/
def twoHistory {S Op : Type} (s : S) : History Two S Op where
  dag := twoDag
  state := fun _ => s
  origin := fun _ => .root
  root := .x

/-- ⚠ **A DAG with no common ancestor does not license `unavailable`.** One
history, both halves: its version graph has **no** common ancestor of the two
versions, and `BaseDecision.unavailable` is nonetheless **invalid** for the pair
of states they carry — because that obligation is a refutation about *states*,
and a state always op-reaches itself.

So the three-valued decision cannot be computed from the DAG alone, in either
direction: §4.1 transports `selected` and `ambiguous` *into*
`MergeModel.BaseDecision` under `RunRealized`, and nothing transports
`unavailable`. -/
theorem dag_absence_does_not_license_unavailable {S Op : Type} (impl : Impl S Op) (s : S) :
    (∀ b, ¬ CommonAncestor (twoHistory (S := S) (Op := Op) s).dag .x .y b) ∧
      ¬ (MergeModel.BaseDecision.unavailable (S := S)).Valid impl
        ((twoHistory (S := S) (Op := Op) s).state .x)
        ((twoHistory (S := S) (Op := Op) s).state .y) := by
  refine ⟨two_no_common, ?_⟩
  intro h
  exact h ⟨s, Reachable.refl _ _, Reachable.refl _ _⟩

/-! ## §5. Repeated merge — the verdict

The data type is the counter MRDT of Sal §2 (`Ancestral.counterAM`,
`l + (a - l) + (b - l)`), the operation is `Ancestral.spendOps 2` (a replica may
spend two units), and the invariant is the ceiling `n ≤ 4` — read as an escrow:
a shared budget of four, two units per replica.

  * `counter_ceiling4_ancestral`: the escrow **is** ancestrally confluent. One
    fork, two branches, one merge: legal, always.
  * `repeated_merge_breaks_the_invariant`: a coherent history over `ccDag` with
    a legal root has an **illegal node**.

Nothing about the merge is weakened to get there. The counterexample needs no
hypothesis beyond `AncestralMerge`'s two laws, and the merge it uses is the one
the literature supplies. -/

/-- The local commit rule of `spendOps B`, unfolded once. -/
theorem spend_tryApply (B : Nat) (op : Unit) (s : Nat) :
    (spendOps B).impl.tryApply op s = if s + 1 ≤ B then some (s + 1) else none := by
  by_cases h : s + 1 ≤ B
  · rw [if_pos h]
    show (if ((decide (s + 1 ≤ B)) = true) then some (s + 1) else none) = some (s + 1)
    rw [if_pos (decide_eq_true h)]
  · rw [if_neg h]
    show (if ((decide (s + 1 ≤ B)) = true) then some (s + 1) else none) = none
    rw [if_neg (by simp [h])]

/-- **What a replica can reach under budget 2**: itself, or some `x` with
`l ≤ x ≤ 2`. Nothing above the budget is ever locally committed — which is what
makes the escrow's single-merge safety true, and what makes a merge result leave
the reachable region. -/
theorem spend2_run : ∀ (ops : List Unit) (l x : Nat),
    run (spendOps 2).impl l ops = some x → x = l ∨ (l ≤ x ∧ x ≤ 2) := by
  intro ops
  induction ops with
  | nil => intro l x h; exact Or.inl (Option.some.inj h).symm
  | cons op ops ih =>
    intro l x h
    by_cases hl : l + 1 ≤ 2
    · have htry : (spendOps 2).impl.tryApply op l = some (l + 1) := by
        rw [spend_tryApply]; exact if_pos hl
      rw [run_cons_some _ _ _ _ htry] at h
      rcases ih (l + 1) x h with he | ⟨h1, h2⟩
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, h2⟩
    · have htry : (spendOps 2).impl.tryApply op l = none := by
        rw [spend_tryApply]; exact if_neg hl
      rw [run_cons_none _ _ _ _ htry] at h
      exact absurd h (by simp)

/-- The same, in `Reachable` form. -/
theorem spend2_reachable {l x : Nat} (h : Reachable (spendOps 2).impl l x) :
    x = l ∨ (l ≤ x ∧ x ≤ 2) := by
  obtain ⟨ops, hr⟩ := h
  exact spend2_run ops l x hr

/-- One spend from zero. -/
theorem spend2_reach_one : Reachable (spendOps 2).impl 0 1 :=
  ⟨[()], show run (spendOps 2).impl 0 [()] = some 1 from rfl⟩

/-- Two spends from zero. -/
theorem spend2_reach_two : Reachable (spendOps 2).impl 0 2 :=
  ⟨[(), ()], show run (spendOps 2).impl 0 [(), ()] = some 2 from rfl⟩

/-- **The escrow is ancestrally confluent.** For every legal ancestor and every
pair of replicas reachable from it by local spends, the counter MRDT's merge
stays under the ceiling of four. This is `Ancestral`'s judgement, holding.

Read the arithmetic: the two branches together spend at most `2 + 2` above a base
of `0`, and `AncestralMerge`'s laws pin everything else. -/
theorem counter_ceiling4_ancestral :
    AncestralConfluent counterAM (spendOps 2).impl (fun n => n ≤ 4) := by
  intro l x y hl hx hy hrx hry
  have hl' : l ≤ 4 := hl
  have hx' : x ≤ 4 := hx
  have hy' : y ≤ 4 := hy
  have hrx' := spend2_reachable hrx
  have hry' := spend2_reachable hry
  show counterMerge l x y ≤ 4
  unfold counterMerge
  rcases hrx' with h | ⟨h1, h2⟩ <;> rcases hry' with h' | ⟨h1', h2'⟩ <;> omega

/-- ⚠ **…and four is the tight ceiling**, so the judgement above is not a
statement that happens to hold for any bound. At three it is **refuted**: both
replicas spend their two units from the fork point and the merge lands on four.
`Ancestral.ceiling_not_ancestral` is the same clash one budget down; this is the
tooth that says `counter_ceiling4_ancestral` had something to prove. -/
theorem counter_ceiling3_not_ancestral :
    ¬ AncestralConfluent counterAM (spendOps 2).impl (fun n => n ≤ 3) := by
  intro h
  have hm : counterAM.merge3 0 2 2 ≤ 3 :=
    h 0 2 2 (by decide) (by decide) (by decide) spend2_reach_two spend2_reach_two
  rw [show counterAM.merge3 0 2 2 = 4 from by decide] at hm
  exact absurd hm (by decide)

/-! ### §5.1 The history, and the node that breaks

States, read off the DAG of §3:

  * `root` holds `0`; `left` holds `1` (one spend); `right` holds `2` (two
    spends) — both op-reachable from the root, so both branches are ordinary
    local histories;
  * `mergeL` and `mergeR` each hold `counterMerge 0 1 2 = 3`, the *same* merge
    performed by two peers, each against the fork point, each covered by
    `counter_ceiling4_ancestral`;
  * `joinLeft` holds `counterMerge 1 3 3 = 5` and `joinRight` holds
    `counterMerge 2 3 3 = 4` — the two merges a procedure may legitimately
    perform once it reports `ambiguous` (§3.1). -/

/-- The states the criss-cross versions hold. -/
def ccState : Ver → Nat
  | .root => 0
  | .left => 1
  | .right => 2
  | .mergeL => 3
  | .mergeR => 3
  | .joinLeft => 5
  | .joinRight => 4

/-- How each criss-cross version came to be. -/
def ccOrigin : Ver → Origin Ver
  | .root => .root
  | .left => .ran .root
  | .right => .ran .root
  | .mergeL => .merged .root .left .right
  | .mergeR => .merged .root .left .right
  | .joinLeft => .merged .left .mergeL .mergeR
  | .joinRight => .merged .right .mergeL .mergeR

/-- The criss-cross history over the counter MRDT. -/
def ccHistory : History Ver Nat Unit where
  dag := ccDag
  state := ccState
  origin := ccOrigin
  root := .root

/-- Only the root is a root: every other version records a run or a merge. -/
theorem ccOrigin_root_unique (v : Ver) (h : ccOrigin v = Origin.root) : v = .root := by
  cases v <;> simp_all [ccOrigin]

/-- **The history is coherent**: every merge's two parents are its DAG parents,
every base is a genuine common ancestor of those two parents, and every merged
state is literally the counter MRDT's merge of the three. Nothing is fudged to
reach §5.2 — this is the history a well-behaved version store would build. -/
theorem ccHistory_coherent : ccHistory.Coherent counterAM (spendOps 2).impl where
  root_unique := ccOrigin_root_unique
  nodes := by
    intro v
    cases v
    · trivial
    · show ccDag.parent .root .left = true ∧ Reachable (spendOps 2).impl 0 1
      exact ⟨by decide, spend2_reach_one⟩
    · show ccDag.parent .root .right = true ∧ Reachable (spendOps 2).impl 0 2
      exact ⟨by decide, spend2_reach_two⟩
    · show ccDag.parent .left .mergeL = true ∧ ccDag.parent .right .mergeL = true ∧
        CommonAncestor ccDag .left .right .root ∧ (3 : Nat) = counterMerge 0 1 2
      exact ⟨by decide, by decide, cc_root_lowest.1, by decide⟩
    · show ccDag.parent .left .mergeR = true ∧ ccDag.parent .right .mergeR = true ∧
        CommonAncestor ccDag .left .right .root ∧ (3 : Nat) = counterMerge 0 1 2
      exact ⟨by decide, by decide, cc_root_lowest.1, by decide⟩
    · show ccDag.parent .mergeL .joinLeft = true ∧ ccDag.parent .mergeR .joinLeft = true ∧
        CommonAncestor ccDag .mergeL .mergeR .left ∧ (5 : Nat) = counterMerge 1 3 3
      exact ⟨by decide, by decide, cc_left_common, by decide⟩
    · show ccDag.parent .mergeL .joinRight = true ∧ ccDag.parent .mergeR .joinRight = true ∧
        CommonAncestor ccDag .mergeL .mergeR .right ∧ (4 : Nat) = counterMerge 2 3 3
      exact ⟨by decide, by decide, cc_right_common, by decide⟩

/-! ### §5.2 The verdict -/

/-- ⚠ **Ancestral confluence does not survive repeated merging.** The escrow is
ancestrally confluent (`counter_ceiling4_ancestral`); the history is coherent
(`ccHistory_coherent`); the root is legal; and `joinLeft` holds `5`, over a
ceiling of `4`.

The escape route is exact and is the diagnosis this file exists to state:
`AncestralConfluent` quantifies over replicas **reachable from the base by local
runs**, and `mergeL`'s state `3` is not reachable from `left`'s state `1` — the
budget stops at `2` (`dag_ancestry_is_not_run_reachable`). One merge and the
judgement's premises are gone. -/
theorem repeated_merge_breaks_the_invariant :
    AncestralConfluent counterAM (spendOps 2).impl (fun n => n ≤ 4)
      ∧ ccHistory.Coherent counterAM (spendOps 2).impl
      ∧ ccState .root ≤ 4
      ∧ ¬ (ccState .joinLeft ≤ 4) :=
  ⟨counter_ceiling4_ancestral, ccHistory_coherent, by decide, by decide⟩

/-- ⚠ **The DAG's ancestry is not the reachability `AncestralConfluent` speaks
about.** `left` is a direct parent of `mergeL`, and `left`'s state does not
op-reach `mergeL`'s. So `RunRealized` fails, and with it every bridge theorem of
§4.1 for this history. -/
theorem dag_ancestry_is_not_run_reachable :
    ccDag.parent .left .mergeL = true ∧ ¬ Reachable (spendOps 2).impl 1 3 := by
  refine ⟨by decide, ?_⟩
  intro h
  rcases spend2_reachable h with he | ⟨_, h2⟩
  · exact absurd he (by decide)
  · exact absurd h2 (by decide)

/-- …stated of the history: no merge-bearing history whose merges leave the
op-reachable region is `RunRealized`. -/
theorem ccHistory_not_runRealized : ¬ RunRealized ccHistory (spendOps 2).impl := by
  intro h
  exact dag_ancestry_is_not_run_reachable.2 (h .left .mergeL (by decide))

/-- ⚠ **…and in the other direction: state-level validity is not version
ancestry.** `MergeModel.BaseDecision.selected 3` is `Valid` for the pair
`(3, 3)` — reflexively, since a state always op-reaches itself — while **no**
common ancestor of `mergeL` and `mergeR` carries the state `3`. A base decision
validated only at the state level therefore certifies nothing about the
history. -/
theorem state_validity_is_not_dag_ancestry :
    (MergeModel.BaseDecision.selected (3 : Nat)).Valid (spendOps 2).impl 3 3
      ∧ ∀ v, CommonAncestor ccDag .mergeL .mergeR v → ccState v ≠ 3 := by
  refine ⟨⟨Reachable.refl _ _, Reachable.refl _ _⟩, ?_⟩
  intro v hv
  rcases cc_commonAncestors v hv with rfl | rfl | rfl <;> decide

/-! ## §6. Criss-cross — the verdict

The two merge versions have exactly two maximal common bases (§3.1), they are
distinct, and no lowest one exists. So a merge-base procedure reports
`ambiguous`, and a replica that must nonetheless merge picks one. The two picks
disagree — and they disagree *across the invariant*. -/

/-- ⚠ **The base accident decides the invariant.** Same two versions, two
equally legitimate maximal common bases, no lowest one to prefer between them —
and the results are `5` and `4` against a ceiling of `4`. One replica commits a
legal state, the other an illegal one, and neither made a mistake.

This is the failure `docs/decisions/D-0005` declines to rule out ("base selection
may be ambiguous", the resolution algebra deliberately not built). It is not a
convergence nuisance: it is an invariant verdict decided by which of two
incomparable ancestors a procedure happened to return. -/
theorem base_accident_decides_the_invariant :
    MaximalCommonBase ccDag .mergeL .mergeR .left
      ∧ MaximalCommonBase ccDag .mergeL .mergeR .right
      ∧ (Ver.left ≠ Ver.right)
      ∧ (¬ ∃ b, LowestCommonBase ccDag .mergeL .mergeR b)
      ∧ counterAM.merge3 (ccState .left) (ccState .mergeL) (ccState .mergeR) = 5
      ∧ counterAM.merge3 (ccState .right) (ccState .mergeL) (ccState .mergeR) = 4
      ∧ ¬ ((5 : Nat) ≤ 4) ∧ ((4 : Nat) ≤ 4) :=
  ⟨cc_left_maximal, cc_right_maximal, by decide, cc_no_lowest,
   by decide, by decide, by decide, by decide⟩

/-- ⚠ **Criss-cross diverges.** The weaker half of the previous theorem, said
plainly: the two legitimate merges of the same pair are different states, so two
replicas performing the same reconciliation against the same DAG do not converge.
`Ancestral`'s `comm` law buys agreement between the two *replicas of one merge*;
it buys nothing between two *base choices*. -/
theorem crisscross_diverges :
    counterAM.merge3 (ccState .left) (ccState .mergeL) (ccState .mergeR)
      ≠ counterAM.merge3 (ccState .right) (ccState .mergeL) (ccState .mergeR) := by
  decide

/-- ⚠ **And the version-level ambiguity of §5's first round is invisible at the
state level.** `left` and `right` are the two maximal bases for `mergeL`/`mergeR`
with *distinct* states — so `ambiguous` is expressible there. But `mergeL` and
`mergeR` themselves hold the *same* state `3`, so a `BaseDecision` about the pair
`(3, 3)` cannot record that two different versions were merged at all. The
decision type is about states; the ambiguity is about versions. -/
theorem ambiguity_visibility :
    MaximalCommonBase ccDag .mergeL .mergeR .left
      ∧ MaximalCommonBase ccDag .mergeL .mergeR .right
      ∧ ccState .left ≠ ccState .right
      ∧ ccState .mergeL = ccState .mergeR :=
  ⟨cc_left_maximal, cc_right_maximal, by decide, by decide⟩

/-! ## §7. The coherence condition that repairs it

§5's diagnosis names the repair. `AncestralConfluent` fails to iterate because
its premise — reachability *from the base* — is destroyed by the first merge. Ask
instead for two things about the **root**:

  * `AncestralConfluentFrom` — the merge is legal for every base and pair drawn
    from the root's reachable set (not from each base's);
  * `MergeClosedFrom` — that set is **closed under merging**.

Together they make every node of every coherent history legal, by induction on
rank. The condition is satisfiable (`lock_mergeClosed`) and refutable
(`counter_not_mergeClosed`), and the refutation lands exactly on §5's history. -/

/-- **The root's reachable set is closed under merging.** -/
def MergeClosedFrom {S Op : Type} (M : AncestralMerge S) (impl : Impl S Op) (ρ : S) : Prop :=
  ∀ l x y : S, Reachable impl ρ l → Reachable impl ρ x → Reachable impl ρ y →
    Reachable impl ρ (M.merge3 l x y)

/-- **Confluence on the root's reachable set.** Compare
`Ancestral.AncestralConfluent`, which asks for reachability *from the base*: this
version asks for reachability from the root, which is the hypothesis a history's
induction can actually supply. -/
def AncestralConfluentFrom {S Op : Type} (M : AncestralMerge S) (impl : Impl S Op)
    (I : Invariant S) (ρ : S) : Prop :=
  ∀ l x y : S, Reachable impl ρ l → Reachable impl ρ x → Reachable impl ρ y →
    I l → I x → I y → I (M.merge3 l x y)

/-- **Every node of a coherent history is legal — and reachable from the root.**
The induction is on `rank`: a `ran` node's parent has smaller rank by
`VersionDag.rank_lt`; a `merged` node's two parents do too, and its *base* does
because it reaches one of them and reachability never decreases rank.

The two conclusions are proved together because each feeds the other: legality of
a merge needs the three inputs reachable (for `AncestralConfluentFrom`), and
reachability of a merge needs `MergeClosedFrom`. -/
theorem History.Coherent.sound {V S Op : Type} {H : History V S Op}
    {M : AncestralMerge S} {impl : Impl S Op} {I : Invariant S}
    (hco : H.Coherent M impl)
    (hloc : LocallySafe impl I)
    (hAC : AncestralConfluentFrom M impl I (H.state H.root))
    (hMC : MergeClosedFrom M impl (H.state H.root))
    (hroot : I (H.state H.root)) :
    ∀ v, Reachable impl (H.state H.root) (H.state v) ∧ I (H.state v) := by
  have step : ∀ v : V,
      (∀ w, H.dag.rank w < H.dag.rank v →
        Reachable impl (H.state H.root) (H.state w) ∧ I (H.state w)) →
      Reachable impl (H.state H.root) (H.state v) ∧ I (H.state v) := by
    intro v ih
    have hnode := hco.nodes v
    cases hor : H.origin v with
    | root =>
      have hv : v = H.root := hco.root_unique v hor
      subst hv
      exact ⟨Reachable.refl _ _, hroot⟩
    | ran p =>
      simp only [OriginOK, hor] at hnode
      obtain ⟨hpar, hrun⟩ := hnode
      obtain ⟨hRp, hIp⟩ := ih p (H.dag.rank_lt _ _ hpar)
      obtain ⟨ops, hops⟩ := hrun
      exact ⟨Reachable.trans hRp ⟨ops, hops⟩, hops.preserves hloc hIp⟩
    | merged l x y =>
      simp only [OriginOK, hor] at hnode
      obtain ⟨hpx, hpy, hca, hst⟩ := hnode
      have hltx := H.dag.rank_lt _ _ hpx
      have hlty := H.dag.rank_lt _ _ hpy
      obtain ⟨hRl, hIl⟩ := ih l (Nat.lt_of_le_of_lt hca.1.rank_le hltx)
      obtain ⟨hRx, hIx⟩ := ih x hltx
      obtain ⟨hRy, hIy⟩ := ih y hlty
      rw [hst]
      exact ⟨hMC _ _ _ hRl hRx hRy, hAC _ _ _ hRl hRx hRy hIl hIx hIy⟩
  have key : ∀ (n : Nat) (v : V), H.dag.rank v ≤ n →
      Reachable impl (H.state H.root) (H.state v) ∧ I (H.state v) := by
    intro n
    induction n with
    | zero => intro v hv; exact step v (fun w hw => absurd hw (by omega))
    | succ n ih => intro v hv; exact step v (fun w hw => ih w (by omega))
  intro v
  exact key (H.dag.rank v) v (Nat.le_refl _)

/-! ### §7.1 The condition is refutable — and it is *exactly* what §5 violates

Both halves are needed for the diagnosis to be sharp, and both are proved: the
counter satisfies `AncestralConfluentFrom` and refutes `MergeClosedFrom`. So §5's
history does not break because the merge is wrong on some triple it was asked
about — it breaks because the merge produced a state nothing was ever asked
about. -/

/-- **The counter satisfies the confluence half.** Everything the root reaches is
at most `2`, and the merge of three such states is at most `4`. -/
theorem counter_ancestralConfluentFrom :
    AncestralConfluentFrom counterAM (spendOps 2).impl (fun n => n ≤ 4) 0 := by
  intro l x y hl hx hy _ _ _
  have hl2 : l ≤ 2 := by rcases spend2_reachable hl with h | ⟨_, h⟩ <;> omega
  have hx2 : x ≤ 2 := by rcases spend2_reachable hx with h | ⟨_, h⟩ <;> omega
  have hy2 : y ≤ 2 := by rcases spend2_reachable hy with h | ⟨_, h⟩ <;> omega
  show counterMerge l x y ≤ 4
  unfold counterMerge
  omega

/-- ⚠ **…and refutes the closure half.** Two branches reachable from `0` merge to
`3`, and `3` is not reachable from `0`: the budget stops at `2`. Set beside
`counter_ancestralConfluentFrom`, this locates §5's counterexample precisely — it
is the single fact the whole break is built on, and the one
`AncestralConfluent` never asks about. -/
theorem counter_not_mergeClosed : ¬ MergeClosedFrom counterAM (spendOps 2).impl 0 := by
  intro h
  have h3 : Reachable (spendOps 2).impl 0 (counterAM.merge3 0 1 2) :=
    h 0 1 2 (Reachable.refl _ _) spend2_reach_one spend2_reach_two
  have hval : counterAM.merge3 0 1 2 = 3 := by decide
  rw [hval] at h3
  rcases spend2_reachable h3 with he | ⟨_, h2⟩
  · exact absurd he (by decide)
  · exact absurd h2 (by decide)

/-! ### §7.2 The condition is satisfiable — the lock, repeatedly

`Ancestral` §5's hand-off lock is the file's prize: mutual exclusion is
ancestrally confluent for `lockAM`. It also satisfies the coherence condition, so
its repeated and criss-cross merges are certified by `Coherent.sound` — the
positive half of this file, and the reason §5's negative is a counterexample and
not an impossibility. -/

/-- **Every legal lock state is one operation away from every state.** The three
grants are total replacements, so the reachability relation on `Lock` is as wide
as the invariant allows — which is `Ancestral` §6's cycle, read as an asset
rather than as the obstruction it is there. -/
theorem lock_reach_of_atMostOne (s t : Lock) (ht : AtMostOne t) :
    Reachable lockImpl s t := by
  obtain ⟨a, b⟩ := t
  cases a <;> cases b
  · exact ⟨[LockOp.release], rfl⟩
  · exact ⟨[LockOp.grantBob], rfl⟩
  · exact ⟨[LockOp.grantAlice], rfl⟩
  · exact absurd ⟨rfl, rfl⟩ ht

/-- The priority policy returns one of three states, each of which any replica
reaches in a single operation. -/
theorem lockPriority_cases (x y : Lock) :
    lockPriority x y = ⟨true, false⟩ ∨ lockPriority x y = ⟨false, true⟩ ∨
      lockPriority x y = ⟨false, false⟩ := by
  unfold lockPriority
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- **The lock is merge-closed, from every root.** Each branch of `lockMerge`
returns a replica the caller already had, or a policy verdict one operation
reaches. Contrast `counter_not_mergeClosed`: the difference between the two
examples is exactly here. -/
theorem lock_mergeClosed (ρ : Lock) : MergeClosedFrom lockAM lockImpl ρ := by
  intro l x y _ hx hy
  show Reachable lockImpl ρ (lockMerge l x y)
  rcases lockMerge_cases l x y with h | h | h
  · rw [h]; exact hy
  · rw [h]; exact hx
  · rw [h]
    rcases lockPriority_cases x y with h' | h' | h' <;> rw [h']
    · exact ⟨[LockOp.grantAlice], rfl⟩
    · exact ⟨[LockOp.grantBob], rfl⟩
    · exact ⟨[LockOp.release], rfl⟩

/-- The lock's confluence needs no reachability at all
(`Ancestral.lock_merge_atMostOne` holds for every triple), so the root-relative
form is immediate. -/
theorem lock_ancestralConfluentFrom (ρ : Lock) :
    AncestralConfluentFrom lockAM lockImpl AtMostOne ρ :=
  fun l x y _ _ _ _ hx hy => lock_merge_atMostOne l x y hx hy

/-- The six versions of a lock history that merges twice. -/
inductive LVer where
  /-- Nobody holds the lock. -/
  | root
  /-- Handed to Alice. -/
  | alice
  /-- Handed to Bob. -/
  | bob
  /-- One replica's merge of the two grants. -/
  | m1
  /-- The other replica's merge of the same pair. -/
  | m2
  /-- The merge of the merges, against the maximal base `alice`. -/
  | j
  deriving DecidableEq, Repr

/-- The lock history's edges — the same criss-cross shape, one join. -/
def lvParent : LVer → LVer → Bool
  | .root, .alice => true
  | .root, .bob => true
  | .alice, .m1 => true
  | .bob, .m1 => true
  | .alice, .m2 => true
  | .bob, .m2 => true
  | .m1, .j => true
  | .m2, .j => true
  | _, _ => false

/-- Depth. -/
def lvRank : LVer → Nat
  | .root => 0
  | .alice => 1
  | .bob => 1
  | .m1 => 2
  | .m2 => 2
  | .j => 3

/-- The lock version DAG. -/
def lvDag : VersionDag LVer where
  parent := lvParent
  rank := lvRank
  rank_lt := by intro p c; cases p <;> cases c <;> decide

/-- The states. `m1` and `m2` are `lockPriority` verdicts; `j` is a
fast-forward. -/
def lvState : LVer → Lock
  | .root => ⟨false, false⟩
  | .alice => ⟨true, false⟩
  | .bob => ⟨false, true⟩
  | .m1 => ⟨true, false⟩
  | .m2 => ⟨true, false⟩
  | .j => ⟨true, false⟩

/-- The origins. -/
def lvOrigin : LVer → Origin LVer
  | .root => .root
  | .alice => .ran .root
  | .bob => .ran .root
  | .m1 => .merged .root .alice .bob
  | .m2 => .merged .root .alice .bob
  | .j => .merged .alice .m1 .m2

/-- The lock history: fork, two independent merges of the fork, and a merge of
those two merges. -/
def lockHistory : History LVer Lock LockOp where
  dag := lvDag
  state := lvState
  origin := lvOrigin
  root := .root

/-- `root` is a common ancestor of the two grants. -/
theorem lv_root_common : CommonAncestor lvDag .alice .bob .root :=
  ⟨Or.inr (.direct (by decide)), Or.inr (.direct (by decide))⟩

/-- `alice` is a common ancestor of the two merges. -/
theorem lv_alice_common : CommonAncestor lvDag .m1 .m2 .alice :=
  ⟨Or.inr (.direct (by decide)), Or.inr (.direct (by decide))⟩

/-- `bob` is a common ancestor of the two merges — the other maximal candidate,
which §7.3 shows the merge does not distinguish. -/
theorem lv_bob_common : CommonAncestor lvDag .m1 .m2 .bob :=
  ⟨Or.inr (.direct (by decide)), Or.inr (.direct (by decide))⟩

/-- Only the root is a root. -/
theorem lvOrigin_root_unique (v : LVer) (h : lvOrigin v = Origin.root) : v = .root := by
  cases v <;> simp_all [lvOrigin]

/-- The lock history is coherent. -/
theorem lockHistory_coherent : lockHistory.Coherent lockAM lockImpl where
  root_unique := lvOrigin_root_unique
  nodes := by
    intro v
    cases v
    · trivial
    · show lvDag.parent .root .alice = true ∧
        Reachable lockImpl ⟨false, false⟩ ⟨true, false⟩
      exact ⟨by decide, ⟨[LockOp.grantAlice], rfl⟩⟩
    · show lvDag.parent .root .bob = true ∧
        Reachable lockImpl ⟨false, false⟩ ⟨false, true⟩
      exact ⟨by decide, ⟨[LockOp.grantBob], rfl⟩⟩
    · show lvDag.parent .alice .m1 = true ∧ lvDag.parent .bob .m1 = true ∧
        CommonAncestor lvDag .alice .bob .root ∧
        (⟨true, false⟩ : Lock) = lockMerge ⟨false, false⟩ ⟨true, false⟩ ⟨false, true⟩
      exact ⟨by decide, by decide, lv_root_common, by decide⟩
    · show lvDag.parent .alice .m2 = true ∧ lvDag.parent .bob .m2 = true ∧
        CommonAncestor lvDag .alice .bob .root ∧
        (⟨true, false⟩ : Lock) = lockMerge ⟨false, false⟩ ⟨true, false⟩ ⟨false, true⟩
      exact ⟨by decide, by decide, lv_root_common, by decide⟩
    · show lvDag.parent .m1 .j = true ∧ lvDag.parent .m2 .j = true ∧
        CommonAncestor lvDag .m1 .m2 .alice ∧
        (⟨true, false⟩ : Lock) = lockMerge ⟨true, false⟩ ⟨true, false⟩ ⟨true, false⟩
      exact ⟨by decide, by decide, lv_alice_common, by decide⟩

/-- **The coherence condition earns its keep.** Mutual exclusion holds at *every
version* of a history that forks, merges twice independently, and merges the
merges — the shape §5 breaks the counter on. `Coherent.sound` is doing the work;
the two hypotheses it needs are `lock_ancestralConfluentFrom` and
`lock_mergeClosed`, and the counter refutes the second. -/
theorem lock_history_safe :
    ∀ v, Reachable lockImpl ⟨false, false⟩ (lvState v) ∧ AtMostOne (lvState v) :=
  lockHistory_coherent.sound lock_locally_safe
    (lock_ancestralConfluentFrom ⟨false, false⟩) (lock_mergeClosed ⟨false, false⟩)
    (by decide)

/-- **The lock history is run-realized** — every DAG edge, *including the edges
into merge nodes*, is a local run. This is the same property as
`lock_mergeClosed` seen from the graph: the lock's merges land back inside the
op-reachable region, which is exactly what `ccHistory_not_runRealized` says the
counter's do not. -/
theorem lockHistory_runRealized : RunRealized lockHistory lockImpl := by
  intro p c _
  exact lock_reach_of_atMostOne (lvState p) (lvState c) (by cases c <;> decide)

/-- **§4's bridge, discharged on a real history.** `alice` is a common ancestor
of the two merge versions in the DAG, so `MergeModel.BaseDecision.selected` is
`Valid` for their two states — the merge-base procedure's answer becomes the
decision model's context, with its obligation proved from ancestry rather than
asserted. The bridge is not vacuous, and `ccHistory_not_runRealized` says exactly
which histories it does not reach. -/
theorem lock_selected_valid :
    (MergeModel.BaseDecision.selected (lvState .alice)).Valid lockImpl
      (lvState .m1) (lvState .m2) :=
  selected_valid lockHistory_runRealized lv_alice_common

/-- The common ancestors of the lock's two merge versions are exactly `root`,
`alice` and `bob` — the same criss-cross enumeration as `cc_commonAncestors`. -/
theorem lv_commonAncestors (v : LVer) (h : CommonAncestor lvDag .m1 .m2 v) :
    v = .root ∨ v = .alice ∨ v = .bob := by
  cases v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · rcases h.2.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases h.1.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)

/-- `alice` is a maximal common base of the two merge versions. -/
theorem lv_alice_maximal : MaximalCommonBase lvDag .m1 .m2 .alice := by
  refine ⟨lv_alice_common, ?_⟩
  intro c hc hreach
  rcases lv_commonAncestors c hc with rfl | rfl | rfl
  · rcases hreach.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rfl
  · rcases hreach.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)

/-- …and so is `bob`, so the lock's second merge is under a genuinely ambiguous
base decision too. -/
theorem lv_bob_maximal : MaximalCommonBase lvDag .m1 .m2 .bob := by
  refine ⟨lv_bob_common, ?_⟩
  intro c hc hreach
  rcases lv_commonAncestors c hc with rfl | rfl | rfl
  · rcases hreach.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rcases hreach.eq_or_rank_lt with he | hr
    · exact absurd he (by decide)
    · exact absurd hr (by decide)
  · rfl

/-- **§4's `ambiguous` bridge, discharged on a real history.** Two distinct
maximal common bases with *distinct states*, so the ambiguity is expressible at
the state level and `MergeModel.BaseDecision.ambiguous` is `Valid` for the pair.
Every hypothesis of `ambiguous_valid` is met by a history that exists. -/
theorem lock_ambiguous_valid :
    (MergeModel.BaseDecision.ambiguous (lvState .alice) (lvState .bob)).Valid lockImpl
      (lvState .m1) (lvState .m2) :=
  ambiguous_valid lockHistory_runRealized lv_alice_maximal lv_bob_maximal (by decide)

/-- …and the lock's last merge is **base-insensitive**: against `alice` it
fast-forwards, against `bob` the priority policy returns the same state. The
ambiguity is genuine here (`lv_alice_maximal`, `lv_bob_maximal`,
`lock_ambiguous_valid`) and it costs nothing. Set beside
`base_accident_decides_the_invariant`, where the same shape of ambiguity decides
an invariant verdict: **whether ambiguity is fatal is a property of the merge,
not of the DAG.** -/
theorem lock_join_base_insensitive :
    lockAM.merge3 (lvState .alice) (lvState .m1) (lvState .m2)
      = lockAM.merge3 (lvState .bob) (lvState .m1) (lvState .m2) := by decide

/-! ### §7.3 ⚠ Invariant safety is not convergence — an eternal two-cycle

`MergeModel.BaseDecision.Valid` licenses a base whenever both replicas op-reach
from it. Under `lockImpl` every state reaches every legal one, so for the pair
(Alice, Bob) **both** `selected Alice` and `selected Bob` are valid — and they
disagree, by `fastforward` on opposite sides.

Two replicas each taking their own state as the base therefore swap, forever.
The invariant survives every step (`lock_merge_atMostOne`); the replicas never
agree. This is the sharpest available statement that `Coherent.sound`'s
conclusion is *not* convergence. -/

/-- One round in which each replica takes its own state as the merge base. -/
def swapRound (p : Lock × Lock) : Lock × Lock :=
  (lockMerge p.1 p.1 p.2, lockMerge p.2 p.2 p.1)

/-- Each side fast-forwards to the other's state: the round is a swap. -/
theorem swapRound_eq (x y : Lock) : swapRound (x, y) = (y, x) := by
  show (lockMerge x x y, lockMerge y y x) = (y, x)
  rw [show lockMerge x x y = y from lockAM.fastforward x y,
      show lockMerge y y x = x from lockAM.fastforward y x]

/-- Iteration, spelled out (Lean core, no mathlib). -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => iter f n (f a)

/-- ⚠ **The two replicas never converge.** Two distinct states swap forever under
a base policy `MergeModel.BaseDecision.Valid` fully licenses. -/
theorem swap_never_converges : ∀ (n : Nat) (x y : Lock), x ≠ y →
    (iter swapRound n (x, y)).1 ≠ (iter swapRound n (x, y)).2 := by
  intro n
  induction n with
  | zero => intro x y h; exact h
  | succ n ih =>
    intro x y h
    show (iter swapRound n (swapRound (x, y))).1 ≠ (iter swapRound n (swapRound (x, y))).2
    rw [swapRound_eq]
    exact ih y x (Ne.symm h)

/-- **Both bases are valid and they disagree** — the state-level fact the orbit
above is built on. Neither replica may be blamed: `MergeModel.BaseDecision`'s
validity obligation is discharged for both. -/
theorem lock_two_valid_bases :
    (MergeModel.BaseDecision.selected (⟨true, false⟩ : Lock)).Valid lockImpl
        ⟨true, false⟩ ⟨false, true⟩
      ∧ (MergeModel.BaseDecision.selected (⟨false, true⟩ : Lock)).Valid lockImpl
        ⟨true, false⟩ ⟨false, true⟩
      ∧ lockAM.merge3 ⟨true, false⟩ ⟨true, false⟩ ⟨false, true⟩
        ≠ lockAM.merge3 ⟨false, true⟩ ⟨true, false⟩ ⟨false, true⟩ :=
  ⟨⟨Reachable.refl _ _, ⟨[LockOp.grantBob], rfl⟩⟩,
   ⟨⟨[LockOp.grantAlice], rfl⟩, Reachable.refl _ _⟩,
   by decide⟩

/-! ## §8. The verdicts, side by side -/

/-- **The frontier codex named, answered.**

  * **Repeated merge** — `AncestralConfluent` does *not* survive it. The escrow
    is ancestrally confluent and a coherent history over it has an illegal node.
  * **Criss-cross** — it *diverges*, and the divergence decides the invariant:
    two maximal common bases, no lowest one, results `5` and `4`, ceiling `4`.
  * **A coherence condition** — `MergeClosedFrom` plus `AncestralConfluentFrom`
    make every node of every coherent history legal. The counter satisfies the
    confluence half and refutes the closure half, which locates the break
    exactly; the lock satisfies both.
  * **…and it still is not convergence.** The lock satisfies the condition,
    every version of its history is legal, and two replicas under a fully valid
    base policy swap forever. -/
theorem the_verdicts :
    (AncestralConfluent counterAM (spendOps 2).impl (fun n => n ≤ 4)
      ∧ ccHistory.Coherent counterAM (spendOps 2).impl
      ∧ ¬ (ccState .joinLeft ≤ 4))
    ∧ (¬ ∃ b, LowestCommonBase ccDag .mergeL .mergeR b)
    ∧ counterAM.merge3 (ccState .left) (ccState .mergeL) (ccState .mergeR)
        ≠ counterAM.merge3 (ccState .right) (ccState .mergeL) (ccState .mergeR)
    ∧ (AncestralConfluentFrom counterAM (spendOps 2).impl (fun n => n ≤ 4) 0
      ∧ ¬ MergeClosedFrom counterAM (spendOps 2).impl 0)
    ∧ (∀ ρ : Lock, MergeClosedFrom lockAM lockImpl ρ)
    ∧ (∀ v, AtMostOne (lvState v))
    ∧ (∀ (n : Nat) (x y : Lock), x ≠ y →
        (iter swapRound n (x, y)).1 ≠ (iter swapRound n (x, y)).2) :=
  ⟨⟨counter_ceiling4_ancestral, ccHistory_coherent, by decide⟩,
   cc_no_lowest, crisscross_diverges,
   ⟨counter_ancestralConfluentFrom, counter_not_mergeClosed⟩, lock_mergeClosed,
   fun v => (lock_history_safe v).2, swap_never_converges⟩

end Uwueave.Histories
