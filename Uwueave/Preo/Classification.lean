/-
# Uwueave.Preo.Classification — a classification ACCUMULATES facets; it does
not pick a winner.

Fragment 1 (`Uwueave.Preo.Elab` §3) ran four routes in order and took the first
match, producing exactly one answer per invariant. The external reviewer
(codex) named the structural defect in that shape:

> SEAM is not a third alternative to free and clash — it is **additional
> structured evidence about a globally clashing invariant**. Rules should
> monotonically add certified facts; a separate report policy ranks
> explanations. Prove **route-order invariance** of the accumulated semantic
> result.

Both halves are here.

## §1–§2 — the facets, and why they cannot disagree

A `Facet` is one certified fact, and every constructor carries its evidence:
`global` carries a `Spec.Verdict` (which cannot exist without an `IConfluent`
proof or a two-replica repro), `seam` carries a `Spec.SegVerdict` (which
carries **both** the global clash and the segmentation proof), `mergeable`
carries a `JoinHom.Fourth` **and** its `Fourth.Correct` proof, and `obligation`
carries no evidence at all and is not readable as an answer.

The three agreement theorems are what make accumulation safe rather than
merely permissive:

  * `verdict_agree` — **any two verdicts for one invariant agree.** Not "the
    elaborator is careful": a `free` and a `clash` for the same `I` are
    contradictory *terms*, so the pair is uninhabitable.
  * `seam_forces_clash` — **a seam facet forces every global facet to CLASH.**
    This is codex's sentence as a theorem: a `SegVerdict` is not a competing
    third answer, it is extra structure on top of a clash, and it *entails* the
    clash (`SegVerdict.escalatesGlobally`).
  * `fourth_unique` — **a computation has one mergeability answer**
    (`JoinHom.fourth_exclusive`).

## §3 — route-order invariance, as a theorem about running a registry

`run` maps a rule registry (a list of *outcomes*, `none` = "the route did not
apply", the fragment-1 `tryEmit` discipline) to a `Classification` by four
`filterMap`s — manifestly monotone, manifestly stateless, no first-match
short-circuit anywhere.

`run_answer_congr` then says: **two registries with the same rules in any order
certify the same answer.** Its hypothesis is membership-equality, so it covers
permutation (`run_answer_of_perm`), duplication, and rule-set extension by a
rule that was already there. What it does *not* claim is that the report is
identical — `run rs |>.global` is a list, and which explanation comes first is
exactly the report policy's business.

The proof is not bookkeeping: it bottoms out in `verdict_agree` and
`seam_forces_clash`, i.e. in the fact that facets cannot contradict each other.
A first-match elaborator has no such theorem available, because its answer
genuinely depends on the order.

⚠ Two adjacent statements worth not conflating. `run_answer_congr` is about
**reordering** a registry — same rules, different sequence. `answerOf_congr`
(and `Classification.answer_unique`) is about **adding or dropping** a rule
whose facet kind was already reached, which is the strictly different fact that
lets the elaborator skip an expensive route once a cheap one has answered. The
elaborator relies on the second; the first is what codex asked for.

## §4 — the seam rule, off the hardcoded budget

`Spec.budgetSegVerdict` is pinned at budget 10. `budgetSeam B hB` is the same
object for every positive budget, so a `preo` author may write their own number
and still reach the seam. `budget_not_iconfluent_at` generalises
`Segmented.budget_not_iconfluent` (which is stated only at 10).

## §5 — the mergeability transport

A `derive` reads one field, so its computation is `g ∘ π` for a projection `π`.
`mergeability_comp` carries a field-scale `Fourth` answer to the declared
state — and note the asymmetry that makes it real content: the `fromResults`
half needs only that `π` is a join homomorphism, while the `needsEvidence` half
needs `π` **surjective** as well (otherwise the composite could be mergeable on
the reachable part while `g` is not). The elaborator emits both, the second as
a state with `default` in every other field.

## What is NOT here, and why

codex's sketch also lists `reachability` and `repairs : Array RepairCandidate`.
Neither is shipped. `Uwueave.Repair`'s `Repair P Q` is indexed by two
`Promise`s, and this fragment has no rule that can *produce* one from a `preo`
declaration; a `repairs` field with no rule that ever fills it is a facet with
no backing theorem, which is the thing the brief forbids. Same for
reachability: `CausalReach`/`WorldFuture` classify executions, and a `preo`
declaration currently declares no operations, so there is nothing to be
reachable. Both are named here so their absence is a decision on the record
rather than an omission.
-/
import Uwueave.Preo.Syntax
import Uwueave.JoinHom

namespace Uwueave.Preo

open Uwueave Uwueave.Catalog Uwueave.Spec Uwueave.Segmented

/-! ## §1. The sixth field kind: a budgeted quota

Fragment 1's `Escrow ι` carries per-replica spend and nothing to spend
*against*. The seam story needs the allocation **inside** the state — that is
the whole point of `Segmented.lean`'s `QuotaState`, and it is why the escrow row
of `Preo.Demo`'s `LoomDoc` was the *other* budget story rather than the seam. -/

/-- **A budgeted quota: allocation plus per-replica spend.** Definitionally
`Segmented.QuotaState` at `ι := Bool`, so `Segmented.budget_segmented` and
`Spec.budgetSegVerdict` apply to a `preo` field of this kind verbatim — which is
the point of choosing the tree's own carrier instead of a new one. -/
abbrev Quota (ι : Type) : Type := (ι → Nat) × Catalog.Escrow ι

/-- The carrier really is the one `Segmented.lean` proves about. -/
theorem quota_bool_eq : Quota Bool = Segmented.QuotaState := rfl

/-! ## §2. Facets, and the three reasons they cannot disagree -/

/-- **Any two verdicts for one invariant agree.** The pair `(free h, clash …)`
is uninhabitable: `h` applied to the clash's own two replicas contradicts its
own refutation. So an accumulating classifier can hold several verdicts for one
invariant without any policy for reconciling them — there is nothing to
reconcile, and this theorem is the licence.

⚠ Read what it does *not* say: it does not say two rules produce the same
*term*. Two clashes may carry different witness pairs, and which repro a report
prints is a report-policy question. The **answer** is what is forced. -/
theorem verdict_agree {S : Type u} [MergeState S] {I : Invariant S} (v w : Verdict I) :
    v.isFree = w.isFree := by
  cases v with
  | free hv =>
    cases w with
    | free _ => rfl
    | clash x y hx hy hbad => exact absurd (hv x y hx hy) hbad
  | clash x y hx hy hbad =>
    cases w with
    | free hw => exact absurd (hw x y hx hy) hbad
    | clash _ _ _ _ _ => rfl

/-- ⚠ **A seam is not a third answer — it forces the first one.** codex's
correction, as a theorem: a `SegVerdict` carries a global clash
(`SegVerdict.escalatesGlobally`), so any global verdict for the same invariant
must read ESCALATES. A classification holding both a seam and a `free` is
therefore not merely inconsistent policy, it is an uninhabited pair of types. -/
theorem seam_forces_clash {S : Type u} [MergeState S] {I : Invariant S} {Seg : Type v}
    (s : SegVerdict I Seg) (v : Verdict I) : v.isFree = false := by
  cases v with
  | free h => exact absurd h s.escalatesGlobally
  | clash _ _ _ _ _ => rfl

/-- **A computation has one mergeability answer.** `JoinHom.fourth_exclusive`
in the form the accumulator needs. -/
theorem fourth_unique {S R : Type} [MergeState S] {f : S → R}
    {a b : JoinHom.Fourth} (ha : JoinHom.Fourth.Correct f a)
    (hb : JoinHom.Fourth.Correct f b) : a = b := by
  cases a with
  | fromResults =>
    cases b with
    | fromResults => rfl
    | needsEvidence => exact absurd ha hb
  | needsEvidence =>
    cases b with
    | fromResults => exact absurd hb ha
    | needsEvidence => rfl

/-- A seam facet with its segment type bundled — a classification may hold
seams over different projections (`SeamAlgebra.Finer` is when one refines
another), so the segment type cannot be an index of the classification. -/
structure SeamFacet {S : Type} [MergeState S] (I : Invariant S) : Type 1 where
  /-- The segment type. -/
  Seg : Type
  /-- The seam verdict itself: the global clash **and** the segmentation proof. -/
  verdict : SegVerdict I Seg
  /-- What the seam means, in the author's words. Display only. -/
  reading : String

/-- A mergeability facet: the fourth verdict for `f`, with its proof. There is
no way to record an answer without one (`Fourth.Correct` is the proof
obligation), and `fourth_unique` says two of these about one `f` agree. -/
structure MergeFacet {S : Type} [MergeState S] {R : Type} (f : S → R) : Type where
  /-- `fromResults` (ship summaries) or `needsEvidence` (ship the log). -/
  answer : JoinHom.Fourth
  /-- The proof that this is the right answer for `f`. -/
  correct : JoinHom.Fourth.Correct f answer
  /-- The theorem this row cites. Display only. -/
  cite : String

/-- **One certified fact about an item.** Every constructor carries evidence —
except `obligation`, which carries none *and* is not readable as an answer
(`Facet.answer` sends it to `none`). That asymmetry is fragment 1's discipline
kept: a facet the elaborator cannot justify is an obligation, never a guess. -/
inductive Facet {S : Type} [MergeState S] (I : Invariant S) {R : Type} (f : S → R) : Type 1 where
  /-- The binary judgement, with its evidence. -/
  | global (v : Verdict I)
  /-- Structured evidence about a globally clashing invariant. -/
  | seam (s : SeamFacet I)
  /-- The fourth verdict for the item's computation. -/
  | mergeable (m : MergeFacet f)
  /-- No rule reached a fact. Not an answer. -/
  | obligation (o : Obligation I)

/-! ## §3. The classification, and its semantic reading

An **item** is an invariant to judge (`I`) and a computation to judge (`f`).
An invariant row takes `f := fun _ => ()`; a `derive` row takes
`I := fun _ => True`. One structure, so the accumulation and the invariance
theorem are stated once. -/

/-- **The accumulated classification of one item.** Every field is a *list*,
because rules add and never replace; the semantic reading (`answer`,
`mergeAnswer`) is what is order-independent, and the list order is the report
policy's to rank. -/
structure Classification {S : Type} [MergeState S] (I : Invariant S)
    {R : Type} (f : S → R) : Type 1 where
  /-- Global verdicts. Several rules may reach one; `verdict_agree` says they
  cannot disagree. -/
  global : List (Verdict I)
  /-- Seam facets — additional structure about a *clashing* invariant, never an
  alternative to one (`seam_forces_clash`). -/
  seams : List (SeamFacet I)
  /-- Mergeability facets for the item's computation. -/
  mergeability : List (MergeFacet f)
  /-- What no rule reached. -/
  obligations : List (Obligation I)

namespace Classification

variable {S : Type} [MergeState S] {I : Invariant S} {R : Type} {f : S → R}

/-- The empty classification: nothing certified, nothing claimed. -/
def empty : Classification I f := ⟨[], [], [], []⟩

/-- The confluence answer, read off the accumulated facets. A seam pins it to
ESCALATES on its own (`seam_forces_clash`); otherwise the global facets speak;
and with neither there is **no answer**, which is `none` and is not FREE. -/
def answerOf (seams : List (SeamFacet I)) (global : List (Verdict I)) : Option Bool :=
  match seams with
  | _ :: _ => some false
  | [] =>
    match global with
    | [] => none
    | v :: _ => some v.isFree

/-- The item's confluence answer. Computed from the facets at every read, never
stored — the fragment-1 rule that a stored answer is a second source of truth. -/
def answer (c : Classification I f) : Option Bool := answerOf c.seams c.global

/-- **Recover the checked semantic verdict, but only from an answered
classification.** A global facet already carries the desired `Spec.Verdict`;
when there is no global facet, an answered classification must contain a seam,
whose carried repro demotes to `Verdict.clash`. With neither facet the equality
premise is impossible, so an unresolved classification has no construction
path through this function.

The global head is deliberately preferred when present. `verdict_agree` and
`seam_forces_clash` prove that this choice cannot change the semantic answer;
`checkedVerdict_isFree` states that agreement exactly. -/
def checkedVerdict (c : Classification I f) {a : Bool}
    (answered : c.answer = some a) : Verdict I := by
  cases hg : c.global with
  | cons verdict _ => exact verdict
  | nil =>
    cases hs : c.seams with
    | cons seam _ => exact seam.verdict.toClash
    | nil =>
      have impossible : False := by
        simp [answer, answerOf, hg, hs] at answered
      exact impossible.elim

/-- The extracted verdict agrees exactly with the answer whose proof licensed
its extraction. This rules out a hidden second verdict policy in exporters. -/
theorem checkedVerdict_isFree (c : Classification I f) {a : Bool}
    (answered : c.answer = some a) : (c.checkedVerdict answered).isFree = a := by
  rcases c with ⟨global, seams, mergeability, obligations⟩
  cases global with
  | cons verdict rest =>
    cases seams with
    | nil =>
      change verdict.isFree = a
      exact Option.some.inj answered
    | cons seam seams =>
      change verdict.isFree = a
      exact (seam_forces_clash seam.verdict verdict).trans (Option.some.inj answered)
  | nil =>
    cases seams with
    | cons seam seams =>
      change false = a
      exact Option.some.inj answered
    | nil => simp [answer, answerOf] at answered

/-- The empty classification is unresolved. In particular there is no
equality proof with which to call `checkedVerdict`. -/
@[simp] theorem empty_answer : (empty (I := I) (f := f)).answer = none := rfl

/-- Any explicitly unresolved classification has no checked-verdict licence. -/
theorem no_checkedVerdict_licence_of_answer_none (c : Classification I f)
    (unresolved : c.answer = none) : ¬ ∃ a, c.answer = some a := by
  rintro ⟨a, answered⟩
  simp [unresolved] at answered

/-- The item's mergeability answer, or `none` when no rule reached one. -/
def mergeAnswer (c : Classification I f) : Option JoinHom.Fourth :=
  match c.mergeability with
  | [] => none
  | m :: _ => some m.answer

/-! ### Soundness: the accumulated answer cannot lie -/

/-- `some true` **is** a proof of I-confluence. -/
theorem answer_true (c : Classification I f) (h : c.answer = some true) : IConfluent I := by
  unfold answer answerOf at h
  cases hs : c.seams with
  | cons a s => rw [hs] at h; exact absurd h (by simp)
  | nil =>
    rw [hs] at h
    cases hg : c.global with
    | nil => rw [hg] at h; exact absurd h (by simp)
    | cons v g =>
      rw [hg] at h
      exact Tactics.iconfluent_of_isFree (v := v) (Option.some.inj h)

/-- `some false` **is** a refutation — from a seam's carried clash or from a
`clash` verdict, and those are the only two ways to get one. -/
theorem answer_false (c : Classification I f) (h : c.answer = some false) : ¬ IConfluent I := by
  unfold answer answerOf at h
  cases hs : c.seams with
  | cons a s => rw [hs] at h; exact a.verdict.escalatesGlobally
  | nil =>
    rw [hs] at h
    cases hg : c.global with
    | nil => rw [hg] at h; exact absurd h (by simp)
    | cons v g =>
      rw [hg] at h
      exact Tactics.not_iconfluent_of_isFree_false (v := v) (Option.some.inj h)

/-- The mergeability answer is the right one for `f`. -/
theorem mergeAnswer_correct (c : Classification I f) {a : JoinHom.Fourth}
    (h : c.mergeAnswer = some a) : JoinHom.Fourth.Correct f a := by
  unfold mergeAnswer at h
  cases hm : c.mergeability with
  | nil => rw [hm] at h; exact absurd h (by simp)
  | cons m ms =>
    rw [hm] at h
    have : m.answer = a := Option.some.inj h
    exact this ▸ m.correct

/-- ⚠ **Two classifications of the same invariant that both answer, agree.**
However they were built, by whatever rules, in whatever order. This is
`verdict_agree` lifted from terms to the accumulator, and it is why an
accumulating classifier needs no reconciliation policy. -/
theorem answer_unique (c d : Classification I f) {a b : Bool}
    (hc : c.answer = some a) (hd : d.answer = some b) : a = b := by
  cases a with
  | true =>
    cases b with
    | true => rfl
    | false => exact absurd (answer_true c hc) (answer_false d hd)
  | false =>
    cases b with
    | true => exact absurd (answer_true d hd) (answer_false c hc)
    | false => rfl

end Classification

/-! ## §4. Running a rule registry, and route-order invariance -/

/-- **A rule outcome.** `none` is a route that did not apply — fragment 1's
`tryEmit` discipline (a route which does not apply leaves *nothing* behind, not
a logged error and a hole). `some facet` is a certified fact. There is no third
possibility, and in particular no way for a rule to report an answer without
its evidence. -/
abbrev Rule {S : Type} [MergeState S] (I : Invariant S) {R : Type} (f : S → R) : Type 1 :=
  Option (Facet I f)

namespace Facet

variable {S : Type} [MergeState S] {I : Invariant S} {R : Type} {f : S → R}

/-- The global facet, if this is one. -/
def asGlobal : Facet I f → Option (Verdict I)
  | .global v => some v
  | _ => none

/-- The seam facet, if this is one. -/
def asSeam : Facet I f → Option (SeamFacet I)
  | .seam s => some s
  | _ => none

/-- The mergeability facet, if this is one. -/
def asMerge : Facet I f → Option (MergeFacet f)
  | .mergeable m => some m
  | _ => none

/-- The obligation, if this is one. -/
def asObligation : Facet I f → Option (Obligation I)
  | .obligation o => some o
  | _ => none

end Facet

/-- **Run a registry.** Four `filterMap`s over the rule outcomes: monotone by
construction (every rule's fact lands), stateless (no accumulator threading),
and with no first-match short-circuit anywhere — which is exactly what makes
§4's invariance theorem provable and what fragment 1's ordered `if/else if`
chain could not support. -/
def run {S : Type} [MergeState S] {I : Invariant S} {R : Type} {f : S → R}
    (rs : List (Rule I f)) : Classification I f where
  global := rs.filterMap fun r => r.bind Facet.asGlobal
  seams := rs.filterMap fun r => r.bind Facet.asSeam
  mergeability := rs.filterMap fun r => r.bind Facet.asMerge
  obligations := rs.filterMap fun r => r.bind Facet.asObligation

section Invariance

variable {S : Type} [MergeState S] {I : Invariant S} {R : Type} {f : S → R}

/-- The invariance kernel at the level of the two lists the answer reads:
**the answer depends only on WHICH facet kinds were reached**, never on which
rule reached them, how many did, or in what order. The `verdict_agree` call at
the bottom is the whole content. -/
theorem answerOf_congr (s₁ s₂ : List (SeamFacet I)) (g₁ g₂ : List (Verdict I))
    (hs : s₁ = [] ↔ s₂ = []) (hg : g₁ = [] ↔ g₂ = []) :
    Classification.answerOf s₁ g₁ = Classification.answerOf s₂ g₂ := by
  cases s₁ with
  | cons a s =>
    cases s₂ with
    | cons b t => rfl
    | nil => exact absurd (hs.mpr rfl) (by simp)
  | nil =>
    cases s₂ with
    | cons b t => exact absurd (hs.mp rfl) (by simp)
    | nil =>
      cases g₁ with
      | nil =>
        cases g₂ with
        | nil => rfl
        | cons w t => exact absurd (hg.mp rfl) (by simp)
      | cons v s =>
        cases g₂ with
        | nil => exact absurd (hg.mpr rfl) (by simp)
        | cons w t => exact congrArg some (verdict_agree v w)

/-- Which facet kinds a registry reaches is a fact about its *membership*. -/
theorem run_global_nil_iff (rs : List (Rule I f)) :
    (run rs).global = [] ↔ ∀ r ∈ rs, r.bind Facet.asGlobal = none :=
  List.filterMap_eq_nil_iff

theorem run_seams_nil_iff (rs : List (Rule I f)) :
    (run rs).seams = [] ↔ ∀ r ∈ rs, r.bind Facet.asSeam = none :=
  List.filterMap_eq_nil_iff

theorem run_merge_nil_iff (rs : List (Rule I f)) :
    (run rs).mergeability = [] ↔ ∀ r ∈ rs, r.bind Facet.asMerge = none :=
  List.filterMap_eq_nil_iff

/-- ⚠ **ROUTE-ORDER INVARIANCE.** Two rule registries with the same rules —
in any order, with any duplication — certify the **same answer**. The
hypothesis is membership-equality rather than permutation on purpose: adding a
rule the registry already had, or running the routes in a different order
because a cheaper one was moved to the front, is covered by the same statement.

What is *not* claimed, and codex's phrasing is exact about it: the two
classifications are not equal. `(run rs).global` is a list and its order is
which explanation a report prints first. **Report ordering may vary; facts may
not.** -/
theorem run_answer_congr (rs ss : List (Rule I f)) (hmem : ∀ r, r ∈ rs ↔ r ∈ ss) :
    (run rs).answer = (run ss).answer := by
  refine answerOf_congr _ _ _ _ ?_ ?_
  · rw [run_seams_nil_iff, run_seams_nil_iff]
    exact ⟨fun h r hr => h r ((hmem r).mpr hr), fun h r hr => h r ((hmem r).mp hr)⟩
  · rw [run_global_nil_iff, run_global_nil_iff]
    exact ⟨fun h r hr => h r ((hmem r).mpr hr), fun h r hr => h r ((hmem r).mp hr)⟩

/-- Permuting the registry is a special case — the literal reading of
"permuting the rule registry preserves the classification". -/
theorem run_answer_of_perm {rs ss : List (Rule I f)} (h : rs.Perm ss) :
    (run rs).answer = (run ss).answer :=
  run_answer_congr rs ss fun _ => h.mem_iff

/-- The same invariance for the mergeability facet — and here it needs **no
hypothesis at all**. `fourth_unique` forces agreement between any two correct
answers for one computation, so two registries that share nothing but the
subject still agree. (Recorded with the weaker route-order statement dropped
rather than carried as an unused hypothesis: an unused hypothesis on a theorem
this load-bearing reads as a stronger requirement than the proof has.) -/
theorem run_mergeAnswer_unique (rs ss : List (Rule I f)) {a b : JoinHom.Fourth}
    (ha : (run rs).mergeAnswer = some a) (hb : (run ss).mergeAnswer = some b) : a = b :=
  fourth_unique (Classification.mergeAnswer_correct _ ha)
    (Classification.mergeAnswer_correct _ hb)

/-- ⚠ **And a seam cannot be overruled by route order either.** If any rule in
the registry produced a seam, the answer is ESCALATES — no matter what else the
registry contains or in what order it ran. This is `seam_forces_clash` at the
registry level: the seam facet does not *compete* with the global facets, it
agrees with all of them by construction. -/
theorem run_answer_of_seam (rs : List (Rule I f)) (s : SeamFacet I)
    (h : (some (Facet.seam s) : Rule I f) ∈ rs) : (run rs).answer = some false := by
  have hne : (run rs).seams ≠ [] := by
    intro hnil
    have := (run_seams_nil_iff rs).mp hnil _ h
    exact absurd this (by simp [Facet.asSeam])
  unfold Classification.answer Classification.answerOf
  cases hs : (run rs).seams with
  | nil => exact absurd hs hne
  | cons a t => rfl

end Invariance

/-! ## §5. The seam rule, parametric in the budget

`Spec.budgetSegVerdict` is the tree's worked seam and it is pinned at budget
`10` — `Segmented.budget_not_iconfluent` is stated only there. A `preo` author
writes their own number, so the rule the elaborator tries has to be parametric,
and generalising the clash is the missing half. -/

/-- The two allocations that refute a budget: one replica holds the whole
budget on `true`, the other on `false`, and both spend all of it. -/
def allocL (B : Nat) : Bool → Nat := fun b => if b then B else 0
/-- The mirrored allocation. -/
def allocR (B : Nat) : Bool → Nat := fun b => if b then 0 else B

/-- ⚠ **The budget escalates at every positive budget** — generalising
`Segmented.budget_not_iconfluent` (stated only at `10`) so a `preo` declaration
may name its own number and still reach the seam. Two legal allocations
`B+0` and `0+B` merge to the pointwise max `B+B`, which is over budget as soon
as `B > 0`. At `B = 0` there is nothing to over-spend and the invariant really
is free, so the hypothesis is not slack. -/
theorem budget_not_iconfluent_at (B : Nat) (hB : 0 < B) : ¬ IConfluent (BudgetInv B) := by
  intro h
  have hx : BudgetInv B (allocL B, allocL B) :=
    ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, by show B + 0 = B; omega⟩
  have hy : BudgetInv B (allocR B, allocR B) :=
    ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, by show 0 + B = B; omega⟩
  have hbad := (h (allocL B, allocL B) (allocR B, allocR B) hx hy).2
  revert hbad
  show ¬ (Nat.max B 0 + Nat.max 0 B = B)
  have e1 : Nat.max B 0 = B := Nat.max_zero B
  have e2 : Nat.max 0 B = B := Nat.zero_max B
  rw [e1, e2]
  omega

/-- **The seam verdict at any positive budget** — the rule the elaborator
tries on a `Quota` field. The segmentation half is `Segmented.budget_segmented`
verbatim (it was always parametric); the clash half is
`budget_not_iconfluent_at`'s witness pair, kept rather than existentially
forgotten. At `B = 10` this is `Spec.budgetSegVerdict`, witness for witness. -/
def budgetSeam (B : Nat) (hB : 0 < B) : SegVerdict (BudgetInv B) (Bool → Nat) where
  σ := Prod.fst
  seamFree := budget_segmented B
  x := (allocL B, allocL B)
  y := (allocR B, allocR B)
  hx := ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, by show B + 0 = B; omega⟩
  hy := ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, by show 0 + B = B; omega⟩
  hbad := by
    intro hgood
    have h2 := hgood.2
    revert h2
    show ¬ (Nat.max B 0 + Nat.max 0 B = B)
    have e1 : Nat.max B 0 = B := Nat.max_zero B
    have e2 : Nat.max 0 B = B := Nat.zero_max B
    rw [e1, e2]
    omega

/-- The generalisation really does recover the tree's pinned instance: at
`B = 10` the seam rule and `Spec.budgetSegVerdict` are the **same value** —
same projection, same two replicas. (The proof fields are `Prop`s, so this is
one `rfl` for the whole record.) -/
theorem budgetSeam_ten : budgetSeam 10 (by decide) = budgetSegVerdict := rfl

/-! ## §6. Transporting a field-scale answer to the declared state

A `preo` invariant is earned on one field's carrier and a `derive` computes
from one field, so both need a lift along the projection. `proj_iconfluent`
(`Uwueave.Preo.Syntax` §2) is the confluence half; these are the seam half and
the mergeability half. -/

/-- **A seam lifts along a join-homomorphic projection with a section.** The
segmentation transports along `π` (compose the seam with the projection); the
clash transports by *planting* the field-scale replicas in a document, which is
what needs the section `ι` — `Spec.Verdict.prodClashRight`'s `a`/`ha`, supplied
as a function rather than a hand-built state.

⚠ This is the lemma fragment 1 said it could not have: "transporting a clash
needs a legal value for every other field … which the elaborator cannot
synthesize". It can, from a section: `ι a` is a document whose field reads `a`,
and `π (ι x ⊔ ι y) = x ⊔ y` carries the refutation. What the elaborator must
supply is `ι` and its two equations, and for a `preo` state those are
`fun a => (default, …, a, …, default)` and two `rfl`s. -/
def seamAlong {S T : Type} [MergeState S] [MergeState T] {I : Invariant T}
    {Seg : Type} (π : S → T) (hπ : ∀ x y : S, π (x ⊔ y) = π x ⊔ π y)
    (ι : T → S) (hι : ∀ a, π (ι a) = a) (hιm : ∀ a b, π (ι a ⊔ ι b) = a ⊔ b)
    (s : SegVerdict I Seg) :
    SegVerdict (S := S) (fun d => I (π d)) (Seg) where
  σ := fun d => s.σ (π d)
  seamFree := by
    intro x y hσ hx hy
    have h := s.seamFree (π x) (π y) hσ hx hy
    exact ⟨by show I (π (x ⊔ y)); rw [hπ]; exact h.1,
           by show s.σ (π (x ⊔ y)) = s.σ (π x); rw [hπ]; exact h.2⟩
  x := ι s.x
  y := ι s.y
  hx := by show I (π (ι s.x)); rw [hι]; exact s.hx
  hy := by show I (π (ι s.y)); rw [hι]; exact s.hy
  hbad := by
    intro hgood
    exact s.hbad (by rw [← hιm]; exact hgood)

/-- **A join homomorphism composes with a join homomorphism.** -/
theorem joinHom_comp {S T R : Type} [MergeState S] [MergeState T] [MergeState R]
    {π : S → T} (hπ : JoinHom π) {g : T → R} (hg : JoinHom g) :
    JoinHom (fun s => g (π s)) := by
  intro x y
  show g (π (x ⊔ y)) = g (π x) ⊔ g (π y)
  rw [hπ, hg]

/-- ⚠ **`needsEvidence` survives a surjective projection.** The direction that
needs a hypothesis fragment 1 never had to state: if `g` cannot be merged from
its results, neither can `g ∘ π` — *provided every field value is reachable*.
Without surjectivity this is false in general (a composite can be mergeable on
a proper sub-image while `g` is not), and the elaborator supplies the witness
rather than assuming it. -/
theorem not_incrementallyMergeable_comp {S T R : Type} [MergeState S] [MergeState T]
    {π : S → T} (hπ : JoinHom π) (hsurj : ∀ a : T, ∃ s : S, π s = a)
    {g : T → R} (hg : ¬ IncrementallyMergeable g) :
    ¬ IncrementallyMergeable (fun s => g (π s)) := by
  intro hc
  obtain ⟨m, hm⟩ := hc
  refine hg ⟨m, fun x y => ?_⟩
  obtain ⟨sx, hsx⟩ := hsurj x
  obtain ⟨sy, hsy⟩ := hsurj y
  have h : g (π (sx ⊔ sy)) = m (g (π sx)) (g (π sy)) := hm sx sy
  rw [show π (sx ⊔ sy) = π sx ⊔ π sy from hπ sx sy, hsx, hsy] at h
  exact h

/-- **The mergeability answer transports to the declared state.** Both halves,
and note they need different hypotheses: `fromResults` needs only that the
projection is a homomorphism, `needsEvidence` needs it surjective too. A `preo`
field projection is both (`rfl`, and a document with `default` elsewhere), so
the elaborator can emit this for every derive it classifies. -/
theorem mergeability_comp {S T R : Type} [MergeState S] [MergeState T]
    {π : S → T} (hπ : JoinHom π) (hsurj : ∀ a : T, ∃ s : S, π s = a)
    {g : T → R} {a : JoinHom.Fourth} (h : JoinHom.Fourth.Correct g a) :
    JoinHom.Fourth.Correct (fun s => g (π s)) a := by
  cases a with
  | fromResults =>
    obtain ⟨m, hm⟩ := h
    refine ⟨m, fun x y => ?_⟩
    show g (π (x ⊔ y)) = m (g (π x)) (g (π y))
    rw [show π (x ⊔ y) = π x ⊔ π y from hπ x y]
    exact hm _ _
  | needsEvidence => exact not_incrementallyMergeable_comp hπ hsurj h

end Uwueave.Preo
