/-
# Uwueave.ResultStatus — a DECLARATION is not an EVALUATION.

`Evidence.lean` built the **runtime** half of an epistemic result: five views,
computed from evidence, with the four-witness separation that makes the second
dimension real. This file builds the half it did not, and re-examines the half
it did.

## Origin: codex's P0 #4, and the distinction it turns on

The diagnosis is **codex's**, from its review of this library. In its words, a
declaration `derive verdict : Forked Claim` is ambiguous between *"every
evaluation of this forks"* and *"this evaluation may fork"*, and it means the
second. So a **declaration states a capability** — what a computation *may* do
— while **evaluation returns a status** — what it currently *is*. Two axes.
Conflating them puts a runtime fact in a static position, where it is either
false (a computation that forks only sometimes) or vacuous (a static type that
must admit everything). The credit for the diagnosis is not ours.

Four further claims of codex's are executed here rather than restated: that the
status space has **six** cells and not five (§3); that future-weakening must be
a **theorem** about future inclusion rather than a subtyping rule (§4); that
exactness is frequently **value**-dependent (§5); and that resolution must be
**retained in the type** (§6).

## What §5 of `PREOSCRIPTING.md` got right, and what it did not

| §5 claim | verdict here |
|---|---|
| 5.1 capability (static) vs status (runtime) — two axes | **confirmed**, and built (`Capability`/`Declares` vs `Status`/`statusOf`) |
| 5.1 the declaration is a property of the computation | ⚠ **corrected**: it is a property of the computation **and the state set it is evaluated over** (`declaration_is_relative_to_the_reach`) |
| 5.2 candidates × closure is at least six cells | **confirmed**, and the sixth cell is **genuinely distinguishable** (§3) |
| 5.2 "`Evidence.lean` ships five constructors (`vacuous` … named rather than folded away)" | ⚠ **corrected**: naming is not splitting. The fold is *inside* `vacuous`, and it folds exactly the closure axis §5.2 says matters |
| 5.3 `Exact Working <: Exact Delivered` must come from a theorem | **confirmed**, derived (`exact_weakens`), **and the converse refuted** (`exact_does_not_strengthen`) — §5.3 asserted the direction without exhibiting the invalidity of the other |
| 5.3 exactness is often value-dependent | **confirmed**, both halves proved (§5), and the consequence stated as a theorem rather than a slogan |
| 5.5 `ResolvedBy π α` carries the policy **and the suppressed alternatives** | **confirmed for the policy**; ⚠ **corrected for the alternatives**: they need no field. Indexing the type by the *evidence* retains them by construction (`alternatives_are_retained`) |

## The three results worth reading

**§3 — the sixth cell is real, and the fold is not faithful.** `Evidence.View`
folds "nothing observed yet" and "definitive absence" into `vacuous`, on the
recorded ground that no theorem there needed the distinction. Here is the
theorem that needs it (`sixth_cell_is_distinguishable`): two evidences with the
*same* candidate set — empty — one closed and one not, which `Evidence.render`
sends to the *same* view, and whose rendered answers have **opposite
stability**. At the closed one the rendered answer survives every admissible
extension (`empty_render_final_under_extension`) — a stronger guarantee than
`exact` ever gets, since `exact` is retracted by a roster growth
(`Evidence.render_retracts_when_a_new_source_appears`). At the open one a
sealed future turns `vacuous` into `provisional 47`. So the fold conflates a
final answer with a non-final one — which is precisely the spinner-versus-
prompt distinction that `forkedClosed` was introduced to make on the row above.

`statusOf` splits them, and `forget_statusOf` proves it is a **refinement** and
not a rival: forgetting the split returns `Evidence.render` on the nose.

**§4 — weakening is a theorem, and it does not run backwards.**
`exact_weakens` derives `Exact Flarge → Exact Fsmall` from plain relation
inclusion, with no properties of the futures involved; the delivery ⊆ extension
instance is then one line, at the state level and at `WorldFuture`'s world
level. `Evidence.extension_stable_implies_delivery_stable` is recovered as an
instance of the general law (`evidence_weakening_is_an_instance`) rather than
re-proved. And `exact_does_not_strengthen` refutes the reverse coercion with a
witness: at `openW` taken as its own pool the answer is delivery-exact and
extension-open.

**§5 — one carrier, one query, two values, opposite statuses.** For an
existential over the grow-only candidate set, `true` is self-certifying — it
survives every extension, using nothing but `⊑` (`anyCandidate_true_is_self_
certifying`) — while `false` is retractable at every uncertified obligation
(`anyCandidate_false_stays_open`) and settles exactly at closure
(`closed_settles_every_value_query`). The consequence codex drew is stated as
two refutations rather than as prose: no single status describes the
computation (`existential_has_no_static_finality`), and finality is not a
function of the closure structure either (`finality_is_not_a_function_of_the_
closure_structure`) — the two witnesses have *identical* obligations and
certificates. Four coarse types cannot carry this; one epistemic carrier whose
status is read off the value it holds can.

## Sibling coordination — two different "resolution"s

`Uwueave/HonestRender.lean` (a sibling lane, **not imported here**) owns the
*render-boundary* notion of resolution: what a surface may display, and under
what disclosure. §6 below owns the *type-level* one: `ResolvedBy π e` indexes
the type by the policy term and by the evidence, so neither the choice nor the
fork is erased by resolving. The two are complementary and neither is defined
in terms of the other; if both files define something called "resolution",
these are the two meanings and this is the type-level one.

## Honest boundary

⟨TERMINAL⟩ = a theorem of the model; ⟨UNDONE⟩ = work wearing a caveat's
clothes.

  * **"No branch selection through an implicit coercion" is half-formalised.**
    ⟨UNDONE⟩ What is enforced here is that the value's projection names its
    policy and its evidence: `ResolvedBy π e` has both as indices, so `r.value`
    cannot be written without them, and `resolved_value_is_not_a_function_of_
    the_evidence` proves the projection is genuinely policy-dependent. What is
    **not** built is any statement that an *elaborator* never inserts that
    projection silently — that is a fact about a surface language, and there is
    no surface language.
  * **Visibility is not modelled.** ⟨UNDONE⟩ `PREOSCRIPTING` §5.2 says
    produced-but-uninspectable is an independent axis rather than a seventh
    cell. Nothing here contradicts that and nothing here builds it: the six
    cells are candidates × closure only.
  * **`Capability` remains three flags; the general effect lattice is shipped.**
    ⟨HISTORICAL LIMIT, DISCHARGED BY `StatusEffects`⟩
    `StatusEffects.Shape` retains all six cells and `StatusEffects.Effect` is a
    downward-closed set under their refinement order, with bottom, top, meet,
    join and distributivity laws. `StatusEffects.fromLegacy_matches` embeds
    this hand-written `Capability.Admits` table exactly. The embedding is
    strict: `StatusEffects.correlated_effect_has_no_legacy_encoding` exhibits
    a capability that permits provisional singletons and closed forks while
    rejecting open forks, a correlation no assignment of the three independent
    flags can express.
  * **`statusOf` is noncomputable.** ⟨TERMINAL at this carrier⟩ Inherited
    verbatim from `Evidence.render`: both decisions quantify over an unbounded
    value type. `Classical.choice` is inside the audit floor.
  * **Finite-reach declarations are inferred; arbitrary reach remains open.**
    ⟨UNDONE at running/arbitrary reach and surface integration⟩ `Declares`
    here is still a proposition a proof discharges. For an explicitly supplied
    finite list of states, `StatusEffects.infer` now returns the downward
    closure of the observed six-way shapes, and `infer_is_least` proves both
    support and leastness. It does not discover the states a running system can
    reach, infer over an unbounded reach predicate, or install that inference
    in the surface elaborator.
  * **The reach set is a hypothesis.** ⟨TERMINAL for the refutation, ⟨UNDONE⟩
    as deployment⟩ `declaration_is_relative_to_the_reach` shows a declaration
    that holds over one state set fails over a wider one. Which states a
    running system actually reaches is `WorldFuture.lean`'s question about
    wellformedness, and it is not answered there either.
-/
import Uwueave.WorldFuture

namespace Uwueave.ResultStatus

open Uwueave Uwueave.Catalog

/-! ## §1. The runtime status — six cells, not five.

`PREOSCRIPTING` §5.2's table, in full:

| candidates | open                  | closed                |
|------------|-----------------------|-----------------------|
| zero       | `pending`             | `absent`              |
| one        | `provisional a`       | `exact a`             |
| many       | `forkedOpen`          | `forkedClosed`        |

`Evidence.View` has the four of the lower two rows and one `vacuous` for the
top row. §3 proves the missing split is not decoration; this section only
defines the type and the refinement map. -/

/-- **The runtime status of a result position** — the full candidates × closure
product. Four constructors are `Evidence.View`'s; the two zero-candidate ones
are the split this file is about. -/
inductive Status (α : Type) : Type where
  /-- One candidate, future closed: `47`. -/
  | exact (a : α)
  /-- One candidate, future open: `47 + ⟨pending⟩`. -/
  | provisional (a : α)
  /-- Several candidates, future closed: waiting will not fix it. -/
  | forkedClosed
  /-- Several candidates, future open. -/
  | forkedOpen
  /-- **Zero candidates, future closed: definitive absence.** There is no
  answer and there will not be one. -/
  | absent
  /-- **Zero candidates, future open: nothing observed yet.** There is no
  answer *so far*. -/
  | pending

/-- Which of the six points a status is, as a numeral. Only ever used to tell
two constructors apart; it carries no meaning of its own. -/
def statusTag {α : Type} : Status α → Nat
  | .exact _ => 0
  | .provisional _ => 1
  | .forkedClosed => 2
  | .forkedOpen => 3
  | .absent => 4
  | .pending => 5

/-- Statuses with different tags are different statuses. -/
theorem status_ne_of_tag {α : Type} {a b : Status α} (h : statusTag a ≠ statusTag b) :
    a ≠ b := fun heq => h (congrArg statusTag heq)

open Classical in
/-- **The status.** `Evidence.render`'s three-way case on the candidates, with
the closure split applied to **all three** rows instead of two. Noncomputable
for `render`'s reason: both decisions quantify over an unbounded type. -/
noncomputable def statusOf {α : Type} (e : Evidence.ResultEvidence α) : Status α :=
  if hu : ∃ a, Evidence.values e a = true ∧ ∀ b, Evidence.values e b = true → b = a then
    (if Evidence.Closed e then Status.exact (Classical.choose hu)
     else Status.provisional (Classical.choose hu))
  else if ∃ a, Evidence.values e a = true then
    (if Evidence.Closed e then Status.forkedClosed else Status.forkedOpen)
  else (if Evidence.Closed e then Status.absent else Status.pending)

/-- **The fold `Evidence.View` performs**: the two zero-candidate statuses go to
one point. Everything else is carried across unchanged. -/
def forget {α : Type} : Status α → Evidence.View α
  | .exact a => .exact a
  | .provisional a => .provisional a
  | .forkedClosed => .forkedClosed
  | .forkedOpen => .forkedOpen
  | .absent => .vacuous
  | .pending => .vacuous

/-- **`statusOf` is a refinement of `render`, not a rival.** Forgetting the
zero-row split returns `Evidence.render` on the nose, at every evidence. So
nothing in `Evidence.lean` is contradicted or restated: this file adds one
distinction to a function that is otherwise the same function. -/
theorem forget_statusOf {α : Type} (e : Evidence.ResultEvidence α) :
    forget (statusOf e) = Evidence.render e := by
  by_cases hu : ∃ a, Evidence.values e a = true ∧ ∀ b, Evidence.values e b = true → b = a
  · by_cases hc : Evidence.Closed e
    · rw [statusOf, dif_pos hu, if_pos hc, Evidence.render, dif_pos hu, if_pos hc]
      rfl
    · rw [statusOf, dif_pos hu, if_neg hc, Evidence.render, dif_pos hu, if_neg hc]
      rfl
  · by_cases hne : ∃ a, Evidence.values e a = true
    · by_cases hc : Evidence.Closed e
      · rw [statusOf, dif_neg hu, if_pos hne, if_pos hc, Evidence.render, dif_neg hu,
          if_pos hne, if_pos hc]
        rfl
      · rw [statusOf, dif_neg hu, if_pos hne, if_neg hc, Evidence.render, dif_neg hu,
          if_pos hne, if_neg hc]
        rfl
    · by_cases hc : Evidence.Closed e
      · rw [statusOf, dif_neg hu, if_neg hne, if_pos hc, Evidence.render, dif_neg hu,
          if_neg hne]
        rfl
      · rw [statusOf, dif_neg hu, if_neg hne, if_neg hc, Evidence.render, dif_neg hu,
          if_neg hne]
        rfl

/-! ### The six inversion lemmas

Each says which evidence produces which status. They are `Evidence.lean`'s
`render_*` lemmas with the zero row split; the four non-empty ones are proved
the same way, and the two new ones are what §3 needs. -/

theorem statusOf_exact {α : Type} {e : Evidence.ResultEvidence α} {a : α}
    (hm : Evidence.values e a = true) (hs : Holes.SealsTo (Evidence.values e) a)
    (hc : Evidence.Closed e) : statusOf e = Status.exact a := by
  have hu : ∃ x, Evidence.values e x = true ∧ ∀ b, Evidence.values e b = true → b = x :=
    ⟨a, hm, hs⟩
  have hch := Classical.choose_spec hu
  have heq : Classical.choose hu = a := hs _ hch.1
  simp only [statusOf, dif_pos hu, if_pos hc, heq]

theorem statusOf_provisional {α : Type} {e : Evidence.ResultEvidence α} {a : α}
    (hm : Evidence.values e a = true) (hs : Holes.SealsTo (Evidence.values e) a)
    (hc : ¬ Evidence.Closed e) : statusOf e = Status.provisional a := by
  have hu : ∃ x, Evidence.values e x = true ∧ ∀ b, Evidence.values e b = true → b = x :=
    ⟨a, hm, hs⟩
  have hch := Classical.choose_spec hu
  have heq : Classical.choose hu = a := hs _ hch.1
  simp only [statusOf, dif_pos hu, if_neg hc, heq]

theorem statusOf_forkedClosed {α : Type} {e : Evidence.ResultEvidence α} {a b : α}
    (ha : Evidence.values e a = true) (hb : Evidence.values e b = true) (hab : a ≠ b)
    (hc : Evidence.Closed e) : statusOf e = Status.forkedClosed := by
  simp only [statusOf, dif_neg (Evidence.not_unique_of_two ha hb hab),
    if_pos (show ∃ x, Evidence.values e x = true from ⟨a, ha⟩), if_pos hc]

theorem statusOf_forkedOpen {α : Type} {e : Evidence.ResultEvidence α} {a b : α}
    (ha : Evidence.values e a = true) (hb : Evidence.values e b = true) (hab : a ≠ b)
    (hc : ¬ Evidence.Closed e) : statusOf e = Status.forkedOpen := by
  simp only [statusOf, dif_neg (Evidence.not_unique_of_two ha hb hab),
    if_pos (show ∃ x, Evidence.values e x = true from ⟨a, ha⟩), if_neg hc]

/-- No candidates and a closed future: **definitive absence**. -/
theorem statusOf_absent {α : Type} {e : Evidence.ResultEvidence α}
    (h : ∀ a, Evidence.values e a = false) (hc : Evidence.Closed e) :
    statusOf e = Status.absent := by
  have hne : ¬ ∃ a, Evidence.values e a = true := by
    rintro ⟨a, ha⟩
    rw [h a] at ha
    exact Bool.noConfusion ha
  have hnu : ¬ ∃ a, Evidence.values e a = true ∧ ∀ b, Evidence.values e b = true → b = a := by
    rintro ⟨a, ha, _⟩
    exact hne ⟨a, ha⟩
  simp only [statusOf, dif_neg hnu, if_neg hne, if_pos hc]

/-- No candidates and an open future: **nothing observed yet**. -/
theorem statusOf_pending {α : Type} {e : Evidence.ResultEvidence α}
    (h : ∀ a, Evidence.values e a = false) (hc : ¬ Evidence.Closed e) :
    statusOf e = Status.pending := by
  have hne : ¬ ∃ a, Evidence.values e a = true := by
    rintro ⟨a, ha⟩
    rw [h a] at ha
    exact Bool.noConfusion ha
  have hnu : ¬ ∃ a, Evidence.values e a = true ∧ ∀ b, Evidence.values e b = true → b = a := by
    rintro ⟨a, ha, _⟩
    exact hne ⟨a, ha⟩
  simp only [statusOf, dif_neg hnu, if_neg hne, if_neg hc]

/-! ## §2. The static axis — a capability, and what it declares.

Codex's split, executed. A `Capability` is what a *declaration* may say; a
`Status` is what an *evaluation* returns; and `Declares` is the only bridge
between them — a proposition, quantified over the states the computation is
evaluated at.

The quantifier is the content. `Declares c Reach peval` is **not** a property
of `peval` alone, and §2's last theorem is that the same evaluator satisfies
the same declaration over one reach set and violates it over a wider one. So
"this computation may fork" is a claim about a computation *and a state space*,
which `PREOSCRIPTING` §5.1 does not say. -/

/-- **A declared capability.** Three flags: whether the computation may produce
no answer, whether its answer may still be open, whether it may fork. -/
structure Capability where
  /-- The computation may return zero candidates. -/
  mayBeEmpty : Bool
  /-- The computation's answer may still be open — evidence may still arrive. -/
  mayOpen : Bool
  /-- The computation may return several incompatible candidates. -/
  mayFork : Bool

/-- **Which statuses a capability admits.** `exact` needs no permission — it is
the status every declaration is willing to receive. Everything else costs a
flag, and the two open×{zero,many} corners cost both of theirs. -/
def Capability.Admits {α : Type} (c : Capability) : Status α → Prop
  | .exact _ => True
  | .provisional _ => c.mayOpen = true
  | .forkedClosed => c.mayFork = true
  | .forkedOpen => c.mayFork = true ∧ c.mayOpen = true
  | .absent => c.mayBeEmpty = true
  | .pending => c.mayBeEmpty = true ∧ c.mayOpen = true

/-- **The declaration.** An evaluator's possible statuses lie within its
declared capability — at every state it may be evaluated at. `Reach` is that
state set, and it is a parameter because the claim is false without it. -/
def Declares {S β : Type} (c : Capability) (Reach : S → Prop)
    (peval : S → Status β) : Prop :=
  ∀ s, Reach s → c.Admits (peval s)

/-- **The declaration soundness theorem.** A declaration that forbids forking is
**refutable** on a computation that forks anywhere in its reach: not merely
unproved, but false, and the fork witness is the refutation. -/
theorem no_fork_declaration_is_refutable {S β : Type} {c : Capability}
    {Reach : S → Prop} {peval : S → Status β} (hc : c.mayFork = false)
    {s : S} (hs : Reach s)
    (hfork : peval s = Status.forkedClosed ∨ peval s = Status.forkedOpen) :
    ¬ Declares c Reach peval := by
  intro hd
  have h := hd s hs
  rcases hfork with hf | hf <;> rw [hf] at h
  · exact Bool.noConfusion (hc.symm.trans h)
  · exact Bool.noConfusion (hc.symm.trans h.1)

/-- The same, for a declaration that forbids an open answer. -/
theorem no_open_declaration_is_refutable {S β : Type} {c : Capability}
    {Reach : S → Prop} {peval : S → Status β} (hc : c.mayOpen = false)
    {s : S} {v : β} (hs : Reach s) (hprov : peval s = Status.provisional v) :
    ¬ Declares c Reach peval := by
  intro hd
  have h := hd s hs
  rw [hprov] at h
  exact Bool.noConfusion (hc.symm.trans h)

/-- **Declarations weaken along future inclusion**, exactly as exactness does
(§4): a capability discharged over the larger future set is discharged over the
smaller one. The reach set is `F s` — the states reachable from `s` under the
named future — so the two axes meet here and nowhere else. -/
theorem declares_weakens {S β : Type} {c : Capability}
    {Fsmall Flarge : Evidence.Future S} (hinc : ∀ s t, Fsmall s t → Flarge s t)
    {peval : S → Status β} {s : S} (h : Declares c (Flarge s) peval) :
    Declares c (Fsmall s) peval :=
  fun t ht => h t (hinc s t ht)

/-! ### Both sides inhabited — one satisfied declaration, one violated

`Evidence.lean`'s own witnesses, evaluated by `statusOf`. -/

theorem statusOf_exactW : statusOf Evidence.exactW = Status.exact 47 :=
  statusOf_exact (Evidence.values_cand47 (e := Evidence.exactW) rfl).1
    (Evidence.values_cand47 (e := Evidence.exactW) rfl).2 Evidence.closed_exactW

theorem statusOf_openW : statusOf Evidence.openW = Status.provisional 47 :=
  statusOf_provisional (Evidence.values_cand47 (e := Evidence.openW) rfl).1
    (Evidence.values_cand47 (e := Evidence.openW) rfl).2 Evidence.not_closed_openW

theorem statusOf_forkedClosedW : statusOf Evidence.forkedClosedW = Status.forkedClosed :=
  statusOf_forkedClosed (Evidence.values_cand4749 (e := Evidence.forkedClosedW) rfl).1
    (Evidence.values_cand4749 (e := Evidence.forkedClosedW) rfl).2 (by decide)
    Evidence.closed_forkedClosedW

theorem statusOf_forkedOpenW : statusOf Evidence.forkedOpenW = Status.forkedOpen :=
  statusOf_forkedOpen (Evidence.values_cand4749 (e := Evidence.forkedOpenW) rfl).1
    (Evidence.values_cand4749 (e := Evidence.forkedOpenW) rfl).2 (by decide)
    Evidence.not_closed_forkedOpenW

theorem not_closed_openForkW : ¬ Evidence.Closed Evidence.openForkW := by
  intro h
  exact Bool.noConfusion (h Evidence.bob (by decide))

theorem statusOf_openForkW : statusOf Evidence.openForkW = Status.forkedOpen :=
  statusOf_forkedOpen (Evidence.values_cand4749 (e := Evidence.openForkW) rfl).1
    (Evidence.values_cand4749 (e := Evidence.openForkW) rfl).2 (by decide)
    not_closed_openForkW

/-- The declaration an interface makes when it promises *one value, possibly
still pending, never a fork* — the common case, and the one `derive verdict :
Claim` means when nobody writes a modality. -/
def mayPend : Capability := { mayBeEmpty := false, mayOpen := true, mayFork := false }

/-- The states a replica reaches before `bob` has spoken. -/
def reachSettled : Evidence.ResultEvidence Holes.Val → Prop :=
  fun e => e = Evidence.exactW ∨ e = Evidence.openW

/-- The same states, plus the one where `bob` — still owed, uncertified —
contributes `49`. This is `Evidence.openW_extends_to_openForkW`'s target: a
state the first reach set omits and the future permits. -/
def reachWithFork : Evidence.ResultEvidence Holes.Val → Prop :=
  fun e => e = Evidence.exactW ∨ e = Evidence.openW ∨ e = Evidence.openForkW

/-- **A satisfied declaration.** Over `reachSettled`, `mayPend` holds: the
statuses are `exact 47` and `provisional 47`, and `mayOpen` pays for the
second. -/
theorem declaration_satisfied : Declares mayPend reachSettled statusOf := by
  rintro e (rfl | rfl)
  · rw [statusOf_exactW]; trivial
  · rw [statusOf_openW]; rfl

/-- ⚠ **A violated declaration — the SAME evaluator and the SAME capability.**
One more reachable state, and `mayPend` is refuted, because `openForkW` has
status `forkedOpen`. -/
theorem declaration_violated : ¬ Declares mayPend reachWithFork statusOf :=
  no_fork_declaration_is_refutable (c := mayPend) rfl
    (Or.inr (Or.inr rfl)) (Or.inr statusOf_openForkW)

/-- ⚠ **A CAPABILITY IS RELATIVE TO A REACH SET.** The two theorems above, as
one statement: the same evaluator, the same declaration, satisfied over one set
of states and refuted over a wider one — and the wider one is not exotic, it is
the first reach set closed under a single admissible extension
(`Evidence.openW_extends_to_openForkW`).

So `PREOSCRIPTING` §5.1's reading — the declaration states what *the
computation* may do — is not quite the right shape. A declaration states what a
computation may do **over a state space**, and a language that lets one be
written without the other has hidden the quantifier that makes it false. -/
theorem declaration_is_relative_to_the_reach :
    Declares mayPend reachSettled statusOf
      ∧ ¬ Declares mayPend reachWithFork statusOf
      ∧ (∀ e, reachSettled e → reachWithFork e)
      ∧ Evidence.ExtensionFuture Evidence.openW Evidence.openForkW :=
  ⟨declaration_satisfied, declaration_violated,
   fun _ h => h.imp id Or.inl, Evidence.openW_extends_to_openForkW⟩

/-! ## §3. THE SIXTH CELL — distinguishable, and the fold is not faithful.

The question `PREOSCRIPTING` §5.2 raises and `Evidence.lean` §4 explicitly
declined ("this file does not split it, because no theorem below needs the
distinction"): are *nothing observed yet* and *definitive absence* two facts or
one?

**Two.** And the separation is not a matter of taste about constructors — it is
a **stability** difference, of exactly the kind that justified `forkedClosed` on
the row above. Two evidences with the identical (empty) candidate set:

  * `emptyClosedW` — closed. Its rendered answer survives **every** admissible
    extension future, which is more than `exact` gets: an `exact` report is
    retracted by a roster growth (`Evidence.render_retracts_when_a_new_source_
    appears`) and an `absent` one is not, because there is no value to move.
  * `emptyOpenW` — open at `bob`. A *sealed* future — the future for which
    `Evidence.render` is sound — turns its `vacuous` into `provisional 47`.

`Evidence.render` sends both to `View.vacuous`. So a consumer switching on the
view alone cannot tell a final answer from a non-final one: it is the spinner
and the prompt again, one row up. -/

/-- No candidates at all. -/
def candNone : GSet (Holes.Val × Evidence.Source) := fun _ => false

/-- One candidate, `47`, attributed to `bob` — who is owed and uncertified in
the witnesses below, which is what makes the arrival admissible. -/
def cand47bob : GSet (Holes.Val × Evidence.Source) :=
  fun p => decide (p = (47, Evidence.bob))

/-- **Definitive absence.** No candidates, and `alice` — the only source owed —
is certified: nothing can arrive, so there is no answer and there will not be
one. -/
def emptyClosedW : Evidence.ResultEvidence Holes.Val :=
  (candNone, Evidence.srcsA, Evidence.srcsA)

/-- **Nothing observed yet.** The same empty candidate set, but `bob` is still
owed: there is no answer *so far*. -/
def emptyOpenW : Evidence.ResultEvidence Holes.Val :=
  (candNone, Evidence.srcsAB, Evidence.srcsA)

/-- `bob` speaks: the sealed future of `emptyOpenW` in which `47` arrives. -/
def bobSpokeW : Evidence.ResultEvidence Holes.Val :=
  (cand47bob, Evidence.srcsAB, Evidence.srcsA)

theorem values_candNone {e : Evidence.ResultEvidence Holes.Val}
    (h : Evidence.candidates e = candNone) (a : Holes.Val) :
    Evidence.values e a = false := by
  cases hb : Evidence.values e a with
  | false => rfl
  | true =>
    obtain ⟨o, ho⟩ := (Evidence.mem_values e a).mp hb
    rw [h] at ho
    exact Bool.noConfusion (show (false : Bool) = true from ho)

theorem mem_cand47bob {b : Holes.Val} {o : Evidence.Source}
    (h : cand47bob (b, o) = true) : b = 47 ∧ o = Evidence.bob := by
  have := of_decide_eq_true h
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem values_cand47bob {e : Evidence.ResultEvidence Holes.Val}
    (h : Evidence.candidates e = cand47bob) :
    Evidence.values e 47 = true ∧ Holes.SealsTo (Evidence.values e) 47 := by
  constructor
  · exact (Evidence.mem_values e 47).mpr ⟨Evidence.bob, by rw [h]; decide⟩
  · intro b hb
    obtain ⟨o, ho⟩ := (Evidence.mem_values e b).mp hb
    rw [h] at ho
    exact (mem_cand47bob ho).1

theorem closed_emptyClosedW : Evidence.Closed emptyClosedW := fun _ h => h

theorem not_closed_emptyOpenW : ¬ Evidence.Closed emptyOpenW := by
  intro h
  exact Bool.noConfusion (h Evidence.bob (by decide))

theorem not_closed_bobSpokeW : ¬ Evidence.Closed bobSpokeW := by
  intro h
  exact Bool.noConfusion (h Evidence.bob (by decide))

/-- **The two zero-candidate cells are inhabited and separated by `statusOf`.**
Same candidate set — empty — and different statuses. -/
theorem statusOf_emptyClosedW : statusOf emptyClosedW = Status.absent :=
  statusOf_absent (values_candNone (e := emptyClosedW) rfl) closed_emptyClosedW

theorem statusOf_emptyOpenW : statusOf emptyOpenW = Status.pending :=
  statusOf_pending (values_candNone (e := emptyOpenW) rfl) not_closed_emptyOpenW

theorem render_emptyClosedW : Evidence.render emptyClosedW = Evidence.View.vacuous :=
  Evidence.render_vacuous (values_candNone (e := emptyClosedW) rfl)

theorem render_emptyOpenW : Evidence.render emptyOpenW = Evidence.View.vacuous :=
  Evidence.render_vacuous (values_candNone (e := emptyOpenW) rfl)

theorem render_bobSpokeW : Evidence.render bobSpokeW = Evidence.View.provisional 47 :=
  Evidence.render_provisional (values_cand47bob (e := bobSpokeW) rfl).1
    (values_cand47bob (e := bobSpokeW) rfl).2 not_closed_bobSpokeW

/-- **DEFINITIVE ABSENCE IS FINAL UNDER THE FULL EXTENSION FUTURE.** A closed,
empty evidence renders `vacuous` at every admissible extension — no roster
growth, no new source, no arriving event moves it.

This is strictly stronger than what `exact` enjoys. `Evidence.render_retracts_
when_a_new_source_appears` shows an `exact 47` re-opening to `provisional 47`
when a source nobody knew about is admitted; the empty answer has no value to
re-open, so the retraction cannot touch it. Absence is the most stable cell of
the six, and it is the one the five-constructor view folded away. -/
theorem empty_render_final_under_extension {α : Type} {e : Evidence.ResultEvidence α}
    (hempty : ∀ a, Evidence.values e a = false) (hc : Evidence.Closed e) :
    Evidence.FreeTermination Evidence.ExtensionFuture Evidence.render e := by
  intro t ht
  have hval : Evidence.values t = Evidence.values e :=
    Evidence.values_congr (Evidence.closed_freezes hc ht.1 ht.2)
  have ht' : ∀ a, Evidence.values t a = false := fun a => by rw [hval]; exact hempty a
  rw [Evidence.render_vacuous ht', Evidence.render_vacuous hempty]

/-- …and the *status* is final too, though only for the sealed future: the
candidate set is frozen either way, but the `absent`/`pending` split reads
`Closed`, and a roster growth re-opens that. See `absence_survives_values_not_
closure` for the price stated as a witness. -/
theorem empty_status_final_under_sealed {α : Type} {e : Evidence.ResultEvidence α}
    (hempty : ∀ a, Evidence.values e a = false) (hc : Evidence.Closed e) :
    Evidence.FreeTermination Evidence.SealedFuture (statusOf (α := α)) e := by
  intro t ht
  obtain ⟨hval, hct⟩ := Evidence.sealed_future_of_closed hc ht
  have ht' : ∀ a, Evidence.values t a = false := fun a => by rw [hval]; exact hempty a
  rw [statusOf_absent ht' hct, statusOf_absent hempty hc]

theorem emptyOpenW_seals_to_bobSpokeW : Evidence.SealedFuture emptyOpenW bobSpokeW := by
  refine ⟨⟨?_, ?_⟩, fun _ h => h⟩
  · refine Evidence.leq_of_components ?_ (leq_refl _) (leq_refl _)
    refine (Holes.gset_leq_iff_subset _ _).mpr (fun p hp => ?_)
    exact Bool.noConfusion (show (false : Bool) = true from hp)
  · intro p _ h2
    have hp : p = (47, Evidence.bob) := of_decide_eq_true h2
    rw [hp]
    exact ⟨by decide, by decide⟩

/-- ⚠ **THE SIXTH CELL IS GENUINELY DISTINGUISHABLE.** Two evidences with the
same (empty) candidate set:

  * `Evidence.render` sends **both** to `vacuous` — the fold;
  * `statusOf` sends them to `absent` and `pending` — the split;
  * and the rendered answers have **opposite stability**: at the closed one it
    survives every extension future, at the open one it does not survive even a
    sealed one.

So the fold is **not faithful**. `Evidence.lean` §4 recorded that it declined
the split "because no theorem below needs the distinction" — true of that file,
and this is the theorem that needs it. A `vacuous` badge is a spinner and a
`vacuous` badge is a prompt, and the type cannot say which. -/
theorem sixth_cell_is_distinguishable :
    Evidence.render emptyClosedW = Evidence.View.vacuous
      ∧ Evidence.render emptyOpenW = Evidence.View.vacuous
      ∧ statusOf emptyClosedW = Status.absent
      ∧ statusOf emptyOpenW = Status.pending
      ∧ Evidence.FreeTermination Evidence.ExtensionFuture Evidence.render emptyClosedW
      ∧ ¬ Evidence.FreeTermination Evidence.SealedFuture Evidence.render emptyOpenW := by
  refine ⟨render_emptyClosedW, render_emptyOpenW, statusOf_emptyClosedW,
    statusOf_emptyOpenW,
    empty_render_final_under_extension (values_candNone (e := emptyClosedW) rfl)
      closed_emptyClosedW, ?_⟩
  intro hft
  have h := hft bobSpokeW emptyOpenW_seals_to_bobSpokeW
  rw [render_bobSpokeW, render_emptyOpenW] at h
  exact absurd h (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

/-- ⚠ **AND THE COMPARISON, AS A THEOREM RATHER THAN A BOAST.** `render` is
final at `emptyClosedW` under the full extension future and is **not** final at
`exactW` under the same future — because a source nobody had heard of re-opens
an `exact` report (`Evidence.exactW_extends_to_openW`) and has nothing to
re-open at an empty one.

So the cell the five-constructor view folded away is the *most* stable of the
six, which is an odd thing for a fold to have chosen. -/
theorem absence_outlives_exactness :
    Evidence.FreeTermination Evidence.ExtensionFuture Evidence.render emptyClosedW
      ∧ ¬ Evidence.FreeTermination Evidence.ExtensionFuture Evidence.render
            Evidence.exactW := by
  refine ⟨empty_render_final_under_extension (values_candNone (e := emptyClosedW) rfl)
    closed_emptyClosedW, ?_⟩
  intro hft
  have h := hft Evidence.openW Evidence.exactW_extends_to_openW
  rw [Evidence.four_states_inhabited.2.1, Evidence.four_states_inhabited.1] at h
  exact absurd h (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

theorem emptyClosedW_extends_to_emptyOpenW :
    Evidence.ExtensionFuture emptyClosedW emptyOpenW := by
  constructor
  · refine Evidence.leq_of_components (leq_refl _) ?_ (leq_refl _)
    refine (Holes.gset_leq_iff_subset _ _).mpr (fun o h => ?_)
    exact decide_eq_true (Or.inl (of_decide_eq_true h))
  · intro p h1 h2
    exact Bool.noConfusion (h1.symm.trans h2)

/-- ⚠ **And the price of the split, paid in public.** The *value* content of
definitive absence is immovable, but the *closure claim* is not: admit one
source nobody had heard of and `absent` re-opens to `pending`, with an
identical (empty) candidate set. This is exactly `Evidence.render_retracts_when
_a_new_source_appears` at the zero row — the same defect, the same cause (an
open source set), and the same remedy (`SealedFuture`, where
`empty_status_final_under_sealed` holds).

Stating it here is the point: the sixth cell is worth having *and* it inherits
the retraction its neighbours have. It is not a free constructor. -/
theorem absence_survives_values_not_closure :
    Evidence.ExtensionFuture emptyClosedW emptyOpenW
      ∧ Evidence.candidates emptyOpenW = Evidence.candidates emptyClosedW
      ∧ statusOf emptyClosedW = Status.absent
      ∧ statusOf emptyOpenW = Status.pending
      ∧ ¬ Evidence.SealedFuture emptyClosedW emptyOpenW := by
  refine ⟨emptyClosedW_extends_to_emptyOpenW, rfl, statusOf_emptyClosedW,
    statusOf_emptyOpenW, ?_⟩
  intro h
  exact Bool.noConfusion (h.2 Evidence.bob (by decide))

/-! ## §4. FUTURE WEAKENING AS A THEOREM.

`PREOSCRIPTING` §2 and §5.3: *"That subtyping direction should be a theorem the
language derives, never a rule it asserts."* Here it is derived, and its
converse is refuted so that the direction is earned rather than chosen.

`Exact F answer s v` is the library's own notion, read off
`Evidence.CanonicalEvaluator.complete`'s hypothesis and `Evidence.exact_sound`'s
conclusion: at every `F`-future of `s` the answer is still exactly `v`. The
weakening needs **no property of the futures at all** — only relation
inclusion — which is what makes it a theorem rather than a rule. -/

/-- One future relation is contained in another. `delivery ⊆ extension` is the
instance everything below is aimed at. -/
def FutureIncluded {S : Type} (Fsmall Flarge : Evidence.Future S) : Prop :=
  ∀ s t, Fsmall s t → Flarge s t

/-- **Exactness, indexed by a future.** At every `F`-future of `s`, the answer
is `v` and nothing but `v`. `Exact Delivered α` and `Exact Working α` are this
at two relations. -/
def Exact {S β : Type} (F : Evidence.Future S) (answer : S → GSet β) (s : S)
    (v : β) : Prop :=
  ∀ t, F s t → answer t v = true ∧ Holes.SealsTo (answer t) v

/-- **THE WEAKENING THEOREM.** Surviving the larger future set implies
surviving the smaller — from relation inclusion alone, at any carrier, for any
answer function. This is the coercion `Exact Working <: Exact Delivered`, and
it is a one-line consequence of a containment rather than a rule anyone chose. -/
theorem exact_weakens {S β : Type} {Fsmall Flarge : Evidence.Future S}
    (hinc : FutureIncluded Fsmall Flarge) {answer : S → GSet β} {s : S} {v : β}
    (h : Exact Flarge answer s v) : Exact Fsmall answer s v :=
  fun t ht => h t (hinc s t ht)

/-- The same for state-relative finality — `Evidence.FreeTermination` weakens
along inclusion too, and by the same argument. -/
theorem freeTermination_weakens {S β : Type} {Fsmall Flarge : Evidence.Future S}
    (hinc : FutureIncluded Fsmall Flarge) {q : S → β} {s : S}
    (h : Evidence.FreeTermination Flarge q s) :
    Evidence.FreeTermination Fsmall q s :=
  fun t ht => h t (hinc s t ht)

/-- Delivery ⊆ extension, at the state level: `Evidence.delivery_is_extension`
packaged as an inclusion. -/
theorem delivery_included_in_extension {α : Type}
    (pool : Evidence.ResultEvidence α) :
    FutureIncluded (Evidence.DeliveryFuture pool) (Evidence.ExtensionFuture (α := α)) :=
  fun _ _ h => Evidence.delivery_is_extension h

/-- Sealed ⊆ extension: a sealed future is an extension future with a closed
source set. -/
theorem sealed_included_in_extension {α : Type} :
    FutureIncluded (Evidence.SealedFuture (α := α)) Evidence.ExtensionFuture :=
  fun _ _ h => h.1

/-- Delivery ⊆ extension at the **world** level too — `WorldFuture.lean`'s
containment, so the weakening theorem instantiates where futures are indexed by
worlds rather than states, which is where `PREOSCRIPTING` §5.4 says they belong. -/
theorem world_delivery_included_in_extension {α : Type} :
    FutureIncluded (WorldFuture.DeliveryFuture (α := α)) WorldFuture.ExtensionFuture :=
  fun _ _ h => WorldFuture.delivery_is_extension h

/-- **The instantiation asked for**: exactness under the extension future
implies exactness under delivery, at any pool. -/
theorem exact_delivery_of_exact_extension {α : Type}
    {pool s : Evidence.ResultEvidence α} {v : Holes.Val}
    {answer : Evidence.ResultEvidence α → GSet Holes.Val}
    (h : Exact Evidence.ExtensionFuture answer s v) :
    Exact (Evidence.DeliveryFuture pool) answer s v :=
  exact_weakens (delivery_included_in_extension pool) h

/-- **`Evidence.extension_stable_implies_delivery_stable` is an instance of the
general law** — recovered, not re-proved. The library already had the
implication at one pair of futures; what §4 adds is that the implication never
depended on which pair. -/
theorem evidence_weakening_is_an_instance {α β : Type}
    {q : Evidence.ResultEvidence α → β} {pool s : Evidence.ResultEvidence α}
    (h : Evidence.FreeTermination Evidence.ExtensionFuture q s) :
    Evidence.FreeTermination (Evidence.DeliveryFuture pool) q s :=
  freeTermination_weakens (delivery_included_in_extension pool) h

/-- …and the world-level one likewise. -/
theorem world_weakening_is_an_instance {α β : Type} {q : WorldFuture.World α → β}
    {w : WorldFuture.World α}
    (h : Evidence.FreeTermination WorldFuture.ExtensionFuture q w) :
    Evidence.FreeTermination WorldFuture.DeliveryFuture q w :=
  freeTermination_weakens world_delivery_included_in_extension h

/-- Non-vacuity for the pair below: `openW` taken as its own pool **has** a
delivery future — itself — so `exact_delivery_at_openW` quantifies over an
inhabited relation and is not exactness by absence of futures. -/
theorem delivery_at_openW_inhabited :
    Evidence.DeliveryFuture Evidence.openW Evidence.openW Evidence.openW :=
  ⟨leq_refl _, leq_refl _, Evidence.admits_refl _⟩

theorem exact_delivery_at_openW :
    Exact (Evidence.DeliveryFuture Evidence.openW) Evidence.values Evidence.openW 47 := by
  intro t ht
  have heq : Evidence.openW = t := leq_antisymm ht.1 ht.2.1
  subst heq
  exact Evidence.values_cand47 (e := Evidence.openW) rfl

theorem not_exact_extension_at_openW :
    ¬ Exact Evidence.ExtensionFuture Evidence.values Evidence.openW 47 := by
  intro h
  have hs := (h Evidence.openForkW Evidence.openW_extends_to_openForkW).2
  have h49 := (Evidence.values_cand4749 (e := Evidence.openForkW) rfl).2
  exact absurd (hs 49 h49) (by decide)

/-- ⚠ **THE CONVERSE IS INVALID, WITH A WITNESS.** Delivery is contained in
extension; at `openW` taken as its own pool the answer is delivery-exact; and
it is **not** extension-exact, because `bob` — owed and uncertified — may still
say `49`.

So the subtyping runs one way and one way only, and the direction is earned:
`exact_weakens` proves it in the valid direction and this refutes the other at
the same pair of futures. Together they are `PREOSCRIPTING` §2's "the futures
are nested, and the reverse coercion is invalid", with the second half now
carrying a witness instead of an assertion. -/
theorem exact_does_not_strengthen :
    FutureIncluded (Evidence.DeliveryFuture Evidence.openW)
        (Evidence.ExtensionFuture (α := Holes.Val))
      ∧ Evidence.DeliveryFuture Evidence.openW Evidence.openW Evidence.openW
      ∧ Exact (Evidence.DeliveryFuture Evidence.openW) Evidence.values Evidence.openW 47
      ∧ ¬ Exact Evidence.ExtensionFuture Evidence.values Evidence.openW 47 :=
  ⟨delivery_included_in_extension Evidence.openW, delivery_at_openW_inhabited,
   exact_delivery_at_openW, not_exact_extension_at_openW⟩

/-! ## §5. VALUE-DEPENDENT EXACTNESS.

Codex's sharpest observation, and the argument for one epistemic carrier rather
than four coarse types: *for an existential over a grow-only set, `true` is
self-certifying while `false` stays open until closure.*

Both halves are proved, at the strongest available future in each direction:

  * the positive at `ExtensionFuture` — the **largest** future set, so the
    guarantee is as strong as it can be. It uses nothing but `⊑`: growth cannot
    retract a witness that already exists;
  * the negative at `SealedFuture` — the **smallest** of the three, and the one
    for which `Evidence.render` is sound, so the refutation is as strong as it
    can be. It transports up to `ExtensionFuture` through §4's weakening rather
    than being re-proved.

And closure is exactly what settles the negative half
(`closed_settles_every_value_query`), which is what "until closure" means. -/

theorem truth_false {p : Prop} (h : ¬ p) : Holes.truth p = false := by
  cases hb : Holes.truth p with
  | false => rfl
  | true => exact absurd (Holes.truth_eq_true.mp hb) h

/-- "Some member of this answer set satisfies `p`" — an existential over a
grow-only set, as a query on the *values*. -/
noncomputable def anyIn {α : Type} (p : α → Bool) (P : Holes.Partial α) : Bool :=
  Holes.truth (∃ a, P a = true ∧ p a = true)

/-- The same query at the evidence carrier: it reads the candidate values and
nothing else, which is why closure settles it. -/
noncomputable def anyCandidate {α : Type} (p : α → Bool)
    (e : Evidence.ResultEvidence α) : Bool :=
  anyIn p (Evidence.values e)

/-- **`true` IS SELF-CERTIFYING.** Once some candidate satisfies `p`, no
permitted future retracts it — at the *extension* future, the largest one, and
with **no closure hypothesis whatsoever**. The proof uses only `s ⊑ t`: a
grow-only set never loses the witness it already has.

This is the half that makes a static status assignment impossible. The answer
is final and the evidence is wide open. -/
theorem anyCandidate_true_is_self_certifying {α : Type} (p : α → Bool)
    {e : Evidence.ResultEvidence α} (h : anyCandidate p e = true) :
    Evidence.FreeTermination Evidence.ExtensionFuture (anyCandidate p) e := by
  intro t ht
  obtain ⟨a, ha, hp⟩ := Holes.truth_eq_true.mp h
  obtain ⟨o, ho⟩ := (Evidence.mem_values e a).mp ha
  have hgrow : Evidence.values t a = true :=
    (Evidence.mem_values t a).mpr ⟨o, Evidence.candidates_grow ht.1 ho⟩
  rw [h]
  exact Holes.truth_eq_true.mpr ⟨a, hgrow, hp⟩

/-- ⚠ **`false` STAYS OPEN.** At any uncertified obligation, and for any value
`p` accepts, there is a **sealed** future — no new source, only an arrival from
a source already owed — in which the answer flips to `true`. So a `false` is
never final while anything is owed.

Sealed is the smallest of the three futures, so `¬ FreeTermination` here gives
`¬ FreeTermination` at extension too, through §4 (`freeTermination_weakens`,
contrapositive). -/
theorem anyCandidate_false_stays_open {α : Type} [DecidableEq α] (p : α → Bool)
    {e : Evidence.ResultEvidence α} {a : α} {o : Evidence.Source}
    (hfalse : anyCandidate p e = false) (hp : p a = true)
    (ho : Evidence.obligations e o = true) (hcert : Evidence.certificates e o = false) :
    ¬ Evidence.FreeTermination Evidence.SealedFuture (anyCandidate p) e := by
  intro hft
  have hle : e ⊑ (Evidence.candidates e ⊔ Delta.addDelta (a, o), Evidence.obligations e,
      Evidence.certificates e) :=
    Evidence.leq_of_components (le_merge_left _ _) (leq_refl _) (leq_refl _)
  have hadm : Evidence.Admits e (Evidence.candidates e ⊔ Delta.addDelta (a, o),
      Evidence.obligations e, Evidence.certificates e) := by
    intro q h1 h2
    have h3 : (Evidence.candidates e q || Delta.addDelta (a, o) q) = true := h2
    rw [h1, Bool.false_or] at h3
    have hq : q = (a, o) := of_decide_eq_true h3
    rw [hq]
    exact ⟨ho, hcert⟩
  have hmem : Evidence.values (Evidence.candidates e ⊔ Delta.addDelta (a, o),
      Evidence.obligations e, Evidence.certificates e) a = true := by
    refine (Evidence.mem_values _ a).mpr ⟨o, ?_⟩
    show (Evidence.candidates e (a, o) || Delta.addDelta (a, o) (a, o)) = true
    rw [show Delta.addDelta (a, o) (a, o) = true from by simp [Delta.addDelta]]
    exact Bool.or_true _
  have htrue : anyCandidate p (Evidence.candidates e ⊔ Delta.addDelta (a, o),
      Evidence.obligations e, Evidence.certificates e) = true :=
    Holes.truth_eq_true.mpr ⟨a, hmem, hp⟩
  have hstep := hft _ (⟨⟨hle, hadm⟩, fun _ h => h⟩ : Evidence.SealedFuture e _)
  rw [htrue, hfalse] at hstep
  exact Bool.noConfusion hstep

/-- **Closure settles it — whatever the value.** Any query that reads only the
candidate *values* is final at a closed evidence, under the full extension
future, because `Evidence.closed_freezes` says the candidate set cannot move.
This is the "until closure" in codex's sentence, as a theorem: closure is
sufficient, and `anyCandidate_false_stays_open` says nothing weaker is. -/
theorem closed_settles_every_value_query {α β : Type} (q : Holes.Partial α → β)
    {e : Evidence.ResultEvidence α} (hc : Evidence.Closed e) :
    Evidence.FreeTermination Evidence.ExtensionFuture
      (fun s => q (Evidence.values s)) e := by
  intro t ht
  show q (Evidence.values t) = q (Evidence.values e)
  rw [Evidence.values_congr (Evidence.closed_freezes hc ht.1 ht.2)]

theorem closed_settles_anyCandidate {α : Type} (p : α → Bool)
    {e : Evidence.ResultEvidence α} (hc : Evidence.Closed e) :
    Evidence.FreeTermination Evidence.ExtensionFuture (anyCandidate p) e :=
  closed_settles_every_value_query (anyIn p) hc

/-! ### The witness pair — identical closure structure, opposite finality -/

/-- The query: *did anyone say `49`?* -/
def isFortyNine : Holes.Val → Bool := fun a => decide (a = 49)

theorem anyCandidate_openForkW : anyCandidate isFortyNine Evidence.openForkW = true :=
  Holes.truth_eq_true.mpr
    ⟨49, (Evidence.values_cand4749 (e := Evidence.openForkW) rfl).2, by decide⟩

theorem anyCandidate_openW : anyCandidate isFortyNine Evidence.openW = false := by
  refine truth_false ?_
  rintro ⟨a, ha, hp⟩
  obtain ⟨o, ho⟩ := (Evidence.mem_values Evidence.openW a).mp ha
  have ho' : Evidence.cand47 (a, o) = true := ho
  have h47 : a = 47 := (Evidence.mem_cand47 ho').1
  rw [h47] at hp
  exact Bool.noConfusion hp

theorem not_final_anyCandidate_openW :
    ¬ Evidence.FreeTermination Evidence.SealedFuture
        (anyCandidate isFortyNine) Evidence.openW :=
  anyCandidate_false_stays_open isFortyNine (a := 49) (o := Evidence.bob)
    anyCandidate_openW (by decide) (by decide) (by decide)

/-- ⚠ **EXACTNESS IS VALUE-DEPENDENT.** One query, two evidences with
**identical** obligations and **identical** certificates — the entire closure
structure agrees — and opposite finality, decided by nothing but which value
the candidate set currently holds.

`openForkW` holds `49`, so the existential is `true` and immovable under every
extension. `openW` does not, so it is `false` and a sealed future flips it.
There is no closure fact separating them, because there is none to find. -/
theorem exactness_is_value_dependent :
    Evidence.obligations Evidence.openW = Evidence.obligations Evidence.openForkW
      ∧ Evidence.certificates Evidence.openW = Evidence.certificates Evidence.openForkW
      ∧ anyCandidate isFortyNine Evidence.openForkW = true
      ∧ Evidence.FreeTermination Evidence.ExtensionFuture
          (anyCandidate isFortyNine) Evidence.openForkW
      ∧ anyCandidate isFortyNine Evidence.openW = false
      ∧ ¬ Evidence.FreeTermination Evidence.SealedFuture
          (anyCandidate isFortyNine) Evidence.openW :=
  ⟨rfl, rfl, anyCandidate_openForkW,
   anyCandidate_true_is_self_certifying isFortyNine anyCandidate_openForkW,
   anyCandidate_openW, not_final_anyCandidate_openW⟩

/-! ### The consequence, as two refutations

Codex's conclusion — *a declaration cannot assign ONE status to the
computation* — is stated as theorems, because as prose it is the kind of claim
that survives being wrong. -/

/-- The two witness states, as a reach set. -/
def twoStates : Evidence.ResultEvidence Holes.Val → Prop :=
  fun e => e = Evidence.openW ∨ e = Evidence.openForkW

/-- **A static finality verdict**: the declaration says the computation is
final, or says it is not, once, for the whole reach set. This is the shape
`derive verdict : Exact Claim` / `derive verdict : Open Claim` has — four
coarse types, each a constant claim about every evaluation. -/
def StaticallyFinal {S : Type} (F : Evidence.Future S) (q : S → Bool)
    (Reach : S → Prop) : Prop :=
  (∀ s, Reach s → Evidence.FreeTermination F q s)
    ∨ (∀ s, Reach s → ¬ Evidence.FreeTermination F q s)

/-- ⚠ **NO STATIC STATUS DESCRIBES AN EXISTENTIAL.** Neither constant verdict
survives: the computation is final at one reachable state and not at another.

This is the argument for **one epistemic carrier over four coarse types**. A
type-level status is a constant, and the status of this computation is not a
constant — it is a function of the value the evidence currently holds. A
carrier that reports the status per evaluation can say this; four types, one of
which must be chosen at declaration time, cannot. -/
theorem existential_has_no_static_finality :
    ¬ StaticallyFinal Evidence.SealedFuture (anyCandidate isFortyNine) twoStates := by
  rintro (hall | hnone)
  · exact not_final_anyCandidate_openW (hall Evidence.openW (Or.inl rfl))
  · exact hnone Evidence.openForkW (Or.inr rfl)
      (freeTermination_weakens sealed_included_in_extension
        (anyCandidate_true_is_self_certifying isFortyNine anyCandidate_openForkW))

/-- ⚠ **AND FINALITY IS NOT A FUNCTION OF THE CLOSURE STRUCTURE EITHER.** The
weaker retreat — *keep the two axes, but let the declaration read the frontier
and the certificates* — fails too, and at the same witnesses: `openW` and
`openForkW` have equal obligations and equal certificates, so any such function
answers the same at both, and the truth does not.

Same shape as `WorldFuture.delivery_stability_is_not_state_indexed`, one level
down: there the missing information was the pool, here it is the value. -/
theorem finality_is_not_a_function_of_the_closure_structure :
    ¬ ∃ f : GSet Evidence.Source × GSet Evidence.Source → Bool,
        ∀ e : Evidence.ResultEvidence Holes.Val,
          f (Evidence.obligations e, Evidence.certificates e) = true
            ↔ Evidence.FreeTermination Evidence.SealedFuture
                (anyCandidate isFortyNine) e := by
  rintro ⟨f, hf⟩
  have hfork : f (Evidence.obligations Evidence.openForkW,
      Evidence.certificates Evidence.openForkW) = true :=
    (hf Evidence.openForkW).mpr
      (freeTermination_weakens sealed_included_in_extension
        (anyCandidate_true_is_self_certifying isFortyNine anyCandidate_openForkW))
  exact not_final_anyCandidate_openW ((hf Evidence.openW).mp hfork)

/-! ## §6. RESOLUTION, RETAINED IN THE TYPE.

`PREOSCRIPTING` §5.5: *"You cannot silently collapse a fork" is right; "you
cannot ever pick one" is wrong.* The enforceable property is that no branch
selection happens through an implicit coercion — so resolution is explicit and
retained.

`ResolvedBy π e` indexes the type by **both** the policy term and the evidence.
That is where the retention lives:

  * the **policy** is an index, so a resolved value's type names the rule that
    produced it;
  * the **alternatives** need no field — the evidence is an index too, so the
    full candidate set is recoverable from the type
    (`alternatives_are_retained`). §5.5's "carrying the policy and the
    suppressed alternatives" over-specified: one of the two is free.

And retention is **load-bearing**, not decoration: two policies on the same
forked evidence disagree, so the value is not a function of the evidence
(`resolved_value_is_not_a_function_of_the_evidence`). Erase the policy and you
have erased something no later reader can reconstruct.

⚠ Sibling coordination: `Uwueave/HonestRender.lean` owns the *render-boundary*
notion of resolution (what a surface may display, and under what disclosure).
This is the *type-level* one. Neither file imports the other and neither is
defined in terms of the other. -/

/-- **A resolution policy**: a rule that selects one candidate from evidence, or
declines. Partiality is real — a policy that names a source has nothing to say
about evidence that source never contributed to. -/
abbrev Policy (α : Type) : Type := Evidence.ResultEvidence α → Option α

open Classical in
/-- **Resolve by source** — the policy family `resolve verdict by era_order`
belongs to: take the candidate attributed to a named source. Noncomputable for
`Evidence.render`'s reason; the choice is classical, the *policy* is not
implicit. -/
noncomputable def bySource {α : Type} (o : Evidence.Source) : Policy α := fun e =>
  if h : ∃ a, Evidence.candidates e (a, o) = true then some (Classical.choose h) else none

/-- **A resolved value keeps what produced it.** `π` and `e` are indices of the
type, so the term cannot exist without naming the policy that chose and the
evidence it chose from. -/
structure ResolvedBy {α : Type} (π : Policy α) (e : Evidence.ResultEvidence α) : Type where
  /-- The selected value. -/
  value : α
  /-- …and the proof that the named policy selected it. -/
  chosen : π e = some value

/-- **The alternatives are retained by construction.** No field is needed: the
evidence is an index, so the full candidate set is a projection of the type.
A resolved fork is still a fork. -/
noncomputable def ResolvedBy.alternatives {α : Type} {π : Policy α}
    {e : Evidence.ResultEvidence α} (_ : ResolvedBy π e) : Holes.Partial α :=
  Evidence.values e

theorem alternatives_are_retained {α : Type} {π : Policy α}
    {e : Evidence.ResultEvidence α} (r : ResolvedBy π e) :
    r.alternatives = Evidence.values e := rfl

theorem bySource_alice_forkedClosedW :
    bySource Evidence.alice Evidence.forkedClosedW = some 47 := by
  have h : ∃ a, Evidence.candidates Evidence.forkedClosedW (a, Evidence.alice) = true :=
    ⟨47, by decide⟩
  have hs := Classical.choose_spec h
  have heq : Classical.choose h = 47 := by
    rcases of_decide_eq_true (show Evidence.cand4749 (Classical.choose h, Evidence.alice)
        = true from hs) with h1 | h1
    · exact congrArg Prod.fst h1
    · exact absurd (show Evidence.alice = Evidence.bob from congrArg Prod.snd h1)
        (by decide)
  rw [bySource, dif_pos h, heq]

theorem bySource_bob_forkedClosedW :
    bySource Evidence.bob Evidence.forkedClosedW = some 49 := by
  have h : ∃ a, Evidence.candidates Evidence.forkedClosedW (a, Evidence.bob) = true :=
    ⟨49, by decide⟩
  have hs := Classical.choose_spec h
  have heq : Classical.choose h = 49 := by
    rcases of_decide_eq_true (show Evidence.cand4749 (Classical.choose h, Evidence.bob)
        = true from hs) with h1 | h1
    · exact absurd (show Evidence.bob = Evidence.alice from congrArg Prod.snd h1)
        (by decide)
    · exact congrArg Prod.fst h1
  rw [bySource, dif_pos h, heq]

/-- `alice`'s reading of the closed fork. -/
noncomputable def resolvedAlice :
    ResolvedBy (bySource Evidence.alice) Evidence.forkedClosedW :=
  ⟨47, bySource_alice_forkedClosedW⟩

/-- `bob`'s reading of the **same** closed fork. -/
noncomputable def resolvedBob :
    ResolvedBy (bySource Evidence.bob) Evidence.forkedClosedW :=
  ⟨49, bySource_bob_forkedClosedW⟩

/-- **Two policies, one forked evidence, different answers.** The fork is the
one `Evidence.lean` names `forkedClosedW`: waiting will not fix it, so the
disagreement is not a timing artifact. -/
theorem policies_disagree_on_a_fork : resolvedAlice.value ≠ resolvedBob.value := by
  show (47 : Holes.Val) ≠ 49
  decide

/-- ⚠ **RETENTION IS LOAD-BEARING.** There is **no** function from evidence to
value that every resolution agrees with: the two witnesses above have the same
evidence and different values. So a design that drops the policy after
resolving — keeping only `α` — has destroyed information that cannot be
recovered from what it kept, and `ResolvedBy π e`'s policy index is doing work
rather than decorating a type. -/
theorem resolved_value_is_not_a_function_of_the_evidence :
    ¬ ∃ f : Evidence.ResultEvidence Holes.Val → Holes.Val,
        ∀ (π : Policy Holes.Val) (e : Evidence.ResultEvidence Holes.Val)
          (r : ResolvedBy π e), r.value = f e := by
  rintro ⟨f, hf⟩
  exact policies_disagree_on_a_fork
    ((hf _ _ resolvedAlice).trans (hf _ _ resolvedBob).symm)

/-- **Resolution does not touch the evidence.** The status of the underlying
result position is what it was before anyone resolved: a `forkedClosed` that
`alice`'s policy read as `47` is still a `forkedClosed`. Selection is a
*reading*, and the reading is stored beside the fork rather than in place of
it. -/
theorem resolution_leaves_the_status_alone :
    statusOf Evidence.forkedClosedW = Status.forkedClosed
      ∧ resolvedAlice.alternatives = Evidence.values Evidence.forkedClosedW
      ∧ resolvedBob.alternatives = Evidence.values Evidence.forkedClosedW :=
  ⟨statusOf_forkedClosedW, rfl, rfl⟩

end Uwueave.ResultStatus
