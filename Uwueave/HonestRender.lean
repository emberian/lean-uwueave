/-
# Uwueave.HonestRender — a UI cannot silently present uncertain data as certain.

`PREOSCRIPTING.md` §8 says the epistemic status of a value determines its
widget, and lists **three enforceable properties and one honest limit**. It says
them in prose. This file makes them theorems, and exhibits the dishonest
renderer each one forbids — because a property nothing can violate is not a
property.

## Origin: codex's second review

The four items are **codex's**, from the second external review of this library
(the first produced `Evidence.lean`'s two corrections; the second produced
`WorldFuture.lean`'s world-indexing). In its words, restated as §8's list:

  1. **No exact badge without a stability certificate.**
  2. **No singular extraction from a possible fork without a named policy.**
  3. **No "fully synchronized" status without naming the scope it is relative
     to.**
  4. ⚠ **Types enforce semantic *presence*, not *salience*.** A correctly typed
     `OpenForked` can still be rendered as one-pixel grey text below the fold.
     "So keep constructors abstract, expose total eliminators, require every
     status to be handled, and make exact badges consume certificates."

The diagnosis and the remedy sketch are codex's; the execution and the
refutations are this file's.

### What was achieved, item by item — read this before citing the file

  * **(1) — ACHIEVED.** `renderedExact_implies_stable` (§4): an honest
    renderer's `exact v` report *is* a `StabilityCert`, i.e. `v` is the answer
    at every future the named relation permits. `readCertified` (§3) is the only
    answer-honest route from a result to a bare `α`, and it takes the
    certificate as an argument. Refuted implementation: `eagerRender` (§7).
  * **(2) — ACHIEVED, half of it by reuse.** `no_honest_projection` (§3) — over
    the *abstract* eliminator interface, so it holds for every implementation —
    is the render-boundary half, and it is exactly what `ResultStatus.lean`'s
    boundary names as unbuilt there. The type-level half is **that file's**:
    `ResultStatus.ResolvedBy π e`, indexed by the policy term and the evidence,
    with `policies_disagree_on_a_fork` and
    `resolved_value_is_not_a_function_of_the_evidence`.
    `singularSelection_implies_namedPolicy` (§5) joins them. Refuted
    implementation: `silentValue` (§7), which applies that file's own policy and
    drops its name.
  * **(3) — ACHIEVED, and mostly inherited.** The future is an index of the
    carrier (`Result F α`) and this file's `StabilityCert` **is**
    `ResultStatus.Exact`, so the coercion between scopes is that file's
    `exact_weakens` (derived from relation inclusion, never a subtyping rule —
    §5.3's requirement) and the invalidity of the other direction is its
    `exact_does_not_strengthen`, witnessed at `Evidence.openW`. Neither is
    restated here. What is new is the **site** index:
    `worldSited_renderer_honest` (§6) instantiates the carrier at
    `WorldFuture.World`, and `state_sited_certificates_refuse_openW` says why
    that is not optional. The residue: nothing here forces a *renderer* to
    display the scope's name — that is item (4) again.
  * **(4) — the limit is TERMINAL, and a proxy is proved.**
    `salience_is_not_enforceable`: a consumer that supplies all five handlers
    may still return the same `β` for every one of them, and it goes through the
    eliminator like any other. That is not a defect to be repaired; it is what
    a type is. The *proxy* codex proposed — "require every status to be handled,
    no default branch" — is `every_status_slot_is_load_bearing`
    (§2): change any one of the five handlers and some result observes the
    change. Presence is enforced; prominence is not; both halves are theorems.

## Why an abstract INTERFACE and not a `private` constructor

Codex's remedy begins "keep constructors abstract". Lean's `private` is a
*module* mechanism: it stops a sibling file naming `Result.view`, and it stops
nothing at all inside this file, where `Result.rec` and structure eta are both
available. A discipline that holds only because nobody typed the other thing is
a naming convention.

So the theorems below are stated over `Carrier F α` (§1): a carrier type, a
report constructor, a site projection, a specification relation `Says`, and a
**five-handler eliminator with one law** (`elim_spec`) pinning it to the
five-way dispatch. A consumer holding only a `Carrier` cannot see a
constructor, because there is nothing to see — that is quantification, not
scoping. `stdCarrier` (§1) inhabits the interface so nothing below is a fact
about an empty class, and `Result` marks `ofParts` and `view` `private`, so no
sibling module can *name* them — but that is hygiene, and the enforcement is
`no_honest_projection`, which holds for every implementation whatsoever.

⚠ And `report` is deliberately **public**: a renderer must be able to say
`exact`, including one that should not. Honesty is therefore a predicate on
*renderers* (§4), which is exactly what makes §7's two dishonest
implementations exhibitable and this module refutable. A type that could not
express the lie could not refuse it either.

## The refutable implementations — the falsifiability bar

  * ⚠ `eagerRender` (§7) reports `exact` on a unique candidate **without
    reading the closure**. It is *correct where it is made*
    (`eagerRender_correct`) and it is not irrevocable: `openW` renders
    `exact 47`, and the sealed future `openForkW` — `bob`, still owed,
    contributes `49` — makes that false. So it is not an
    `Evidence.SoundEvaluator` and not an honest renderer, and the badge it
    prints is a promise about a future it never consulted.
  * ⚠ `silentValue` (§7) is a total `Result → Holes.Val` that applies
    `ResultStatus.bySource alice` to the site's evidence and then **drops the
    policy**. It type-checks. At the *closed* fork `forkedClosedW` — waiting
    will not fix it — it returns `47` while `49` is equally supported, and
    `no_honest_projection` says no function of that type is answer-honest.
    `silent_and_named_agree` is the sharp form: it computes **the same number**
    as `ResultStatus.resolvedAlice.value`, so what the type retains is not the
    number — it is that `bySource bob` would have said `49`.

## Sibling coordination — and one deliberate correction to it

`Uwueave/ResultStatus.lean` (committed before this file) carries a note saying
the two files' notions of "resolution" are complementary and that *"neither is
defined in terms of the other"*. The first half stands: that file owns the
**type-level** notion, this one owns the **render-boundary** notion, and the
two questions are different. ⚠ The second half is corrected here, in one
direction and on purpose: this file **imports** `ResultStatus` and reuses its
`Policy`, `ResolvedBy` and `Exact` rather than defining its own. A second
`ResolvedBy` in one library is two shapes that agree today and disagree later,
and the render-boundary theorems lose nothing by being stated over the
committed one. `ResultStatus` still imports nothing from here.

## Honest boundary

⟨TERMINAL⟩ = a theorem of the model; ⟨UNDONE U-0081⟩ = work wearing a caveat's clothes.

  * **Salience is not typable.** ⟨TERMINAL⟩ `salience_is_not_enforceable` is the
    statement, and no strengthening of the interface removes it: a presentation
    is a function out of the result, and constant functions exist. What is
    enforceable is that the five handlers be *supplied* and that each be
    *observable*; whether the pixels differ is outside every type system, not
    outside this one.
  * **`report` is public, so a lie is constructible.** ⟨TERMINAL for this file's
    question, ⟨UNDONE U-0082⟩ as deployment⟩ Honesty is a predicate on renderers, not a
    property of the carrier. A deployment that wants the *type* to refuse must
    export `renderReport` and not `report`; nothing here enforces that, and no
    theorem below assumes it.
  * **The eliminator is five-way, and the sixth cell is a sibling's.**
    ⟨DONE downstream in `Uwueave.RenderSix`⟩
    `ResultStatus.sixth_cell_is_distinguishable` proves that
    `Evidence.View.vacuous` folds two states with *opposite* stability —
    "nothing observed yet" and "definitive absence". `dispatch` and
    `Carrier.elim` are over `Evidence.View` because `Evidence.SoundEvaluator`
    and `exact_sound` — §4's seed — are stated there. So a consumer of this
    carrier handles five statuses, not six, and a surface built on it cannot
    tell a spinner from "there is no answer". This file intentionally retains
    that five-way carrier. `RenderSix.Carrier6`, `statusOf_sound6`, and
    `the_named_limit_is_retired` implement and prove the six-way successor while
    preserving the exact fold back to this carrier.
  * **The eliminator is `Type 0`-valued.** ⟨UNDONE U-0083⟩ `Carrier.elim` eliminates
    into `Type`; a `Prop`-valued consumer goes through `Says`, and
    `Classical.choice` can turn `says_total` into a projection. So the barrier
    against extraction is `no_honest_projection` — a statement about what such a
    function can *mean* — and never the absence of one.
  * **The future index is phantom in the data.** ⟨UNDONE U-0084⟩ `Result F α` mentions
    `F` in its type and in every honesty statement, and
    `ResultStatus.exact_does_not_strengthen` prices dropping it. Nothing
    prevents a `cast` between `Result F α` and `Result G α`; the index is a
    discipline the theorems reward, not one the kernel enforces.
  * **The checked adapter binds the report site to the evaluated state;
    the observation premise is explicit downstream.**
    ⟨DONE downstream in `Uwueave.Preo.ResultProgram`⟩
    `CheckedReport.site_exact` and `refuses_wrong_site` bind a checked report to
    its evaluated state. `ObservedReport` then retains a caller-supplied
    `ObservationBoundary.Authentic` proof. The remaining deployment question is
    centralized at that boundary; this five-status carrier does not restate it.
  * **Disclosure is explicitly and totally decided downstream.**
    ⟨DONE downstream in `Uwueave.Preo.ResultProgram`⟩ The alternatives still
    survive resolution by `ResultStatus.alternatives_are_retained`.
    `ResultProgram.SurfacePolicy.disclosure : S → β → Disclosure` additionally
    makes a named shown/hidden decision for every value at every site;
    `CheckedReport.renderAt_disclosure` projects it exactly and
    `refuses_wrong_disclosure` rejects a contradictory claim. This types the
    decision, not its eventual pixel salience.
  * **Obligations become authorization-carrying affordances downstream.**
    ⟨DONE downstream in `Uwueave.RenderProgress`⟩ `DischargeOffer` retains the
    resulting state, actor, delegation and revocation sets, a proof of
    `Authority.Active`, a permitted-future proof, and proof that the action
    leaves `pending`. `statusOf_pendingActionable` constructs the offer only
    from live authority, while `a_revoked_actor_gets_no_button` rejects the
    same affordance after revocation.
  * **The empirical claim of §8 is untouched.** ⟨UNDONE U-0085⟩ *That a recurring class
    of local-first UI misrepresentations consists of unproved coercions from
    open/forked evidence to exact singular presentation* needs a defect corpus
    and a coding protocol. This file proves the coercions are unsound; it says
    nothing about how often they occur.
  * **Noncomputability is inherited.** ⟨TERMINAL at this carrier⟩
    `Evidence.values`, `Evidence.render` and `eagerRender` all quantify over an
    unbounded value type. `Classical.choice` is inside the audit floor.
-/
import Uwueave.ResultStatus

namespace Uwueave.HonestRender

open Uwueave Uwueave.Catalog

/-! ## §1. The carrier — a five-handler dispatch, and one law that pins it.

`dispatch` is the specification: the five-way case analysis on
`Evidence.View α`, written once. `Carrier F α` is the interface a consumer
gets — a carrier type `R`, a way to *make* a report, the site it was made at,
a `Says` relation saying which view a report carries, and an eliminator
`elim` whose only law is that it **is** `dispatch` on that view.

Two things follow immediately and are the point of the shape:

  * a consumer holding a `Carrier` has no constructor to match on, because the
    interface exposes none — this is quantification, not `private`;
  * `elim_spec` leaves no room for a default branch: whatever `elim` does, it
    does one of the five handlers, and §2 shows all five are reachable.

The future `F` is an index of the carrier and appears in no field. That is
deliberate and it is priced in §6: it is load-bearing in every honesty
statement, and `ResultStatus.exact_does_not_strengthen` shows a certificate
that forgets it is false. -/

/-- **The five-handler dispatch.** The specification of any total eliminator
for `Evidence.View`: one handler per constructor, and no default case to write.
⚠ Five, not six — `ResultStatus.Status` splits `vacuous`, and the boundary says
what that costs a surface built on this carrier. -/
def dispatch {α β : Type} (onExact onProvisional : α → β)
    (onForkedClosed onForkedOpen onVacuous : β) : Evidence.View α → β
  | .exact a => onExact a
  | .provisional a => onProvisional a
  | .forkedClosed => onForkedClosed
  | .forkedOpen => onForkedOpen
  | .vacuous => onVacuous

/-- **A result carrier for the future `F`.** A type of results, a report
constructor, the site a report was made at, the specification relation `Says`,
and a total five-handler eliminator pinned to `dispatch` by `elim_spec`.

`site` is public on purpose: `WorldFuture.lean` proves an exactness certificate
that escapes its world is a true statement filed under the wrong key, so the
situation a report was made at travels *with* the report. `Says` is `Prop`-
valued and is the specification, not an extraction route. -/
structure Carrier {S : Type} (F : Evidence.Future S) (α : Type) : Type 1 where
  /-- The type of results. A consumer sees this and the fields below; it does
  not see a constructor, because the interface does not have one. -/
  R : Type
  /-- Make a report of a view at a site. Public: a renderer must be able to
  speak, including dishonestly (§7). -/
  report : S → Evidence.View α → R
  /-- The situation the report was made at. -/
  site : R → S
  /-- The specification: which view this result carries. -/
  Says : R → Evidence.View α → Prop
  /-- **The total eliminator.** Five handlers, one per status. -/
  elim : {β : Type} → R → (α → β) → (α → β) → β → β → β → β
  /-- A report is made at the site it was given. -/
  site_report : ∀ s v, site (report s v) = s
  /-- A report says the view it was made with. -/
  says_report : ∀ s v, Says (report s v) v
  /-- A result says at most one view. -/
  says_functional : ∀ r v v', Says r v → Says r v' → v = v'
  /-- A result says at least one view — so `elim` never has nothing to do. -/
  says_total : ∀ r, ∃ v, Says r v
  /-- **The eliminator IS the dispatch.** No default branch is expressible,
  because there is no behaviour left for one to have. -/
  elim_spec : ∀ {β : Type} (r : R) (v : Evidence.View α) (onExact onProvisional : α → β)
    (onForkedClosed onForkedOpen onVacuous : β), Says r v →
    elim r onExact onProvisional onForkedClosed onForkedOpen onVacuous
      = dispatch onExact onProvisional onForkedClosed onForkedOpen onVacuous v

/-- **The reference result type.** A site and a view, with the view `private`
so that no *other* module can project it. The module boundary is real; it is
not what enforces anything (see the header) — `no_honest_projection` is. -/
structure Result {S : Type} (F : Evidence.Future S) (α : Type) : Type where
  private ofParts ::
  /-- The situation this report was made at. Public: a certificate carries its
  world. -/
  site : S
  private view : Evidence.View α

/-- **The interface is inhabited.** `Result` with the obvious operations
satisfies every law, so nothing stated over `Carrier` is a fact about an empty
class. -/
def stdCarrier {S : Type} (F : Evidence.Future S) (α : Type) : Carrier F α where
  R := Result F α
  report := fun s v => Result.ofParts s v
  site := Result.site
  Says := fun r v => r.view = v
  elim := fun r onE onP onFC onFO onV => dispatch onE onP onFC onFO onV r.view
  site_report := fun _ _ => rfl
  says_report := fun _ _ => rfl
  says_functional := fun _ _ _ h h' => h ▸ h'
  says_total := fun r => ⟨r.view, rfl⟩
  elim_spec := fun _ _ _ _ _ _ _ h => by rw [← h]

/-- At the reference carrier, `Says` on a fresh report is view equality. The
handle every concrete witness below uses. -/
theorem std_says {S α : Type} (F : Evidence.Future S) (s : S)
    (v v' : Evidence.View α) :
    (stdCarrier F α).Says ((stdCarrier F α).report s v) v' ↔ v = v' := Iff.rfl

/-! ## §2. The eliminator is total, and every slot of it is load-bearing.

Three facts, in the order they are needed:

  * **total** — every result says a view, and on that view `elim` is the
    dispatch, so there is no result on which the eliminator has nothing to
    return and none on which it returns something the five handlers did not
    (`elim_total`);
  * **complete** — *every* consumer `f : C.R → β` agrees, at each site, with an
    `elim` built from its own five branch behaviours (`consumers_factor`). This
    is the semantic form of "the constructors are not public": however a
    consumer was written, it is a five-handler dispatch;
  * **no default branch** — change any one of the five handlers and some result
    observes the change (`every_status_slot_is_load_bearing`). This is the
    checkable proxy codex proposed for the salience limit, and §8 is where it is
    read against what it does *not* buy. -/

variable {S α : Type} {F : Evidence.Future S}

/-- `elim` on a fresh report is the dispatch on the view it was made with. -/
theorem elim_report {β : Type} (C : Carrier F α) (s : S) (v : Evidence.View α)
    (onE onP : α → β) (onFC onFO onV : β) :
    C.elim (C.report s v) onE onP onFC onFO onV = dispatch onE onP onFC onFO onV v :=
  C.elim_spec _ v onE onP onFC onFO onV (C.says_report s v)

/-- The `exact` computation rule. -/
theorem elim_exact {β : Type} (C : Carrier F α) (s : S) (a : α)
    (onE onP : α → β) (onFC onFO onV : β) :
    C.elim (C.report s (Evidence.View.exact a)) onE onP onFC onFO onV = onE a :=
  elim_report C s _ onE onP onFC onFO onV

/-- The `provisional` computation rule. -/
theorem elim_provisional {β : Type} (C : Carrier F α) (s : S) (a : α)
    (onE onP : α → β) (onFC onFO onV : β) :
    C.elim (C.report s (Evidence.View.provisional a)) onE onP onFC onFO onV = onP a :=
  elim_report C s _ onE onP onFC onFO onV

/-- The `forkedClosed` computation rule. -/
theorem elim_forkedClosed {β : Type} (C : Carrier F α) (s : S)
    (onE onP : α → β) (onFC onFO onV : β) :
    C.elim (C.report s Evidence.View.forkedClosed) onE onP onFC onFO onV = onFC :=
  elim_report C s _ onE onP onFC onFO onV

/-- The `forkedOpen` computation rule. -/
theorem elim_forkedOpen {β : Type} (C : Carrier F α) (s : S)
    (onE onP : α → β) (onFC onFO onV : β) :
    C.elim (C.report s Evidence.View.forkedOpen) onE onP onFC onFO onV = onFO :=
  elim_report C s _ onE onP onFC onFO onV

/-- The `vacuous` computation rule. -/
theorem elim_vacuous {β : Type} (C : Carrier F α) (s : S)
    (onE onP : α → β) (onFC onFO onV : β) :
    C.elim (C.report s Evidence.View.vacuous) onE onP onFC onFO onV = onV :=
  elim_report C s _ onE onP onFC onFO onV

/-- **The eliminator is total.** Every result says a view, and on it `elim` is
exactly the five-handler dispatch: it is defined at every result, and it never
returns a value none of the five handlers supplied. -/
theorem elim_total {β : Type} (C : Carrier F α) (r : C.R)
    (onE onP : α → β) (onFC onFO onV : β) :
    ∃ v, C.Says r v ∧ C.elim r onE onP onFC onFO onV = dispatch onE onP onFC onFO onV v := by
  obtain ⟨v, hv⟩ := C.says_total r
  exact ⟨v, hv, C.elim_spec r v onE onP onFC onFO onV hv⟩

/-- **Every consumer is a five-handler dispatch.** For any `f : C.R → β` and any
site, `f` agrees with the `elim` built from `f`'s own behaviour on the five
statuses. So a consumer cannot avoid handling a status by writing something
other than `elim`: whatever it wrote *is* an `elim`, extensionally, and its
`forkedOpen` behaviour is `f` applied to a forked report whether it meant to
have one or not. -/
theorem consumers_factor {β : Type} (C : Carrier F α) (f : C.R → β) (s : S)
    (v : Evidence.View α) :
    f (C.report s v)
      = C.elim (C.report s v)
          (fun a => f (C.report s (Evidence.View.exact a)))
          (fun a => f (C.report s (Evidence.View.provisional a)))
          (f (C.report s Evidence.View.forkedClosed))
          (f (C.report s Evidence.View.forkedOpen))
          (f (C.report s Evidence.View.vacuous)) := by
  rw [elim_report]
  cases v <;> rfl

/-- **NO DEFAULT BRANCH — every handler slot is observed.** Two consumers that
differ in any one of the five handlers differ at some result. So none of the
five may be supplied "just to typecheck": each one is the whole behaviour of the
consumer at a reachable status.

This is the checkable proxy codex proposed in place of the unenforceable
salience requirement. §8 states precisely what it does not buy. -/
theorem every_status_slot_is_load_bearing {β : Type} (C : Carrier F α) (s : S)
    (onE onP onE' onP' : α → β) (onFC onFO onV onFC' onFO' onV' : β) :
    (onE ≠ onE' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onV ≠ C.elim r onE' onP onFC onFO onV)
      ∧ (onP ≠ onP' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onV ≠ C.elim r onE onP' onFC onFO onV)
      ∧ (onFC ≠ onFC' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onV ≠ C.elim r onE onP onFC' onFO onV)
      ∧ (onFO ≠ onFO' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onV ≠ C.elim r onE onP onFC onFO' onV)
      ∧ (onV ≠ onV' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onV ≠ C.elim r onE onP onFC onFO onV') := by
  refine ⟨fun hne => ?_, fun hne => ?_, fun hne => ?_, fun hne => ?_, fun hne => ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, onE a ≠ onE' a :=
      Classical.byContradiction fun hc =>
        hne (funext fun a => Classical.byContradiction fun h => hc ⟨a, h⟩)
    refine ⟨C.report s (Evidence.View.exact a), ?_⟩
    rw [elim_exact, elim_exact]
    exact ha
  · obtain ⟨a, ha⟩ : ∃ a, onP a ≠ onP' a :=
      Classical.byContradiction fun hc =>
        hne (funext fun a => Classical.byContradiction fun h => hc ⟨a, h⟩)
    refine ⟨C.report s (Evidence.View.provisional a), ?_⟩
    rw [elim_provisional, elim_provisional]
    exact ha
  · refine ⟨C.report s Evidence.View.forkedClosed, ?_⟩
    rw [elim_forkedClosed, elim_forkedClosed]
    exact hne
  · refine ⟨C.report s Evidence.View.forkedOpen, ?_⟩
    rw [elim_forkedOpen, elim_forkedOpen]
    exact hne
  · refine ⟨C.report s Evidence.View.vacuous, ?_⟩
    rw [elim_vacuous, elim_vacuous]
    exact hne

/-- A report determines its view: two reports at the same site with different
views are different results. What §7 needs to refute a renderer rather than a
view. -/
theorem report_view_inj (C : Carrier F α) {s : S} {v v' : Evidence.View α}
    (h : C.report s v = C.report s v') : v = v' :=
  C.says_functional _ v v' (h ▸ C.says_report s v) (C.says_report s v')

/-! ## §3. What a singular value means, and why nothing produces one for free.

`IsTheAnswer answer s v` is `Holes.lean`'s seal read at a site: `v` is a
candidate and it is the *only* one. `StabilityCert F answer s v` is that,
quantified over every future `F` permits — which is precisely the conclusion of
`Evidence.exact_sound`, made a value one can require as an argument.

`no_honest_projection` is the theorem the header calls the enforcement. It is
stated over the abstract `Carrier`, so it is about every implementation, and its
premise is exactly the situation that makes the claim true: a site whose
evidence forks. Where nothing ever forks a projection *can* be honest, and
saying so is the difference between a theorem and a slogan. -/

/-- **`v` is THE answer at `s`**: a candidate, and the only one
(`Holes.SealsTo`). This is what a singular UI value asserts. -/
def IsTheAnswer (answer : S → GSet α) (s : S) (v : α) : Prop :=
  answer s v = true ∧ Holes.SealsTo (answer s) v

/-- **A stability certificate**: `v` is the answer at every future `F` permits
from `s`. `Evidence.exact_sound`'s conclusion, as a value — and **not a new
notion**: it is `ResultStatus.Exact`, so §6's scope coercion is that file's
`exact_weakens` and needs no restatement here. -/
abbrev StabilityCert (F : Evidence.Future S) (answer : S → GSet α) (s : S) (v : α) :
    Prop := ResultStatus.Exact F answer s v

/-- ⚠ **NO IMPLICIT COERCION.** At a carrier over evidence that forks at some
site, **no** total function `C.R → α` is answer-honest — not a clever one, not a
conservative one. Whatever it returns at a forked report is one of two
candidates, and being one of two is exactly not being the answer.

Stated over the abstract interface, so it is not a fact about `Result`: it holds
for every carrier satisfying §1's laws, including ones whose constructors a
consumer could never see. This is what "keep the constructors abstract" buys
when it is a theorem instead of a convention. -/
theorem no_honest_projection (C : Carrier F α) (answer : S → GSet α) (s : S)
    (hfork : ∃ a b : α, a ≠ b ∧ answer s a = true ∧ answer s b = true) :
    ¬ ∃ g : C.R → α, ∀ r, IsTheAnswer answer (C.site r) (g r) := by
  rintro ⟨g, hg⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hfork
  have h := hg (C.report s Evidence.View.forkedOpen)
  rw [C.site_report] at h
  exact hab ((h.2 a ha).trans (h.2 b hb).symm)

/-- **…and the fork premise is load-bearing.** Where the evidence never forks a
total projection *is* honest: at the one-site carrier whose answer is the
singleton `{47}`, `fun _ => 47` returns the answer at every result. So
`no_honest_projection` is a statement about forked evidence and not a blanket
prohibition — its hypothesis can fail, and when it fails the conclusion does
too. -/
theorem honest_projection_exists_without_a_fork :
    ∃ g : (stdCarrier (fun _ _ : Unit => True) Holes.Val).R → Holes.Val,
      ∀ r, IsTheAnswer (fun _ : Unit => (fun a => decide (a = 47) : GSet Holes.Val))
        ((stdCarrier (fun _ _ : Unit => True) Holes.Val).site r) (g r) :=
  ⟨fun _ => 47, fun _ => ⟨rfl, fun _ hb => of_decide_eq_true hb⟩⟩

/-- **The certified read** — the repair for the first half of the trichotomy.
It consumes the result *and* a stability certificate for a value at the
result's own site, and returns that value.

The proof is the certificate unwrapped, and that is the content: the argument
the bare projection could not supply is exactly the missing proof, and
`readCertified_is_the_answer` is true only because it was supplied. -/
def readCertified (C : Carrier F α) (answer : S → GSet α) (_r : C.R) (v : α)
    (_cert : StabilityCert F answer (C.site _r) v) : α := v

/-- The certified read returns the answer — at every future `F` permits from the
site, not merely at the site. -/
theorem readCertified_is_the_answer (C : Carrier F α) (answer : S → GSet α)
    (r : C.R) (v : α) (cert : StabilityCert F answer (C.site r) v)
    {t : S} (ht : F (C.site r) t) :
    IsTheAnswer answer t (readCertified C answer r v cert) := cert t ht

/-! ## §4. The render boundary — an exact badge is a promise about the future.

An **honest renderer** is one with a sound evaluator behind it: it reports, at
each site, the view some `Evidence.SoundEvaluator` computes there. That is not a
restatement of the conclusion — `Evidence.SoundEvaluator` is two independently
meaningful clauses (an exact report is true where it is made, and is never
retracted along a permitted future), and §7 exhibits a renderer that has the
first and not the second.

`renderedExact_implies_stable` is then the property PREOSCRIPTING §8 asks for:
the badge is not a statement about now, it is a certificate about every
permitted future, and an honest renderer can be made to hand one over. -/

/-- **An honest renderer**: some sound evaluator is behind it, and it reports
that evaluator's view at each site. -/
def HonestRenderer (F : Evidence.Future S) (answer : S → GSet α)
    (C : Carrier F α) (ρ : S → C.R) : Prop :=
  ∃ peval : S → Evidence.View α,
    Evidence.SoundEvaluator F answer peval ∧ ∀ s, ρ s = C.report s (peval s)

/-- **RENDERED EXACT ⇒ STABLE.** If an honest renderer's report at `s` says
`exact v`, then `v` is the answer at **every** future `F` permits from `s` — the
badge yields a `StabilityCert`, which `readCertified` is the only answer-honest
consumer of.

`Evidence.exact_sound` is the seed; what is added is the render boundary: the
hypothesis is a fact about the *report a UI holds*, not about an evaluator a
proof happens to mention. -/
theorem renderedExact_implies_stable {answer : S → GSet α} {C : Carrier F α}
    {ρ : S → C.R} (hρ : HonestRenderer F answer C ρ) {s : S} {v : α}
    (h : C.Says (ρ s) (Evidence.View.exact v)) :
    StabilityCert F answer s v := by
  obtain ⟨peval, hsound, hrep⟩ := hρ
  have hsays : C.Says (ρ s) (peval s) := by
    rw [hrep s]; exact C.says_report s (peval s)
  have hv : peval s = Evidence.View.exact v := C.says_functional (ρ s) _ _ hsays h
  exact fun t ht => Evidence.exact_sound hsound hv ht

/-- A sound evaluator, reported at the site it read, is an honest renderer. The
only way this file builds one. -/
theorem soundEvaluator_renders_honestly {answer : S → GSet α} (C : Carrier F α)
    {peval : S → Evidence.View α} (hs : Evidence.SoundEvaluator F answer peval) :
    HonestRenderer F answer C (fun s => C.report s (peval s)) :=
  ⟨peval, hs, fun _ => rfl⟩

/-- **The sanctioned renderer** at the state carrier: `Evidence.render`, whose
soundness for the sealed future is `Evidence.render_sound`. -/
noncomputable def renderReport {β : Type}
    (C : Carrier (Evidence.SealedFuture (α := β)) β)
    (e : Evidence.ResultEvidence β) : C.R := C.report e (Evidence.render e)

/-- `renderReport` is an honest renderer. -/
theorem renderReport_honest {β : Type}
    (C : Carrier (Evidence.SealedFuture (α := β)) β) :
    HonestRenderer (Evidence.SealedFuture (α := β)) Evidence.values C
      (renderReport C) :=
  soundEvaluator_renders_honestly C Evidence.render_sound

/-! ## §5. Resolution — reused from `ResultStatus.lean`, not rebuilt.

§5.5 of `PREOSCRIPTING.md`: *"you cannot silently collapse a fork" is right;
"you cannot ever pick one" is wrong.* The **type-level** half of that — a
`Policy`, a `ResolvedBy π e` indexed by the policy term *and* the evidence, and
the proof that two policies on one fork disagree — is `ResultStatus.lean`'s §6,
committed before this file existed. It is imported, not duplicated: a second
`ResolvedBy` in the same library is two shapes that agree today and disagree
later.

What this file owns is the half that file names as unbuilt in its own boundary:
*"what is **not** built is any statement that an elaborator never inserts that
projection silently"*. `no_honest_projection` (§3) is that statement at the
render boundary, and `singularSelection_implies_namedPolicy` below joins the two
into the property §8 asks for. -/

/-- The carrier every concrete witness below lives at: results over
`Evidence.ResultEvidence Holes.Val`, indexed by the sealed future. -/
def valCarrier : Carrier (Evidence.SealedFuture (α := Holes.Val)) Holes.Val :=
  stdCarrier _ _

/-- `47` is a candidate at `Evidence.forkedClosedW` — the fork *waiting will not
fix*, which is why every witness below sits there rather than at the open one. -/
theorem cand47_forkedClosedW : Evidence.values Evidence.forkedClosedW 47 = true :=
  (Evidence.values_cand4749 (e := Evidence.forkedClosedW) rfl).1

/-- `49` is a candidate at `Evidence.forkedClosedW`. -/
theorem cand49_forkedClosedW : Evidence.values Evidence.forkedClosedW 49 = true :=
  (Evidence.values_cand4749 (e := Evidence.forkedClosedW) rfl).2

/-- ⚠ **SINGULAR SELECTION ⇒ A NAMED POLICY.** Four clauses, and the last is the
one that stops the retention being decoration:

  * no total `valCarrier.R → Holes.Val` is answer-honest — the closed fork at
    `Evidence.forkedClosedW` refutes every one of them (`no_honest_projection`),
    and it is *closed*, so the refutation is not a timing artifact;
  * a resolution exists and is explicit: `ResultStatus.resolvedAlice` and
    `ResultStatus.resolvedBob` are taken at the **same evidence**, which is an
    index of both their types;
  * they return different values — `47` and `49`
    (`ResultStatus.policies_disagree_on_a_fork`);
  * and no function of the evidence alone agrees with every resolution
    (`ResultStatus.resolved_value_is_not_a_function_of_the_evidence`), so the
    policy in the type is information a later reader cannot reconstruct.

A surface that prints the number and drops the policy has hidden a decision
that changes the number. -/
theorem singularSelection_implies_namedPolicy :
    (¬ ∃ g : valCarrier.R → Holes.Val,
        ∀ r, IsTheAnswer Evidence.values (valCarrier.site r) (g r))
      ∧ ResultStatus.resolvedAlice.value = 47
      ∧ ResultStatus.resolvedBob.value = 49
      ∧ ResultStatus.resolvedAlice.value ≠ ResultStatus.resolvedBob.value
      ∧ ¬ ∃ f : Evidence.ResultEvidence Holes.Val → Holes.Val,
          ∀ (π : ResultStatus.Policy Holes.Val)
            (e : Evidence.ResultEvidence Holes.Val)
            (x : ResultStatus.ResolvedBy π e), x.value = f e :=
  ⟨no_honest_projection valCarrier Evidence.values Evidence.forkedClosedW
     ⟨47, 49, by decide, cand47_forkedClosedW, cand49_forkedClosedW⟩,
   rfl, rfl, ResultStatus.policies_disagree_on_a_fork,
   ResultStatus.resolved_value_is_not_a_function_of_the_evidence⟩

/-- ⚠ **NO IMPLICIT COERCION — the trichotomy, in one statement.** At a carrier
over evidence that forks somewhere:

  * a bare `C.R → α` is **never** answer-honest;
  * consuming a **stability certificate**, the read is the answer at every
    permitted future;
  * consuming a **named policy**, the value carries the proof that *that policy*
    selected it, and both the policy and the evidence are indices of its type
    (`ResultStatus.ResolvedBy`).

So the extra argument is not decoration: without one of the two the conclusion
is false, and with either it is a theorem. That is the enforceable content of
§5.5's *"no branch selection occurs through an implicit coercion"*. -/
theorem noImplicitCoercion (C : Carrier F α) (answer : S → GSet α) (s : S)
    (hfork : ∃ a b : α, a ≠ b ∧ answer s a = true ∧ answer s b = true) :
    (¬ ∃ g : C.R → α, ∀ r, IsTheAnswer answer (C.site r) (g r))
      ∧ (∀ (r : C.R) (v : α) (cert : StabilityCert F answer (C.site r) v) (t : S),
          F (C.site r) t → IsTheAnswer answer t (readCertified C answer r v cert))
      ∧ (∀ (π : ResultStatus.Policy α) (e : Evidence.ResultEvidence α)
          (x : ResultStatus.ResolvedBy π e), π e = some x.value) :=
  ⟨no_honest_projection C answer s hfork,
   fun r v cert _t ht => readCertified_is_the_answer C answer r v cert ht,
   fun _ _ x => x.chosen⟩

/-! ## §6. Scope — the badge names its future, and the site must be a world.

§8's third property: no "fully synchronized" status without naming the scope it
is relative to. Half of it is **inherited rather than restated**: this file's
`StabilityCert` *is* `ResultStatus.Exact`, so the coercion between scopes is
`ResultStatus.exact_weakens` (derived from relation inclusion, never a
subtyping rule — §5.3's requirement) and its invalidity in the other direction
is `ResultStatus.exact_does_not_strengthen`, with `Evidence.openW` as the
witness. Nothing about that needs re-proving at the render boundary and nothing
below re-proves it.

What is new here is the other index — the **site**. `WorldFuture.lean` proves
that every sound *state*-indexed certificate must refuse `openW`, so a badge
whose site is a materialized state cannot carry delivery-stability at all.
`worldCarrier` is therefore built beside `valCarrier`, and it is the deployable
one. -/

/-- The world-sited carrier: results whose site is a `WorldFuture.World`, indexed
by the world-level sealed future. -/
def worldCarrier : Carrier (WorldFuture.SealedFuture (α := Holes.Val)) Holes.Val :=
  stdCarrier _ _

/-- **The deployable renderer is world-sited.** `WorldFuture.renderW` is sound
for the world-level sealed future (`WorldFuture.renderW_sound`), so reporting it
at the world it read is an honest renderer — and the `site` a badge carries is
then the world, which is what `WorldFuture.certificate_reuse_is_unsound` says a
certificate must carry. -/
theorem worldSited_renderer_honest :
    HonestRenderer (WorldFuture.SealedFuture (α := Holes.Val))
      (fun w => Evidence.values (WorldFuture.observe w)) worldCarrier
      (fun w => worldCarrier.report w (WorldFuture.renderW w)) :=
  soundEvaluator_renders_honestly worldCarrier WorldFuture.renderW_sound

/-- ⚠ **WHY THE SITE MAY NOT BE A STATE WHEN THE FUTURE IS DELIVERY.** Any
predicate on materialized states that soundly licenses "the rendered answer will
not move under delivery" must **refuse** `Evidence.openW` — even though a
replica standing at `WorldFuture.wQuiesced` has correctly checked exactly that,
at that state. `WorldFuture.no_sound_state_cert_accepts_openW` restated at this
file's boundary: it is why §6 builds `worldCarrier` and not only
`valCarrier`. -/
theorem state_sited_certificates_refuse_openW
    (C : Evidence.ResultEvidence Holes.Val → Prop)
    (hC : ∀ w : WorldFuture.World Holes.Val, C (WorldFuture.observe w) →
      Evidence.FreeTermination WorldFuture.DeliveryFuture WorldFuture.renderW w) :
    ¬ C Evidence.openW :=
  WorldFuture.no_sound_state_cert_accepts_openW C hC

/-! ## §7. THE REFUTABLE IMPLEMENTATIONS — without these the module cannot go red.

Two dishonest renderers, one per forbidden move.

`eagerRender` reports `exact` on a unique candidate **without reading the
closure**. It is not a strawman: it is *correct where it is made*, satisfying
the first clause of `Evidence.SoundEvaluator` exactly. What it fails is
irrevocability, which is the whole reason §8's first property is about a
*certificate* and not about a check.

`silentValue` is the coercion §5.5 forbids: a total `Result → Holes.Val` that
mentions no policy. It type-checks, it is total, and `no_honest_projection`
says it cannot be answer-honest — and `silent_and_named_agree` shows it computes
the same number the named resolution does, so the type is carrying the only
thing that differs. -/

open Classical in
/-- ⚠ **THE FIRST DISHONEST RENDERER.** `exact` on a unique candidate, closure
never consulted. -/
noncomputable def eagerRender {β : Type} (e : Evidence.ResultEvidence β) :
    Evidence.View β :=
  if hu : ∃ a, Evidence.values e a = true ∧ ∀ b, Evidence.values e b = true → b = a then
    Evidence.View.exact (Classical.choose hu)
  else if ∃ a, Evidence.values e a = true then Evidence.View.forkedOpen
  else Evidence.View.vacuous

/-- `eagerRender` answers `exact a` on any sealed, inhabited evidence — closed or
not. -/
theorem eagerRender_exact {β : Type} {e : Evidence.ResultEvidence β} {a : β}
    (hm : Evidence.values e a = true) (hs : Holes.SealsTo (Evidence.values e) a) :
    eagerRender e = Evidence.View.exact a := by
  have hu : ∃ x, Evidence.values e x = true
      ∧ ∀ b, Evidence.values e b = true → b = x := ⟨a, hm, hs⟩
  have hch := Classical.choose_spec hu
  have heq : Classical.choose hu = a := hs _ hch.1
  simp only [eagerRender, dif_pos hu, heq]

/-- `eagerRender` answers `forkedOpen` on two distinct candidates. -/
theorem eagerRender_fork {β : Type} {e : Evidence.ResultEvidence β} {a b : β}
    (ha : Evidence.values e a = true) (hb : Evidence.values e b = true) (hab : a ≠ b) :
    eagerRender e = Evidence.View.forkedOpen := by
  simp only [eagerRender, dif_neg (Evidence.not_unique_of_two ha hb hab),
    if_pos (show ∃ x, Evidence.values e x = true from ⟨a, ha⟩)]

/-- **`eagerRender` is correct where it is made.** Its `exact` reports really are
backed by the evidence at the state they are made at — the first clause of
`Evidence.SoundEvaluator`, in full. The defect is not local falsehood. -/
theorem eagerRender_correct {β : Type} (e : Evidence.ResultEvidence β) (v : β)
    (h : eagerRender e = Evidence.View.exact v) :
    Evidence.values e v = true ∧ Holes.SealsTo (Evidence.values e) v := by
  by_cases hu : ∃ a, Evidence.values e a = true
      ∧ ∀ b, Evidence.values e b = true → b = a
  · rw [eagerRender, dif_pos hu] at h
    injection h with hv
    obtain ⟨hm, hs⟩ := Classical.choose_spec hu
    exact ⟨hv ▸ hm, fun b hb => hv ▸ (hs b hb)⟩
  · by_cases hne : ∃ a, Evidence.values e a = true
    · rw [eagerRender, dif_neg hu, if_pos hne] at h
      exact absurd h (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))
    · rw [eagerRender, dif_neg hu, if_neg hne] at h
      exact absurd h (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

theorem eagerRender_openW : eagerRender Evidence.openW = Evidence.View.exact 47 :=
  eagerRender_exact (Evidence.values_cand47 (e := Evidence.openW) rfl).1
    (Evidence.values_cand47 (e := Evidence.openW) rfl).2

theorem eagerRender_openForkW :
    eagerRender Evidence.openForkW = Evidence.View.forkedOpen :=
  eagerRender_fork (Evidence.values_cand4749 (e := Evidence.openForkW) rfl).1
    (Evidence.values_cand4749 (e := Evidence.openForkW) rfl).2 (by decide)

/-- `47` is not the answer at `openForkW`: `49` is a candidate too. -/
theorem not_isTheAnswer_openForkW :
    ¬ IsTheAnswer Evidence.values Evidence.openForkW 47 := by
  intro h
  exact absurd (h.2 49 (Evidence.values_cand4749 (e := Evidence.openForkW) rfl).2)
    (by decide)

/-- ⚠ **THE EAGER BADGE IS A LIE, and here is exactly which clause it breaks.**
It is correct where it is made; `openW` renders `exact 47`; `openForkW` is a
**sealed** future of `openW`; and `47` is not the answer there. So `eagerRender`
is not an `Evidence.SoundEvaluator`, and `renderedExact_implies_stable`'s
conclusion is false of it: the badge promises a future the renderer never
consulted. -/
theorem eagerRender_is_not_sound :
    (∀ e v, eagerRender (β := Holes.Val) e = Evidence.View.exact v →
        Evidence.values e v = true ∧ Holes.SealsTo (Evidence.values e) v)
      ∧ eagerRender Evidence.openW = Evidence.View.exact 47
      ∧ Evidence.SealedFuture Evidence.openW Evidence.openForkW
      ∧ ¬ IsTheAnswer Evidence.values Evidence.openForkW 47
      ∧ ¬ Evidence.SoundEvaluator (Evidence.SealedFuture (α := Holes.Val))
          Evidence.values eagerRender := by
  refine ⟨eagerRender_correct, eagerRender_openW, Evidence.openW_seals_to_openForkW,
    not_isTheAnswer_openForkW, ?_⟩
  intro hs
  have h := hs.irrevocable Evidence.openW Evidence.openForkW 47
    Evidence.openW_seals_to_openForkW eagerRender_openW
  rw [eagerRender_openForkW] at h
  exact absurd h (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

/-- ⚠ **…and therefore it is not an honest renderer.** Not "unproved" —
refuted: any evaluator behind it would have to *be* it (`report_view_inj`), and
no sound evaluator is. -/
theorem eagerRenderer_is_dishonest :
    ¬ HonestRenderer (Evidence.SealedFuture (α := Holes.Val)) Evidence.values
        valCarrier (fun e => valCarrier.report e (eagerRender e)) := by
  rintro ⟨peval, hsound, hrep⟩
  have hpe : ∀ e, eagerRender e = peval e :=
    fun e => report_view_inj valCarrier (hrep e)
  have h1 : peval Evidence.openW = Evidence.View.exact 47 := by
    rw [← hpe]; exact eagerRender_openW
  have h2 := hsound.irrevocable Evidence.openW Evidence.openForkW 47
    Evidence.openW_seals_to_openForkW h1
  rw [← hpe, eagerRender_openForkW] at h2
  exact absurd h2 (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

/-- ⚠ **THE SECOND DISHONEST IMPLEMENTATION: a silent fork projection.** A
total `valCarrier.R → Holes.Val` that applies `ResultStatus.bySource alice` to
the site's evidence and then **drops the policy**, returning a bare number.
It consults no status, names no rule, and it type-checks. -/
noncomputable def silentValue (r : valCarrier.R) : Holes.Val :=
  (ResultStatus.bySource Evidence.alice (valCarrier.site r)).getD 0

/-- The report the silent projection is refuted at: the **closed** fork, so the
refutation is not a timing artifact. -/
noncomputable def forkedReport : valCarrier.R :=
  valCarrier.report Evidence.forkedClosedW Evidence.View.forkedClosed

theorem silentValue_forkedReport : silentValue forkedReport = 47 := by
  show (ResultStatus.bySource Evidence.alice
    (valCarrier.site forkedReport)).getD 0 = 47
  rw [show valCarrier.site forkedReport = Evidence.forkedClosedW from
    valCarrier.site_report _ _, ResultStatus.bySource_alice_forkedClosedW]
  rfl

/-- ⚠ **THE SILENT PROJECTION EXISTS AND CANNOT BE HONEST.** It returns `47`
at a report whose evidence supports `49` just as well, and
`no_honest_projection` says no function of its type is answer-honest — so this
is not a defect of *this* projection, repairable by a better one. -/
theorem silentValue_cannot_be_honest :
    silentValue forkedReport = 47
      ∧ Evidence.values Evidence.forkedClosedW 49 = true
      ∧ ¬ ∃ g : valCarrier.R → Holes.Val,
          ∀ r, IsTheAnswer Evidence.values (valCarrier.site r) (g r) :=
  ⟨silentValue_forkedReport, cand49_forkedClosedW,
   no_honest_projection valCarrier Evidence.values Evidence.forkedClosedW
     ⟨47, 49, by decide, cand47_forkedClosedW, cand49_forkedClosedW⟩⟩

/-- ⚠ **THE SAME NUMBER, AND ONLY THE TYPE DIFFERS.** The silent projection and
`ResultStatus.resolvedAlice` compute **`47`** alike — the same policy, applied
to the same evidence, with the name kept in one case and dropped in the other.
So what `ResolvedBy π e` retains is not the value; it is the fact that a choice
was made and that `bySource bob` would have said `49`
(`singularSelection_implies_namedPolicy`). Dropping the policy drops nothing you
can see in the number, which is precisely why a type has to carry it. -/
theorem silent_and_named_agree :
    silentValue forkedReport = ResultStatus.resolvedAlice.value :=
  silentValue_forkedReport

/-! ### The honest renderer is not the silent one — non-vacuity

`Evidence.blindEval` is a sound evaluator that reports `exact` nowhere
(`Evidence.completeness_is_load_bearing`), so "honest" alone buys nothing: a
renderer that says `vacuous` forever satisfies §4. The witnesses below pin that
the sanctioned renderer is *not* of that kind — it does report `exact`, and the
certificate the badge yields is a real one. -/

/-- The sanctioned renderer says `exact 47` at `Evidence.exactW`. -/
theorem renderReport_says_exact :
    valCarrier.Says (renderReport valCarrier Evidence.exactW)
      (Evidence.View.exact 47) :=
  (std_says _ _ _ _).mpr Evidence.four_states_inhabited.1

/-- **The badge is backed, and the class is not empty.** `renderReport` reports
`exact 47` at `exactW`, and `renderedExact_implies_stable` turns that report
into a certificate: `47` is the answer at every sealed future of `exactW`. -/
theorem exact_badge_at_exactW_is_backed :
    StabilityCert (Evidence.SealedFuture (α := Holes.Val)) Evidence.values
      Evidence.exactW 47 :=
  renderedExact_implies_stable (renderReport_honest valCarrier) renderReport_says_exact

/-! ## §8. THE SALIENCE LIMIT — stated exactly, with the proxy that replaces it.

Codex's fourth item is a limit, not a property, and it is ⟨TERMINAL⟩: a
presentation is a function out of the result, constant functions exist, and no
interface refuses one. `salience_is_not_enforceable` says exactly that — and
says it *through the eliminator*, which is the sharp form: supplying all five
handlers, as the remedy demands, does not make the five outputs differ.

What is enforceable is the pair:

  * every status must be **given a value** — there is no default branch, because
    `elim_spec` leaves `elim` no behaviour outside the five
    (`elim_total`, `consumers_factor`);
  * and each value is **observed** — change one handler and some result changes
    (`every_status_slot_is_load_bearing`).

So: *semantic presence is enforced; visual prominence is not.* Both halves are
theorems, and the second is not a weaker version of the first — it is the
strongest checkable thing in the neighbourhood, which is what codex proposed and
what §8 above delivers. -/

/-- ⚠ **SALIENCE IS NOT ENFORCEABLE — and the eliminator does not help.** A
consumer that supplies all five handlers may still return the same `β` at every
result. `OpenForked` in one-pixel grey is this function with `β` a stylesheet:
the five branches were written, and they were written identical. No property of
the interface excludes it, and none can. -/
theorem salience_is_not_enforceable {β : Type} (C : Carrier F α) (b : β) (r : C.R) :
    C.elim r (fun _ => b) (fun _ => b) b b b = b := by
  obtain ⟨v, hv⟩ := C.says_total r
  rw [C.elim_spec r v _ _ _ _ _ hv]
  cases v <;> rfl

/-- **PRESENCE IS ENFORCED, PROMINENCE IS NOT — the verdict, in one statement.**
The negative half is `salience_is_not_enforceable` at an arbitrary display type;
the positive half is that each of the five handlers is observed by some result,
so none may be supplied merely to typecheck. The gap between them is the honest
limit of what a type system reaches, and it is stated here rather than papered
over with a stronger-sounding claim. -/
theorem presence_enforced_prominence_not {β : Type} (C : Carrier F α) (s : S)
    (b b' : β) (hbb : b ≠ b') :
    (∀ r : C.R, C.elim r (fun _ => b) (fun _ => b) b b b = b)
      ∧ (∃ r : C.R, C.elim r (fun _ => b) (fun _ => b) b b b
          ≠ C.elim r (fun _ => b) (fun _ => b) b b' b) :=
  ⟨fun r => salience_is_not_enforceable C b r,
   (every_status_slot_is_load_bearing C s (fun _ => b) (fun _ => b) (fun _ => b)
      (fun _ => b) b b b b b' b).2.2.2.1 hbb⟩

end Uwueave.HonestRender
