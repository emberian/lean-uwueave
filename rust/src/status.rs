//! # `status` — the six-cell epistemic carrier, HAND-TRANSLATED from Lean.
//!
//! ## ⚠ What this module is, stated before anything else
//!
//! **This is a hand transcription. Nothing in this file is verified.** The Lean
//! development (`../../Uwueave/ResultStatus.lean`, `RenderSix.lean`,
//! `RenderProgress.lean`, `Evidence.lean`) proves the theorems that make this
//! design the right one; the Rust below is a second, independent, unproved
//! shape of the same idea, typed by a human. The Lean proofs **license the
//! design**. They say nothing whatsoever about this code.
//!
//! That distinction is the whole point of the file, so it is worth saying in
//! the vocabulary the rest of the crate uses: [`crate::movelog`],
//! [`crate::seq`] and [`crate::era`] contain **no** decision logic — they
//! marshal bytes into a Lean-authored kernel compiled to C. This module
//! contains decision logic and calls no kernel. It is therefore of a strictly
//! weaker kind than everything around it, and the tests at the bottom are unit
//! tests, not evidence.
//!
//! ### What could drift, concretely
//!
//! Each item is a place where the Rust and the Lean could disagree and no
//! machine would notice.
//!
//! 1. **`GSet` is a `Bool`-valued function; [`Evidence`] uses `BTreeSet`.** The
//!    Lean carrier admits infinite candidate sets and infinite rosters. Ours
//!    cannot. Every theorem about an unbounded value type is being applied here
//!    to a finite fragment of it, and the restriction is invisible in the types.
//! 2. **`statusOf` is `noncomputable` in Lean; [`status_of`] is a total
//!    function here.** Lean's takes "is there exactly one candidate value"
//!    classically, over an unbounded type. Ours counts a `BTreeSet`. Ours is
//!    the computable analogue `Evidence.lean` explicitly records as *not built*
//!    ("the list-shaped computable analogue that `Holes.evalSet_ofList` gives
//!    for the image is not built for `render`"). So [`status_of`] is not a
//!    compiled `statusOf`; it is a different function that we believe agrees on
//!    finite inputs. Nobody proved that.
//! 3. **The fork constructors carry their candidates.** Lean's
//!    `Status.forkedOpen` carries **nothing**: `ResultStatus.ResolvedBy π e` is
//!    indexed by the evidence, so `alternatives_are_retained` is `rfl` — the
//!    alternatives are free. Rust has no dependent types, so
//!    [`Status::ForkedOpen`] carries a `Vec<(T, Source)>` by value and
//!    retention becomes something we *do* rather than something the type *is*.
//!    A future edit that drops the vector compiles.
//! 4. **`HonestWidget` is a `Prop` in Lean and a runtime check here.**
//!    [`honest_widget`] evaluates a candidate assignment at two statuses and
//!    reports. Lean's is a universally-quantified structure that cannot be
//!    inhabited by a dishonest assignment at all. Ours can be dodged by not
//!    calling it.
//! 5. **`PendingSound` quantifies over all states; [`pending_sound`] takes a
//!    slice.** A Rust check over a finite sample of states is a test.
//!    `RenderProgress.PendingSound` is a theorem about every state there is.
//! 6. **The five-cell fold [`View`] exists only to reproduce the blindness.**
//!    `ResultStatus.forget` is a Lean function with `forget_statusOf` proved
//!    about it. Ours is a `match` we wrote to look the same.
//! 7. **`Source` is `u64`; Lean's is `Nat`.** Wraparound is unrepresentable in
//!    the Lean and merely unlikely here.
//! 8. **No liveness half.** `RenderProgress.PendingProgress` rides
//!    `Liveness.FairOn` and a real scheduler premise. Nothing here models a
//!    schedule, so the module carries truth (`PendingSound`) and affordance
//!    (the `stopWaiting` button) and **not** progress. A `Pending` cell in this
//!    module is not a promise that anything will ever arrive.
//!
//! ### What would make this not a hand transcription
//!
//! Named here because "honestly labelled" is a stopping condition, not a fix.
//! The three existing decision layers ([`crate::movelog`], [`crate::seq`],
//! [`crate::era`]) are Lean-authored, emitted to C by `lake`, and called
//! through `shim.c`. The reason this one is not is concrete and small:
//! `ResultStatus.statusOf` is `noncomputable` — "is there exactly one candidate
//! value" is taken classically over an unbounded type — so there is no compiled
//! artifact to call. Closing that is two named pieces of Lean work:
//!
//! 1. a **computable, list-shaped `statusOf`** — the counterpart of
//!    `Holes.evalSet_ofList` that `Evidence.lean` records as not built for
//!    `render`; and
//! 2. a **refinement theorem** that it agrees with `statusOf` on evidence whose
//!    candidate set is the image of a list.
//!
//! With those, this file becomes marshalling and the decision moves back where
//! the other three already are. Until then every function below is a Rust twin
//! of a Lean definition, which is exactly the shape the rest of the crate exists
//! to avoid, and calling it anything else would be a lie.
//!
//! ## The six cells
//!
//! `ResultStatus.lean` §1's table, which is the shape everything else is built
//! on:
//!
//! | candidates | open              | closed          |
//! |------------|-------------------|-----------------|
//! | zero       | [`Status::Pending`] | [`Status::Absent`] |
//! | one        | [`Status::Provisional`] | [`Status::Exact`] |
//! | many       | [`Status::ForkedOpen`] | [`Status::ForkedClosed`] |
//!
//! The zero row is the one everybody folds into a single "empty" state, and
//! `ResultStatus.sixth_cell_is_distinguishable` is the theorem that the fold is
//! not faithful: the two cells have **opposite stability**, and the two UI bugs
//! everyone has shipped live exactly in the gap — a spinner on a definitively
//! absent answer, and "no results" flashed while a peer is still owed.

use std::collections::BTreeSet;

// ---------------------------------------------------------------------------
// §1. The evidence — three grow-only components (Uwueave/Evidence.lean §1)
// ---------------------------------------------------------------------------

/// A source of future evidence: a peer, an epoch, a frontier point.
///
/// Lean: `Evidence.Source := Nat`.
pub type Source = u64;

/// **The evidence behind one result position.**
///
/// Lean: `Evidence.ResultEvidence α := GSet (α × Source) × GSet Source × GSet Source`.
///
/// Three grow-only sets, merged componentwise:
///
/// * `candidates` — observed values, each **attributed** to the source that
///   justified it. Attribution is what lets a certificate bite, and what lets a
///   fork be rendered as a disagreement between named parties rather than as a
///   shrug;
/// * `obligations` — sources whose future contributions are still admissible
///   (Timely's frontier: a lower bound on what may still appear);
/// * `certificates` — sources declared closed. An arbiter's cut, an LVars
///   freeze, "I have nothing more".
///
/// The merge is union in all three components, so it is commutative,
/// associative and idempotent for the reason `GSet`'s is: it is
/// `BTreeSet::extend` three times, and nothing is ever removed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Evidence<T: Ord> {
    candidates: BTreeSet<(T, Source)>,
    obligations: BTreeSet<Source>,
    certificates: BTreeSet<Source>,
}

impl<T: Ord> Default for Evidence<T> {
    fn default() -> Self {
        Self {
            candidates: BTreeSet::new(),
            obligations: BTreeSet::new(),
            certificates: BTreeSet::new(),
        }
    }
}

impl<T: Ord + Clone> Evidence<T> {
    /// Empty evidence: nothing observed, nobody owed, nobody certified.
    ///
    /// Note that this is **closed** ([`Evidence::is_closed`]), because a
    /// vacuous obligation set is vacuously discharged — so its status is
    /// [`Status::Absent`], not [`Status::Pending`]. That is correct and it is
    /// worth knowing: "I asked nobody" and "I asked and they answered" are the
    /// same epistemic position, and both differ from "I am waiting".
    pub fn new() -> Self {
        Self::default()
    }

    /// Evidence from its three components at once.
    pub fn from_parts(
        candidates: impl IntoIterator<Item = (T, Source)>,
        obligations: impl IntoIterator<Item = Source>,
        certificates: impl IntoIterator<Item = Source>,
    ) -> Self {
        Self {
            candidates: candidates.into_iter().collect(),
            obligations: obligations.into_iter().collect(),
            certificates: certificates.into_iter().collect(),
        }
    }

    /// Record that `source` may still speak. Grow-only.
    pub fn owe(&mut self, source: Source) -> &mut Self {
        self.obligations.insert(source);
        self
    }

    /// Record a candidate value, attributed to the source that justified it.
    /// Grow-only.
    pub fn observe(&mut self, value: T, source: Source) -> &mut Self {
        self.candidates.insert((value, source));
        self
    }

    /// Declare `source` closed: it will contribute nothing further.
    ///
    /// Lean: `Evidence.certify`. Note what it does **not** do — it deletes no
    /// candidate (`certify_keeps_candidates`). Closure is a claim about the
    /// future, never a retraction of the past.
    pub fn certify(&mut self, source: Source) -> &mut Self {
        self.certificates.insert(source);
        self
    }

    /// Componentwise union. This is the whole merge; there is nothing to
    /// decide.
    pub fn merge(&mut self, other: &Self) {
        self.candidates.extend(other.candidates.iter().cloned());
        self.obligations.extend(other.obligations.iter().copied());
        self.certificates.extend(other.certificates.iter().copied());
    }

    /// [`Evidence::merge`], not in place.
    pub fn merged(&self, other: &Self) -> Self {
        let mut out = self.clone();
        out.merge(other);
        out
    }

    /// The attributed candidates.
    pub fn candidates(&self) -> &BTreeSet<(T, Source)> {
        &self.candidates
    }

    /// The sources still owed.
    pub fn obligations(&self) -> &BTreeSet<Source> {
        &self.obligations
    }

    /// The sources certified closed.
    pub fn certificates(&self) -> &BTreeSet<Source> {
        &self.certificates
    }

    /// **The value axis — attribution forgotten.**
    ///
    /// Lean: `Evidence.values`. This is the projection `status_of` reads for
    /// the candidate count, and forgetting the attribution here is why two
    /// sources that agree on `47` produce [`Status::Exact`] rather than a fork.
    pub fn values(&self) -> BTreeSet<T> {
        self.candidates.iter().map(|(v, _)| v.clone()).collect()
    }

    /// Every source that attributed the given value.
    pub fn sources_for(&self, value: &T) -> Vec<Source> {
        self.candidates.iter().filter(|(v, _)| v == value).map(|(_, o)| *o).collect()
    }

    /// The sources that have actually spoken: contributed a candidate, or
    /// certified themselves closed.
    pub fn heard_from(&self) -> BTreeSet<Source> {
        let mut out: BTreeSet<Source> = self.candidates.iter().map(|(_, o)| *o).collect();
        out.extend(self.certificates.iter().copied());
        out
    }

    /// **The future is closed**: every source still owed carries a certificate.
    ///
    /// Lean: `Evidence.Closed`. Deliberately *not* a fact about the values —
    /// that is the whole content of the two-axis split, and
    /// `Evidence.closed_iconfluent` is why this half survives a merge while the
    /// value half does not.
    pub fn is_closed(&self) -> bool {
        self.obligations.iter().all(|o| self.certificates.contains(o))
    }

    /// The sources that are owed and not yet certified — what a `Pending` cell
    /// is waiting for.
    pub fn open_sources(&self) -> Vec<Source> {
        self.obligations.iter().copied().filter(|o| !self.certificates.contains(o)).collect()
    }

    /// **The give-up state**: certify every source still owed.
    ///
    /// Lean: `RenderProgress.sealAll`. Candidates are untouched
    /// (`sealAll_keeps_candidates`); the only thing that moves is the closure
    /// claim. It is the honest discharge available with no peer cooperation at
    /// all — and it is lossy, because a peer that would have answered is now
    /// recorded as silent.
    pub fn seal_all(&self) -> Self {
        let mut out = self.clone();
        out.certificates.extend(out.obligations.iter().copied().collect::<Vec<_>>());
        out
    }

    /// `self ⊑ other` — componentwise inclusion, the induced order.
    pub fn leq(&self, other: &Self) -> bool {
        self.candidates.is_subset(&other.candidates)
            && self.obligations.is_subset(&other.obligations)
            && self.certificates.is_subset(&other.certificates)
    }

    /// **What a step may add.** A candidate that was not there may arrive only
    /// from a source that is still owed and has not been certified.
    ///
    /// Lean: `Evidence.Admits`.
    pub fn admits(&self, other: &Self) -> bool {
        other.candidates.iter().filter(|p| !self.candidates.contains(p)).all(|(_, o)| {
            self.obligations.contains(o) && !self.certificates.contains(o)
        })
    }

    /// **The extension future**: a monotone step respecting the certificates
    /// already held. New sources are permitted to appear.
    ///
    /// Lean: `Evidence.ExtensionFuture`.
    pub fn extends_to(&self, other: &Self) -> bool {
        self.leq(other) && self.admits(other)
    }

    /// **The sealed future**: an extension future over a *closed source set* —
    /// no source may appear that was not already an obligation.
    ///
    /// Lean: `Evidence.SealedFuture`. This is the future for which the
    /// renderer's soundness clauses hold; `render_retracts_when_a_new_source_
    /// appears` is why nothing weaker will do.
    pub fn seals_to(&self, other: &Self) -> bool {
        self.extends_to(other) && other.obligations.is_subset(&self.obligations)
    }

    /// "Some candidate satisfies `p`" — an existential over a grow-only set.
    ///
    /// Lean: `ResultStatus.anyCandidate`. Its `true` is self-certifying and its
    /// `false` is retractable at every uncertified obligation, which is the
    /// argument for one epistemic carrier over four coarse static types.
    pub fn any_candidate(&self, p: impl Fn(&T) -> bool) -> bool {
        self.candidates.iter().any(|(v, _)| p(v))
    }
}

// ---------------------------------------------------------------------------
// §2. The six-cell status (Uwueave/ResultStatus.lean §1)
// ---------------------------------------------------------------------------

/// **The runtime status of a result position** — the full candidates × closure
/// product.
///
/// Lean: `ResultStatus.Status`. A *declaration* states a capability (see
/// [`Capability`]); an *evaluation* returns one of these. Conflating them puts
/// a runtime fact in a static position, where it is either false or vacuous.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Status<T> {
    /// One candidate value, future closed. `47`.
    Exact(T),
    /// One candidate value, future open. `47 + ⟨pending⟩`.
    Provisional(T),
    /// Several incompatible candidates, future **closed**: waiting will not fix
    /// it. Carries every candidate with its attribution — see drift note 3.
    ForkedClosed(Vec<(T, Source)>),
    /// Several incompatible candidates, future open.
    ForkedOpen(Vec<(T, Source)>),
    /// **Zero candidates, future closed: definitive absence.** There is no
    /// answer and there will not be one.
    Absent,
    /// **Zero candidates, future open: nothing observed yet.** There is no
    /// answer *so far*.
    Pending,
}

impl<T> Status<T> {
    /// Which of the six cells this is, as a numeral — for telling constructors
    /// apart and for nothing else. Lean: `ResultStatus.statusTag`.
    pub fn tag(&self) -> u8 {
        match self {
            Status::Exact(_) => 0,
            Status::Provisional(_) => 1,
            Status::ForkedClosed(_) => 2,
            Status::ForkedOpen(_) => 3,
            Status::Absent => 4,
            Status::Pending => 5,
        }
    }

    /// The cell's name, for the ugly terminal UI.
    pub fn name(&self) -> &'static str {
        match self {
            Status::Exact(_) => "exact",
            Status::Provisional(_) => "provisional",
            Status::ForkedClosed(_) => "forkedClosed",
            Status::ForkedOpen(_) => "forkedOpen",
            Status::Absent => "absent",
            Status::Pending => "pending",
        }
    }
}

/// **The status.** The three-way case on the candidate *values*, with the
/// closure split applied to **all three** rows.
///
/// Lean: `ResultStatus.statusOf` — and see drift note 2: the Lean one is
/// noncomputable and this one is not, so they are two functions we believe
/// agree, not one function compiled twice.
pub fn status_of<T: Ord + Clone>(e: &Evidence<T>) -> Status<T> {
    let values = e.values();
    let closed = e.is_closed();
    match values.len() {
        0 => {
            if closed {
                Status::Absent
            } else {
                Status::Pending
            }
        }
        1 => {
            // `values` is non-empty here, but expressing that to the compiler
            // costs an `expect` on a path that is not fallible in the sense the
            // caller cares about. Pattern-match instead so there is no unwrap.
            match values.into_iter().next() {
                Some(v) => {
                    if closed {
                        Status::Exact(v)
                    } else {
                        Status::Provisional(v)
                    }
                }
                // Unreachable: `len() == 1`. Falling back to the zero-row cell
                // keeps the function total without lying about finality.
                None => {
                    if closed {
                        Status::Absent
                    } else {
                        Status::Pending
                    }
                }
            }
        }
        _ => {
            let candidates: Vec<(T, Source)> = e.candidates().iter().cloned().collect();
            if closed {
                Status::ForkedClosed(candidates)
            } else {
                Status::ForkedOpen(candidates)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §3. The five-cell fold — kept only to reproduce its blindness
// ---------------------------------------------------------------------------

/// The **older** five-constructor view, in which the two zero-candidate cells
/// are one point.
///
/// Lean: `Evidence.View`. It exists in this crate for exactly one purpose: to
/// let [`forget`] demonstrate that the fold cannot see the two dishonest
/// renderers, because the lie lives precisely where the fold is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum View<T> {
    /// One candidate, closed.
    Exact(T),
    /// One candidate, open.
    Provisional(T),
    /// Several, closed.
    ForkedClosed,
    /// Several, open.
    ForkedOpen,
    /// No candidates — *either* zero-candidate cell.
    Vacuous,
}

/// **The fold the five-constructor view performs**: both zero-candidate
/// statuses go to one point.
///
/// Lean: `ResultStatus.forget`, about which `forget_statusOf` proves that
/// forgetting the split returns `Evidence.render` on the nose. So the six-cell
/// status is a *refinement*, not a rival — and
/// `RenderSix.spinnerRender_folds_to_render` is the sharp consequence: the
/// five-status honesty predicate is **satisfied** by the spinner.
///
/// ⚠ One asymmetry with the Lean, on top of drift note 6: Lean's
/// `Status.forkedClosed` carries nothing, so `forget` loses nothing on the fork
/// rows. Ours carries the attributed candidates, so `forget` **drops them**.
/// That is a second, unproved way this function loses information, and it is
/// the only place in this module where a fork's candidates go anywhere. It is
/// deliberately not on any rendering path — [`widget_of`] never routes through
/// here.
pub fn forget<T>(status: Status<T>) -> View<T> {
    match status {
        Status::Exact(v) => View::Exact(v),
        Status::Provisional(v) => View::Provisional(v),
        Status::ForkedClosed(_) => View::ForkedClosed,
        Status::ForkedOpen(_) => View::ForkedOpen,
        Status::Absent => View::Vacuous,
        Status::Pending => View::Vacuous,
    }
}

// ---------------------------------------------------------------------------
// §4. The two dishonest renderers (Uwueave/RenderSix.lean §5)
// ---------------------------------------------------------------------------

/// ⚠ **THE SPINNER THAT NEVER STOPS.** [`status_of`] with definitive absence
/// re-badged as "nothing observed yet".
///
/// Lean: `RenderSix.spinnerRender`. This is the loading-forever bug, and it is
/// here so the slice can construct it and watch the widget layer refuse it. It
/// is **not** locally false — at a definitively absent evidence the answer set
/// really is empty. What is false is that waiting might help.
pub fn spinner_render<T: Ord + Clone>(e: &Evidence<T>) -> Status<T> {
    match status_of(e) {
        Status::Absent => Status::Pending,
        other => other,
    }
}

/// ⚠ **THE EMPTY STATE ASSERTED TOO EARLY.** [`status_of`] with "nothing
/// observed yet" re-badged as definitive absence — the empty state that flashes
/// before the data arrives, asserted as final.
///
/// Lean: `RenderSix.giveUpRender`.
pub fn give_up_render<T: Ord + Clone>(e: &Evidence<T>) -> Status<T> {
    match status_of(e) {
        Status::Pending => Status::Absent,
        other => other,
    }
}

/// A renderer that badges on one unrelated certificate and reads neither the
/// candidates nor the closure of the evidence it is shown at.
///
/// Lean: `RenderProgress.unrelatedEscape`. It satisfies the *escapability*
/// clause at every state and is still an epistemic lie, which is the separation
/// `escapability_does_not_imply_epistemic_truth` makes.
pub fn unrelated_escape<T: Ord + Clone>(e: &Evidence<T>, watched: Source) -> Status<T> {
    if e.certificates().contains(&watched) {
        Status::Absent
    } else {
        Status::Pending
    }
}

// ---------------------------------------------------------------------------
// §5. The semantic widget (Uwueave/RenderProgress.lean §7)
// ---------------------------------------------------------------------------

/// Whether this cell can still change. Lean: `RenderProgress.Finality`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Finality {
    /// Settled: no permitted future changes this cell.
    Terminal,
    /// Open: something is still owed.
    Open,
}

/// How many candidates the cell holds. Lean: `RenderProgress.Plurality`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Plurality {
    /// No candidate.
    Zero,
    /// Exactly one.
    One,
    /// Several — a fork.
    Many,
}

/// A discharge a surface may offer at a cell. Lean: `RenderProgress.Action`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Action {
    /// Wait for a source still owed to contribute.
    AwaitDelivery,
    /// Give up on the sources still owed ([`Evidence::seal_all`], as a button).
    StopWaiting,
    /// Pick among forked candidates — and name the [`Policy`] while doing it.
    ResolveFork,
}

impl Action {
    /// The button's label, for the ugly terminal UI.
    pub fn label(self) -> &'static str {
        match self {
            Action::AwaitDelivery => "[wait for a peer]",
            Action::StopWaiting => "[stop waiting]",
            Action::ResolveFork => "[resolve - and NAME the policy]",
        }
    }
}

/// What the cell shows for candidates.
///
/// Lean: `RenderProgress.CandidatePresentation`. `Several` carries the
/// attributed candidates here where Lean's carries nothing, for drift note 3's
/// reason — and because a fork that does not show who said what is a fork
/// rendered as a shrug.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CandidatePresentation<T> {
    /// Nothing to show.
    Nothing,
    /// One value.
    Single(T),
    /// Several values, with attribution. Never collapsed.
    Several(Vec<(T, Source)>),
}

/// **The intermediate contract.** A renderer may not go straight from a status
/// to pixels; it must first produce this.
///
/// Lean: `RenderProgress.SemanticWidget`. The point of interposing it is
/// [`constant_widget_is_honest`] returning `false`: `salience_is_not_
/// enforceable6` says a consumer into an arbitrary output type may return the
/// same thing at all six statuses, and a consumer into *this* type may not,
/// because one value cannot be both `Terminal` and `Open`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticWidget<T> {
    /// Whether the cell can still change.
    pub finality: Finality,
    /// How many candidates it holds.
    pub plurality: Plurality,
    /// The discharge the surface offers here, if any.
    pub pending_action: Option<Action>,
    /// What it shows for candidates.
    pub candidates: CandidatePresentation<T>,
}

/// **The sanctioned widget assignment, one per status.**
///
/// Lean: `RenderProgress.widgetOf`, about which `widgetOf_honest` proves the
/// five [`honest_widget`] clauses. The two that matter:
/// **`Absent` maps to `Terminal`** and **`Pending` maps to `Open`**.
pub fn widget_of<T>(status: Status<T>) -> SemanticWidget<T> {
    match status {
        Status::Exact(v) => SemanticWidget {
            finality: Finality::Terminal,
            plurality: Plurality::One,
            pending_action: None,
            candidates: CandidatePresentation::Single(v),
        },
        Status::Provisional(v) => SemanticWidget {
            finality: Finality::Open,
            plurality: Plurality::One,
            pending_action: Some(Action::AwaitDelivery),
            candidates: CandidatePresentation::Single(v),
        },
        Status::ForkedClosed(cs) => SemanticWidget {
            finality: Finality::Terminal,
            plurality: Plurality::Many,
            pending_action: Some(Action::ResolveFork),
            candidates: CandidatePresentation::Several(cs),
        },
        Status::ForkedOpen(cs) => SemanticWidget {
            finality: Finality::Open,
            plurality: Plurality::Many,
            pending_action: Some(Action::AwaitDelivery),
            candidates: CandidatePresentation::Several(cs),
        },
        Status::Absent => SemanticWidget {
            finality: Finality::Terminal,
            plurality: Plurality::Zero,
            pending_action: None,
            candidates: CandidatePresentation::Nothing,
        },
        Status::Pending => SemanticWidget {
            finality: Finality::Open,
            plurality: Plurality::Zero,
            pending_action: Some(Action::StopWaiting),
            candidates: CandidatePresentation::Nothing,
        },
    }
}

/// **What "loading" means at the interface**: the widget claims the cell is
/// still open. Everything a spinner asserts is this bit.
///
/// Lean: `RenderProgress.loading`.
pub fn loading<T>(w: &SemanticWidget<T>) -> bool {
    match w.finality {
        Finality::Terminal => false,
        Finality::Open => true,
    }
}

/// Which clause of the interface a candidate widget assignment broke.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HonestWidgetViolation {
    /// `absent → finality = terminal` failed: the surface says a definitively
    /// absent answer might still change. This is the loading-forever bug at the
    /// widget layer.
    AbsentNotTerminal,
    /// `pending → finality = open` failed: the surface asserts a spinner is
    /// final.
    PendingNotOpen,
    /// A definitively absent cell offered something to wait for.
    AbsentHasButton,
    /// A zero-candidate cell claimed candidates.
    AbsentNotZero,
    /// …including the spinner.
    PendingNotZero,
}

/// **The interface obligation**, as a runtime check.
///
/// Lean: `RenderProgress.HonestWidget` — a `Prop` with five clauses, which see
/// drift note 4. The two clauses codex names are the first two; the other three
/// keep the zero row honest about its plurality and its buttons.
///
/// The `T` here is only a type parameter of the assignment; the check needs no
/// value, because the two cells it evaluates carry none.
pub fn honest_widget<T, W>(w: W) -> Result<(), HonestWidgetViolation>
where
    W: Fn(Status<T>) -> SemanticWidget<T>,
{
    let at_absent = w(Status::Absent);
    let at_pending = w(Status::Pending);
    if at_absent.finality != Finality::Terminal {
        return Err(HonestWidgetViolation::AbsentNotTerminal);
    }
    if at_pending.finality != Finality::Open {
        return Err(HonestWidgetViolation::PendingNotOpen);
    }
    if at_absent.pending_action.is_some() {
        return Err(HonestWidgetViolation::AbsentHasButton);
    }
    if at_absent.plurality != Plurality::Zero {
        return Err(HonestWidgetViolation::AbsentNotZero);
    }
    if at_pending.plurality != Plurality::Zero {
        return Err(HonestWidgetViolation::PendingNotZero);
    }
    Ok(())
}

/// Would a **constant** widget assignment satisfy the interface?
///
/// Always `false`, and that is the theorem: Lean's
/// `RenderProgress.constant_widget_is_not_honest`. One value cannot have
/// `finality = Terminal` and `finality = Open`. This is strictly more than the
/// salience limit gives — the last hop from [`SemanticWidget`] to pixels is
/// still a function into an arbitrary type and may still be constant
/// (`salience_is_still_not_enforceable_after_the_widget`), but the *semantic*
/// layer can no longer be.
pub fn constant_widget_is_honest<T: Clone>(v: SemanticWidget<T>) -> bool {
    honest_widget(|_: Status<T>| v.clone()).is_ok()
}

/// Which soundness clause a surface broke at a named state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WidgetSoundViolation {
    /// The evidence is definitively absent and the surface did not say
    /// `Terminal`. `RenderProgress.spinner_widget_is_not_sound` is this, at
    /// `emptyClosedW`.
    LoadsAtAbsent,
    /// The evidence is open and empty and the surface did not say `Open`.
    SettlesAtPending,
}

/// **A widget-sound surface**: it reads the evidence, and its finality agrees
/// with [`status_of`] at the two zero-candidate cells.
///
/// Lean: `RenderProgress.WidgetSound`, discharged for the sanctioned renderer
/// (`sanctioned_widget_is_sound`) and refuted for the spinner
/// (`spinner_widget_is_not_sound`) — the latter at **one state**, with no
/// reasoning about futures at all.
///
/// ⚠ Drift note 5 applies: `states` is a finite sample. The Lean statement
/// quantifies over every state there is.
pub fn widget_sound<T: Ord + Clone, F>(
    surface: F,
    states: &[Evidence<T>],
) -> Result<(), (usize, WidgetSoundViolation)>
where
    F: Fn(&Evidence<T>) -> SemanticWidget<T>,
{
    for (i, e) in states.iter().enumerate() {
        let w = surface(e);
        match status_of(e) {
            Status::Absent if w.finality != Finality::Terminal => {
                return Err((i, WidgetSoundViolation::LoadsAtAbsent));
            }
            Status::Pending if w.finality != Finality::Open => {
                return Err((i, WidgetSoundViolation::SettlesAtPending));
            }
            _ => {}
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// §6. PendingSound — epistemic truth NOW (Uwueave/RenderProgress.lean §2)
// ---------------------------------------------------------------------------

/// Which honesty clause a renderer broke, and where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PendingSoundViolation {
    /// A spinner was shown where a candidate is already known.
    PendingWithCandidates,
    /// A spinner was shown where the evidence is **settled** — the answer is
    /// definitively absent and waiting cannot help. This is the clause that
    /// fires on "loading forever on an empty result", and it fires at the
    /// state itself, with no reasoning about futures.
    PendingWhileSettled,
}

/// **The epistemic honesty condition for a spinner.** A `Pending` badge is
/// honest at the state where it is shown exactly when there is no candidate and
/// the evidence is not closed.
///
/// Lean: `RenderProgress.PendingSound`, discharged for `statusOf`
/// (`statusOf_pendingSound`) and refuted for the spinner
/// (`spinnerRender_is_not_pendingSound`) at a **single state**.
///
/// ⚠ Drift note 5: `states` is a finite sample.
pub fn pending_sound<T: Ord + Clone, F>(
    peval: F,
    states: &[Evidence<T>],
) -> Result<(), (usize, PendingSoundViolation)>
where
    F: Fn(&Evidence<T>) -> Status<T>,
{
    for (i, e) in states.iter().enumerate() {
        if let Status::Pending = peval(e) {
            if !e.values().is_empty() {
                return Err((i, PendingSoundViolation::PendingWithCandidates));
            }
            if e.is_closed() {
                return Err((i, PendingSoundViolation::PendingWhileSettled));
            }
        }
    }
    Ok(())
}

/// **The discharge offer at a `Pending` cell** — what pressing the button
/// produces, and the fact that it is a permitted move.
///
/// Lean: `RenderProgress.DischargeOffer`, minus the field that carries the
/// weight there: `authorized : Authority.Active grants revoked actor`, a live
/// unrevoked delegation chain. This crate has an authority substrate
/// ([`crate::movelog::Grant`]) and wiring the offer to it is real work that
/// this slice does not do — so the button here is *unauthorised* and says so.
/// `a_revoked_actor_gets_no_button` has no analogue below.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DischargeOffer<T: Ord> {
    /// The state pressing the button produces.
    pub after: Evidence<T>,
    /// Whether the move stays inside the permitted (sealed) future.
    pub permitted: bool,
}

/// The honest discharge available with no peer cooperation: stop waiting.
///
/// Lean: the witness in `statusOf_pendingActionable`. `RenderProgress` §1's
/// sharpest observation is that this same move discharges `pending_escapable`
/// — which is why that clause is neither a truth condition nor a liveness one.
/// A clause a spinner satisfies **by giving up** is not a liveness clause.
pub fn stop_waiting<T: Ord + Clone>(e: &Evidence<T>) -> DischargeOffer<T> {
    let after = e.seal_all();
    let permitted = e.seals_to(&after);
    DischargeOffer { after, permitted }
}

// ---------------------------------------------------------------------------
// §7. The static axis — a capability, and what it declares (§2 of ResultStatus)
// ---------------------------------------------------------------------------

/// **A declared capability**: what a *declaration* may say, as opposed to what
/// an *evaluation* returns.
///
/// Lean: `ResultStatus.Capability`. Three flags, and
/// `Capability.Admits` is a hand-written table over six constructors, so a
/// capability cannot express "may fork only at closed futures". That ceiling is
/// inherited verbatim here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Capability {
    /// The computation may return zero candidates.
    pub may_be_empty: bool,
    /// The computation's answer may still be open.
    pub may_open: bool,
    /// The computation may return several incompatible candidates.
    pub may_fork: bool,
}

impl Capability {
    /// **Which statuses this capability admits.** `Exact` needs no permission —
    /// it is the status every declaration is willing to receive. Everything
    /// else costs a flag, and the two open × {zero, many} corners cost both.
    ///
    /// Lean: `ResultStatus.Capability.Admits`.
    pub fn admits<T>(&self, status: &Status<T>) -> bool {
        match status {
            Status::Exact(_) => true,
            Status::Provisional(_) => self.may_open,
            Status::ForkedClosed(_) => self.may_fork,
            Status::ForkedOpen(_) => self.may_fork && self.may_open,
            Status::Absent => self.may_be_empty,
            Status::Pending => self.may_be_empty && self.may_open,
        }
    }
}

/// **The declaration**, checked over a reach set.
///
/// Lean: `ResultStatus.Declares`. The quantifier is the content: a declaration
/// is **not** a property of the computation alone. The same evaluator satisfies
/// the same declaration over one reach set and violates it over a wider one
/// (`declaration_is_relative_to_the_reach`), and a language that lets one be
/// written without the other has hidden the quantifier that makes it false.
///
/// Returns the index of the first state whose status the capability refuses.
pub fn declares<T: Ord + Clone, F>(
    capability: Capability,
    reach: &[Evidence<T>],
    peval: F,
) -> Result<(), usize>
where
    F: Fn(&Evidence<T>) -> Status<T>,
{
    for (i, e) in reach.iter().enumerate() {
        if !capability.admits(&peval(e)) {
            return Err(i);
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// §8. Resolution, with the policy retained (§6 of ResultStatus)
// ---------------------------------------------------------------------------

/// **A resolution policy**: a named rule that selects one candidate from
/// evidence, or declines.
///
/// Lean: `ResultStatus.Policy` plus the *name*, which Lean gets for free
/// because `ResolvedBy π e` is indexed by the policy **term**. Rust cannot
/// index a type by a function, so the name is a `&'static str` we carry and
/// print. Losing it is a compiling edit — drift note 3's cousin.
pub struct Policy<T: Ord> {
    /// The rule's name. It appears in every rendering of a resolved value,
    /// because `resolved_value_is_not_a_function_of_the_evidence` says a reader
    /// who has only the value cannot reconstruct it.
    pub name: &'static str,
    /// The rule.
    pub select: Box<dyn Fn(&Evidence<T>) -> Option<T>>,
}

impl<T: Ord + Clone + 'static> Policy<T> {
    /// **Resolve by source** — take the candidate attributed to a named source.
    /// The family `resolve verdict by era_order` belongs to.
    ///
    /// Lean: `ResultStatus.bySource`. Partiality is real: a policy that names a
    /// source has nothing to say about evidence that source never contributed
    /// to.
    pub fn by_source(name: &'static str, source: Source) -> Self {
        Policy {
            name,
            select: Box::new(move |e: &Evidence<T>| {
                e.candidates().iter().find(|(_, o)| *o == source).map(|(v, _)| v.clone())
            }),
        }
    }

    /// Resolve by taking the greatest candidate value.
    pub fn greatest(name: &'static str) -> Self {
        Policy {
            name,
            select: Box::new(|e: &Evidence<T>| e.values().into_iter().next_back()),
        }
    }

    /// Apply the policy, keeping what produced the answer **and** what it
    /// suppressed.
    pub fn resolve(&self, e: &Evidence<T>) -> Option<ResolvedBy<T>> {
        (self.select)(e).map(|value| ResolvedBy {
            policy: self.name,
            value,
            alternatives: e.candidates().iter().cloned().collect(),
        })
    }
}

/// **A resolved value keeps what produced it** — and what it suppressed.
///
/// Lean: `ResultStatus.ResolvedBy π e`, where `π` and `e` are *indices of the
/// type*, so the term cannot exist without naming the policy that chose and the
/// evidence it chose from, and `alternatives_are_retained` is `rfl`.
///
/// ⚠ Here both are ordinary fields (drift note 3). `resolution_leaves_the_
/// status_alone` still holds of the design — resolving does not touch the
/// evidence, so a `ForkedClosed` that a policy read as `2` is still a
/// `ForkedClosed` — but here that is a discipline, not a theorem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedBy<T> {
    /// The rule that chose. Printed everywhere the value is.
    pub policy: &'static str,
    /// The selected value.
    pub value: T,
    /// **Every candidate, including the ones this reading suppressed.**
    pub alternatives: Vec<(T, Source)>,
}

// ---------------------------------------------------------------------------
// §9. The count, and why it may not be merged (Uwueave/JoinHom.lean)
// ---------------------------------------------------------------------------

/// **A count, recomputed from evidence rather than merged from counts.**
///
/// `JoinHom.no_count_merge_without_provenance` quantifies over **every**
/// `m : Nat → Nat → Nat` and refutes all of them: the input pair `(1, 1)` must
/// answer `1` when the two replicas saw the same element and `2` when they saw
/// different ones. A count that has forgotten *which* elements it counted
/// cannot be merged at all.
///
/// So this function takes the evidence, not two numbers, and there is
/// deliberately no `merge_counts` anywhere in this module.
pub fn count_from_evidence<T: Ord + Clone>(e: &Evidence<T>) -> usize {
    e.values().len()
}

/// **The count position's evidence, derived.**
///
/// The count is a *summary* of the mention evidence, so replicating it would be
/// the refuted architecture (`JoinHom` §5's "replicate computed summaries",
/// correct **exactly** when the summary is a `JoinHom` — and `card` is not).
/// This derives it instead: `ReplicatesEvidence`, free for every interpreter
/// with no hypothesis at all (`evidence_architecture_is_free`).
///
/// One design decision that is ours and not Lean's, stated out loud: the count
/// position holds **no candidate at all** until some source has spoken. A count
/// of `0` published before anybody has answered is a claim, not an observation
/// — it is [`give_up_render`] at the count layer, "no results" asserted while a
/// peer is still owed. So the closure structure is inherited from the mention
/// evidence and the candidate appears only once [`Evidence::heard_from`] is
/// non-empty.
pub fn count_position<T: Ord + Clone>(mentions: &Evidence<T>, derived_by: Source) -> Evidence<usize> {
    let mut out = Evidence::from_parts(
        Vec::new(),
        mentions.obligations().iter().copied(),
        mentions.certificates().iter().copied(),
    );
    if !mentions.heard_from().is_empty() {
        out.observe(count_from_evidence(mentions), derived_by);
    }
    out
}

// ---------------------------------------------------------------------------
// Tests — one per mirrored Lean theorem, each naming it.
//
// ⚠ These are UNIT TESTS. Every one of them checks a finite number of closed
// instances of a statement Lean proves for all inputs. A green suite here is
// evidence that the transcription was not obviously botched, and is not
// evidence of anything else. See the module header.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: Source = 1;
    const BOB: Source = 2;
    const CAROL: Source = 3;

    // The Lean witnesses, transcribed. `Uwueave/Evidence.lean` §9 and
    // `ResultStatus.lean` §3 name these exact states.

    /// `Evidence.exactW` — one candidate `47` from `alice`, roster closed.
    fn exact_w() -> Evidence<u64> {
        Evidence::from_parts([(47, ALICE)], [ALICE], [ALICE])
    }
    /// `Evidence.openW` — the same candidate, `bob` still owed.
    fn open_w() -> Evidence<u64> {
        Evidence::from_parts([(47, ALICE)], [ALICE, BOB], [ALICE])
    }
    /// `Evidence.forkedClosedW` — `47` and `49`, roster closed.
    fn forked_closed_w() -> Evidence<u64> {
        Evidence::from_parts([(47, ALICE), (49, BOB)], [ALICE, BOB], [ALICE, BOB])
    }
    /// `Evidence.openForkW` — `47` and `49`, `bob` still owed.
    fn open_fork_w() -> Evidence<u64> {
        Evidence::from_parts([(47, ALICE), (49, BOB)], [ALICE, BOB], [ALICE])
    }
    /// `ResultStatus.emptyClosedW` — **definitive absence**. No candidates, and
    /// the only source owed is certified.
    fn empty_closed_w() -> Evidence<u64> {
        Evidence::from_parts([], [ALICE], [ALICE])
    }
    /// `ResultStatus.emptyOpenW` — **nothing observed yet**. Same empty
    /// candidate set, `bob` still owed.
    fn empty_open_w() -> Evidence<u64> {
        Evidence::from_parts([], [ALICE, BOB], [ALICE])
    }
    /// `ResultStatus.bobSpokeW` — the sealed future of `emptyOpenW` in which
    /// `bob` contributes `47`.
    fn bob_spoke_w() -> Evidence<u64> {
        Evidence::from_parts([(47, BOB)], [ALICE, BOB], [ALICE])
    }

    // -- §1. the six inversion lemmas ---------------------------------------

    #[test]
    // mirrors ResultStatus.statusOf_exact / statusOf_provisional /
    // statusOf_forkedClosed / statusOf_forkedOpen / statusOf_absent /
    // statusOf_pending — and ResultStatus.statusOf_exactW, statusOf_openW,
    // statusOf_forkedClosedW, statusOf_openForkW, statusOf_emptyClosedW,
    // statusOf_emptyOpenW at the named witnesses.
    fn six_inversion_lemmas_at_the_lean_witnesses() {
        assert_eq!(status_of(&exact_w()), Status::Exact(47));
        assert_eq!(status_of(&open_w()), Status::Provisional(47));
        assert_eq!(
            status_of(&forked_closed_w()),
            Status::ForkedClosed(vec![(47, ALICE), (49, BOB)])
        );
        assert_eq!(status_of(&open_fork_w()), Status::ForkedOpen(vec![(47, ALICE), (49, BOB)]));
        assert_eq!(status_of(&empty_closed_w()), Status::Absent);
        assert_eq!(status_of(&empty_open_w()), Status::Pending);
        // …and all six tags are distinct: ResultStatus.status_ne_of_tag.
        let tags: BTreeSet<u8> = [
            status_of(&exact_w()).tag(),
            status_of(&open_w()).tag(),
            status_of(&forked_closed_w()).tag(),
            status_of(&open_fork_w()).tag(),
            status_of(&empty_closed_w()).tag(),
            status_of(&empty_open_w()).tag(),
        ]
        .into_iter()
        .collect();
        assert_eq!(tags.len(), 6);
    }

    #[test]
    // mirrors Evidence.values / Holes.SealsTo: two sources that AGREE are not a
    // fork, because `values` forgets the attribution. The fork is a
    // disagreement about the value, never about who spoke.
    fn agreement_between_two_sources_is_exact_not_forked() {
        let e: Evidence<u64> = Evidence::from_parts([(47, ALICE), (47, BOB)], [ALICE, BOB], [ALICE, BOB]);
        assert_eq!(status_of(&e), Status::Exact(47));
    }

    // -- §3. the sixth cell -------------------------------------------------

    #[test]
    // mirrors ResultStatus.forget_statusOf — forgetting the zero-row split
    // returns the five-cell view on the nose, so the six-cell status is a
    // refinement rather than a rival.
    fn forget_status_of_is_the_five_cell_view() {
        assert_eq!(forget(status_of(&exact_w())), View::Exact(47));
        assert_eq!(forget(status_of(&open_w())), View::Provisional(47));
        assert_eq!(forget(status_of(&forked_closed_w())), View::ForkedClosed);
        assert_eq!(forget(status_of(&open_fork_w())), View::ForkedOpen);
        assert_eq!(forget(status_of(&empty_closed_w())), View::Vacuous);
        assert_eq!(forget(status_of(&empty_open_w())), View::Vacuous);
    }

    #[test]
    // mirrors ResultStatus.sixth_cell_is_distinguishable — two evidences with
    // the SAME (empty) candidate set: the fold sends both to `vacuous`, the
    // split sends them to `absent` and `pending`, and their rendered answers
    // have OPPOSITE stability.
    fn sixth_cell_is_distinguishable() {
        let closed = empty_closed_w();
        let open = empty_open_w();
        assert_eq!(closed.values(), open.values(), "same candidate set — both empty");

        // the fold cannot tell them apart
        assert_eq!(forget(status_of(&closed)), View::Vacuous);
        assert_eq!(forget(status_of(&open)), View::Vacuous);
        // the split can
        assert_eq!(status_of(&closed), Status::Absent);
        assert_eq!(status_of(&open), Status::Pending);

        // opposite stability: the closed one survives its sealed futures…
        let sealed = closed.seal_all();
        assert!(closed.seals_to(&sealed));
        assert_eq!(status_of(&sealed), Status::Absent);
        // …and the open one does not survive even one.
        let spoke = bob_spoke_w();
        assert!(open.seals_to(&spoke), "bob is owed and uncertified, so his arrival is sealed");
        assert_eq!(status_of(&spoke), Status::Provisional(47));
        assert_ne!(status_of(&spoke), status_of(&open));
    }

    #[test]
    // mirrors ResultStatus.empty_status_final_under_sealed — a closed, empty
    // evidence keeps its `absent` badge at every sealed future.
    fn empty_status_final_under_sealed() {
        let closed = empty_closed_w();
        // Every sealed future of a closed evidence has the same candidate set,
        // so enumerate a few and check the badge does not move.
        let futures = [closed.clone(), closed.seal_all(), {
            let mut c = closed.clone();
            c.certify(ALICE);
            c
        }];
        for t in &futures {
            assert!(closed.seals_to(t));
            assert_eq!(status_of(t), Status::Absent);
        }
    }

    #[test]
    // mirrors ResultStatus.absence_survives_values_not_closure — the price of
    // the split, paid in public. Admit ONE source nobody had heard of and
    // `absent` re-opens to `pending`, with an IDENTICAL (empty) candidate set.
    // The extension future permits it; the sealed future does not.
    fn absence_survives_values_not_closure() {
        let closed = empty_closed_w();
        let widened = empty_open_w();
        assert_eq!(closed.candidates(), widened.candidates(), "identical candidate sets");
        assert!(closed.extends_to(&widened), "a roster growth is an extension future");
        assert!(!closed.seals_to(&widened), "…and is NOT a sealed one");
        assert_eq!(status_of(&closed), Status::Absent);
        assert_eq!(status_of(&widened), Status::Pending);
    }

    #[test]
    // mirrors ResultStatus.absence_outlives_exactness — absence is the MOST
    // stable of the six cells: an `exact` report re-opens when a source nobody
    // knew about is admitted, and an `absent` one has no value to re-open.
    fn absence_outlives_exactness() {
        // exact, then a new source appears
        let exact = exact_w();
        let widened = open_w();
        assert!(exact.extends_to(&widened));
        assert_eq!(status_of(&exact), Status::Exact(47));
        assert_eq!(status_of(&widened), Status::Provisional(47), "the exact report was retracted");

        // absent, under every SEALED future: unmoved
        let absent = empty_closed_w();
        for t in [absent.clone(), absent.seal_all()] {
            assert!(absent.seals_to(&t));
            assert_eq!(status_of(&t), Status::Absent);
        }
    }

    // -- §5. value-dependent exactness --------------------------------------

    #[test]
    // mirrors ResultStatus.anyCandidate_true_is_self_certifying — once some
    // candidate satisfies `p`, no permitted future retracts it, using nothing
    // but ⊑ and with NO closure hypothesis at all.
    fn any_candidate_true_is_self_certifying() {
        let e = open_fork_w();
        let is49 = |v: &u64| *v == 49;
        assert!(e.any_candidate(is49));
        // any extension future — including a roster growth, the widest move
        let mut wider = e.clone();
        wider.owe(CAROL);
        wider.observe(50, CAROL);
        assert!(e.extends_to(&wider) || e.leq(&wider), "growth is monotone either way");
        assert!(wider.any_candidate(is49), "grow-only sets never lose a witness they already have");
    }

    #[test]
    // mirrors ResultStatus.anyCandidate_false_stays_open — at any uncertified
    // obligation the `false` answer flips in a SEALED future, so a `false` is
    // never final while anything is owed.
    fn any_candidate_false_stays_open() {
        let e = open_w();
        let is49 = |v: &u64| *v == 49;
        assert!(!e.any_candidate(is49));
        assert!(e.obligations().contains(&BOB) && !e.certificates().contains(&BOB));
        let mut t = e.clone();
        t.observe(49, BOB);
        assert!(e.seals_to(&t), "an arrival from an owed, uncertified source is sealed");
        assert!(t.any_candidate(is49), "the answer flipped");
    }

    #[test]
    // mirrors ResultStatus.closed_settles_every_value_query — closure is
    // sufficient: any query reading only the candidate values is final at a
    // closed evidence, because the candidate set cannot move.
    fn closed_settles_every_value_query() {
        let e = forked_closed_w();
        assert!(e.is_closed());
        // Every sealed future of a closed evidence admits no new candidate.
        let mut attempt = e.clone();
        attempt.observe(51, BOB);
        assert!(!e.admits(&attempt), "BOB is certified, so nothing more may arrive from him");
        assert!(!e.seals_to(&attempt));
        // and the sealed futures that DO exist leave the values alone
        let sealed = e.seal_all();
        assert!(e.seals_to(&sealed));
        assert_eq!(sealed.values(), e.values());
    }

    #[test]
    // mirrors ResultStatus.exactness_is_value_dependent — ONE query, two
    // evidences with IDENTICAL obligations and IDENTICAL certificates, and
    // opposite finality, decided by nothing but which value the candidate set
    // currently holds.
    fn exactness_is_value_dependent() {
        let a = open_w();
        let b = open_fork_w();
        assert_eq!(a.obligations(), b.obligations());
        assert_eq!(a.certificates(), b.certificates());
        let is49 = |v: &u64| *v == 49;
        assert!(!a.any_candidate(is49), "openW does not hold 49 — retractable");
        assert!(b.any_candidate(is49), "openForkW holds 49 — immovable");
        // …so there is no closure fact separating them, because there is none.
    }

    #[test]
    // mirrors ResultStatus.finality_is_not_a_function_of_the_closure_structure
    // — the retreat "let the declaration read the frontier and the
    // certificates" fails at the same witnesses: equal obligations, equal
    // certificates, different truth. Any such function answers the same at both.
    fn finality_is_not_a_function_of_the_closure_structure() {
        let a = open_w();
        let b = open_fork_w();
        let closure_key =
            |e: &Evidence<u64>| (e.obligations().clone(), e.certificates().clone());
        assert_eq!(closure_key(&a), closure_key(&b), "the entire closure structure agrees");
        let is49 = |v: &u64| *v == 49;
        assert_ne!(a.any_candidate(is49), b.any_candidate(is49), "and the truth does not");
    }

    #[test]
    // mirrors ResultStatus.existential_has_no_static_finality — neither
    // constant verdict survives, which is the argument for one epistemic
    // carrier over four coarse static types.
    fn existential_has_no_static_finality() {
        let reach = [open_w(), open_fork_w()];
        let is49 = |v: &u64| *v == 49;
        let all_final = reach.iter().all(|e| e.any_candidate(is49));
        let none_final = reach.iter().all(|e| !e.any_candidate(is49));
        assert!(!all_final && !none_final, "no constant finality verdict describes this reach set");
    }

    // -- §2. the declaration is relative to the reach -----------------------

    #[test]
    // mirrors ResultStatus.declaration_is_relative_to_the_reach — the SAME
    // evaluator and the SAME capability, satisfied over one state set and
    // refuted over a wider one that is closed under a single admissible
    // extension.
    fn declaration_is_relative_to_the_reach() {
        // `mayPend`: one value, possibly still pending, never a fork — what
        // `derive verdict : Claim` means when nobody writes a modality.
        let may_pend = Capability { may_be_empty: false, may_open: true, may_fork: false };
        let settled = [exact_w(), open_w()];
        let with_fork = [exact_w(), open_w(), open_fork_w()];
        assert!(declares(may_pend, &settled, status_of).is_ok());
        assert_eq!(declares(may_pend, &with_fork, status_of), Err(2));
        // …and the wider reach set is not exotic: it is the first one closed
        // under one admissible extension.
        assert!(open_w().extends_to(&open_fork_w()));
    }

    // -- §4/§5 of RenderSix. the two dishonest renderers ---------------------

    #[test]
    // mirrors RenderSix.spinnerRender_folds_to_render and
    // giveUpRender_folds_to_render — THE FOLD CANNOT SEE THE LIE, because the
    // lie lives exactly where the fold is.
    fn the_fold_cannot_see_either_lie() {
        for e in [empty_closed_w(), empty_open_w(), exact_w(), forked_closed_w()] {
            assert_eq!(forget(spinner_render(&e)), forget(status_of(&e)));
            assert_eq!(forget(give_up_render(&e)), forget(status_of(&e)));
        }
    }

    #[test]
    // mirrors RenderSix.spinnerRender_spins_forever — the spinner has NO
    // permitted future at which it stops, because `emptyClosedW` is closed and
    // a closed absence is final under every sealed future.
    fn spinner_render_spins_forever() {
        let e = empty_closed_w();
        assert_eq!(spinner_render(&e), Status::Pending);
        for t in [e.clone(), e.seal_all()] {
            assert!(e.seals_to(&t));
            assert_eq!(spinner_render(&t), Status::Pending, "still spinning");
        }
    }

    #[test]
    // mirrors RenderSix.spinnerRender_correct_where_it_is_made — not locally
    // false. At `emptyClosedW` the answer set really IS empty; what is false is
    // that waiting might help.
    fn spinner_render_is_correct_where_it_is_made() {
        assert!(empty_closed_w().values().is_empty());
    }

    #[test]
    // mirrors RenderSix.giveUpRender_is_not_sound6 — refuted by the OPPOSITE
    // clause: it reports `absent` at `emptyOpenW`, and the sealed future in
    // which bob contributes 47 reports `provisional 47`, so a definitive
    // absence was RETRACTED.
    fn give_up_render_retracts_an_absence() {
        let e = empty_open_w();
        assert_eq!(give_up_render(&e), Status::Absent);
        let t = bob_spoke_w();
        assert!(e.seals_to(&t));
        assert_eq!(give_up_render(&t), Status::Provisional(47), "the absence was retracted");
    }

    #[test]
    // mirrors RenderSix.statusOf_sound6's `absent_final` and `exact_final`
    // clauses — the sanctioned renderer retracts neither badge along a sealed
    // future.
    fn status_of_is_sound_at_the_two_final_cells() {
        let absent = empty_closed_w();
        for t in [absent.clone(), absent.seal_all()] {
            assert!(absent.seals_to(&t));
            assert_eq!(status_of(&t), Status::Absent);
        }
        let exact = exact_w();
        for t in [exact.clone(), exact.seal_all()] {
            assert!(exact.seals_to(&t));
            assert_eq!(status_of(&t), Status::Exact(47));
        }
    }

    // -- RenderProgress §1–§2. give-up, and epistemic truth -----------------

    #[test]
    // mirrors RenderProgress.sealAll_keeps_candidates + closed_sealAll +
    // sealed_sealAll — giving up deletes no evidence, closes the roster, and is
    // a PERMITTED move.
    fn seal_all_gives_up_without_deleting_anything() {
        let e = empty_open_w();
        let after = e.seal_all();
        assert_eq!(after.candidates(), e.candidates(), "nothing was delivered or deleted");
        assert!(after.is_closed());
        assert!(e.seals_to(&after), "the give-up move is inside the permitted future");
    }

    #[test]
    // mirrors RenderProgress.statusOf_pending_escapable_by_sealing and
    // the_old_clause_is_discharged_by_giving_up — `pending_escapable` is
    // satisfied by "give up on every peer", with NO candidate arriving at all.
    // A clause a spinner satisfies by giving up is not a liveness clause.
    fn pending_escapable_is_discharged_by_giving_up() {
        let e = empty_open_w();
        assert_eq!(status_of(&e), Status::Pending);
        let offer = stop_waiting(&e);
        assert!(offer.permitted);
        assert_ne!(status_of(&offer.after), Status::Pending);
        assert_eq!(status_of(&offer.after), Status::Absent);
        assert_eq!(offer.after.candidates(), e.candidates(), "nothing arrived");
    }

    #[test]
    // mirrors RenderProgress.statusOf_pendingSound — the sanctioned renderer's
    // `pending` inversion is exactly the two clauses.
    fn status_of_is_pending_sound() {
        let states =
            [exact_w(), open_w(), forked_closed_w(), open_fork_w(), empty_closed_w(), empty_open_w()];
        assert!(pending_sound(status_of, &states).is_ok());
    }

    #[test]
    // mirrors RenderProgress.spinnerRender_is_not_pendingSound — THE SPINNER IS
    // REFUTED AT ONE STATE. No "spins forever" argument is needed, only the
    // fact that `emptyClosedW` is closed.
    fn spinner_render_is_not_pending_sound() {
        let states = [empty_closed_w()];
        assert_eq!(
            pending_sound(spinner_render, &states),
            Err((0, PendingSoundViolation::PendingWhileSettled))
        );
    }

    #[test]
    // mirrors RenderProgress.escapability_does_not_imply_epistemic_truth —
    // `unrelatedEscape` satisfies the escapability clause at every state and is
    // still an epistemic lie at a named one.
    fn escapability_does_not_imply_epistemic_truth() {
        let watched = BOB;
        let render = |e: &Evidence<u64>| unrelated_escape(e, watched);
        // it escapes everywhere: certifying BOB is always a sealed future
        for e in [empty_closed_w(), empty_open_w(), open_w()] {
            if let Status::Pending = render(&e) {
                let mut t = e.clone();
                t.certify(watched);
                assert!(e.seals_to(&t));
                assert_ne!(render(&t), Status::Pending);
            }
        }
        // …and it lies at `emptyClosedW`, where statusOf says `absent`
        let states = [empty_closed_w()];
        assert_eq!(status_of(&states[0]), Status::Absent);
        assert_eq!(
            pending_sound(render, &states),
            Err((0, PendingSoundViolation::PendingWhileSettled))
        );
    }

    // -- RenderProgress §7. the semantic widget ------------------------------

    #[test]
    // mirrors RenderProgress.widgetOf_honest — the sanctioned assignment
    // satisfies all five interface clauses.
    fn widget_of_is_honest() {
        assert_eq!(honest_widget(widget_of::<u64>), Ok(()));
    }

    #[test]
    // mirrors RenderProgress.no_honest_widget_loads_at_absent — a dishonest
    // `loading = true` at `absent` is EXCLUDED. This is the loading-forever bug
    // refuted at the type rather than at a future.
    fn no_honest_widget_loads_at_absent() {
        assert_eq!(honest_widget(widget_of::<u64>), Ok(()));
        assert!(!loading(&widget_of(Status::<u64>::Absent)));
    }

    #[test]
    // mirrors RenderProgress.honest_widget_loads_at_pending — and the bit is
    // not constantly `false`: the spinner cell DOES load.
    fn honest_widget_loads_at_pending() {
        assert!(loading(&widget_of(Status::<u64>::Pending)));
    }

    #[test]
    // mirrors RenderProgress.constant_widget_is_not_honest — a CONSTANT
    // assignment is excluded outright, which is strictly more than the salience
    // limit gives. One value cannot be both terminal and open.
    fn constant_widget_is_not_honest() {
        for v in [
            widget_of(Status::<u64>::Absent),
            widget_of(Status::<u64>::Pending),
            widget_of(Status::Exact(47u64)),
        ] {
            assert!(!constant_widget_is_honest(v));
        }
    }

    #[test]
    // mirrors RenderProgress.sanctioned_widget_is_sound and
    // spinner_widget_is_not_sound — the second at ONE state, with no reasoning
    // about futures.
    fn sanctioned_widget_is_sound_and_the_spinner_is_not() {
        let states =
            [exact_w(), open_w(), forked_closed_w(), open_fork_w(), empty_closed_w(), empty_open_w()];
        assert!(widget_sound(|e| widget_of(status_of(e)), &states).is_ok());

        let one = [empty_closed_w()];
        assert_eq!(
            widget_sound(|e| widget_of(spinner_render(e)), &one),
            Err((0, WidgetSoundViolation::LoadsAtAbsent))
        );
    }

    #[test]
    // mirrors RenderProgress.widget_sound_surface_cannot_load_at_absent — any
    // widget-sound surface returns loading = false at every definitively absent
    // evidence.
    fn widget_sound_surface_cannot_load_at_absent() {
        let states = [empty_closed_w(), empty_open_w()];
        let surface = |e: &Evidence<u64>| widget_of(status_of(e));
        assert!(widget_sound(surface, &states).is_ok());
        for e in &states {
            if let Status::Absent = status_of(e) {
                assert!(!loading(&surface(e)));
            }
        }
    }

    #[test]
    // mirrors RenderProgress.salience_is_still_not_enforceable_after_the_widget
    // — THE LIMIT THAT SURVIVES, said plainly. The last hop from the widget to
    // pixels is a function into an arbitrary type and constant functions still
    // exist: six statuses, six distinct widgets, one grey pixel.
    fn salience_is_still_not_enforceable_after_the_widget() {
        let paint = |_w: &SemanticWidget<u64>| "▓";
        let all = [
            widget_of(Status::Exact(47u64)),
            widget_of(Status::Provisional(47u64)),
            widget_of(Status::ForkedClosed(vec![(47u64, ALICE), (49, BOB)])),
            widget_of(Status::ForkedOpen(vec![(47u64, ALICE), (49, BOB)])),
            widget_of(Status::<u64>::Absent),
            widget_of(Status::<u64>::Pending),
        ];
        // the widgets really are six distinct objects…
        for (i, a) in all.iter().enumerate() {
            for b in all.iter().skip(i + 1) {
                assert_ne!(a, b);
            }
        }
        // …and the paint collapses them anyway.
        assert!(all.iter().all(|w| paint(w) == "▓"));
    }

    // -- §6 of ResultStatus. resolution -------------------------------------

    #[test]
    // mirrors ResultStatus.policies_disagree_on_a_fork and
    // resolved_value_is_not_a_function_of_the_evidence — there is NO function
    // from evidence to value that every resolution agrees with, so a design
    // that drops the policy has destroyed information nothing can recover.
    fn resolved_value_is_not_a_function_of_the_evidence() {
        let e = forked_closed_w();
        let by_alice = Policy::by_source("bySource(alice)", ALICE);
        let by_bob = Policy::by_source("bySource(bob)", BOB);
        let ra = by_alice.resolve(&e);
        let rb = by_bob.resolve(&e);
        match (ra, rb) {
            (Some(ra), Some(rb)) => {
                assert_eq!(ra.value, 47);
                assert_eq!(rb.value, 49);
                assert_ne!(ra.value, rb.value, "same evidence, different values");
                assert_ne!(ra.policy, rb.policy);
            }
            other => panic!("both policies name a source that contributed: {other:?}"),
        }
    }

    #[test]
    // mirrors ResultStatus.alternatives_are_retained and
    // resolution_leaves_the_status_alone — a resolved fork is still a fork.
    // Selection is a READING, stored beside the fork rather than in place of it.
    fn resolution_leaves_the_status_alone() {
        let e = forked_closed_w();
        let policy = Policy::by_source("bySource(alice)", ALICE);
        match policy.resolve(&e) {
            Some(r) => {
                assert_eq!(r.alternatives, vec![(47, ALICE), (49, BOB)], "nothing suppressed");
                assert_eq!(
                    status_of(&e),
                    Status::ForkedClosed(vec![(47, ALICE), (49, BOB)]),
                    "the underlying status is what it was before anyone resolved"
                );
            }
            None => panic!("alice contributed a candidate"),
        }
    }

    #[test]
    // mirrors ResultStatus.bySource's partiality — a policy that names a source
    // has nothing to say about evidence that source never contributed to.
    fn a_policy_may_decline() {
        let e = empty_closed_w();
        let policy: Policy<u64> = Policy::by_source("bySource(bob)", BOB);
        assert!(policy.resolve(&e).is_none());
    }

    // -- Evidence.lean. the two merge verdicts ------------------------------

    #[test]
    // mirrors Evidence.closed_iconfluent — closure survives merge with no
    // coordination: two replicas that have each closed their own futures merge
    // to a closed future.
    fn closure_is_iconfluent() {
        let a: Evidence<u64> = Evidence::from_parts([(1, ALICE)], [ALICE], [ALICE]);
        let b: Evidence<u64> = Evidence::from_parts([(2, BOB)], [BOB], [BOB]);
        assert!(a.is_closed() && b.is_closed());
        assert!(a.merged(&b).is_closed(), "closure needs no agreement");
    }

    #[test]
    // mirrors Holes.determinacy_not_iconfluent (the CONTRAST) — "exactly one
    // candidate" does NOT survive merge. Two replicas each holding one value
    // merge to a fork, and this is the reason the fork cell exists at all.
    fn determinacy_is_not_iconfluent() {
        let a: Evidence<u64> = Evidence::from_parts([(1, ALICE)], [ALICE], [ALICE]);
        let b: Evidence<u64> = Evidence::from_parts([(2, BOB)], [BOB], [BOB]);
        assert_eq!(status_of(&a), Status::Exact(1));
        assert_eq!(status_of(&b), Status::Exact(2));
        assert_eq!(status_of(&a.merged(&b)), Status::ForkedClosed(vec![(1, ALICE), (2, BOB)]));
    }

    #[test]
    // mirrors RenderProgress.values_merge — a value in the merge came from one
    // side, which is why the merged fork can name who said what.
    fn values_merge_distributes() {
        let a: Evidence<u64> = Evidence::from_parts([(1, ALICE)], [ALICE], []);
        let b: Evidence<u64> = Evidence::from_parts([(2, BOB)], [BOB], []);
        let m = a.merged(&b);
        for v in m.values() {
            assert!(a.values().contains(&v) || b.values().contains(&v));
        }
    }

    #[test]
    // mirrors RenderProgress.anyCandidate_true_iconfluent — a grow-only
    // existential's `true` is merge-safe UNILATERALLY: one replica's `true`
    // survives a merge with an arbitrary peer, no agreement needed. On the merge
    // axis this is a STRONGER badge than absence, which needs both replicas.
    fn any_candidate_true_is_unilaterally_merge_safe() {
        let a = open_fork_w();
        let is49 = |v: &u64| *v == 49;
        assert!(a.any_candidate(is49));
        for peer in [exact_w(), empty_closed_w(), empty_open_w(), Evidence::new()] {
            assert!(a.merged(&peer).any_candidate(is49));
        }
    }

    #[test]
    // mirrors RenderProgress.absence_is_not_unilaterally_merge_closed — and the
    // correction cuts the other way: `absent` needs BOTH replicas to assert it.
    fn absence_is_not_unilaterally_merge_closed() {
        let mine: Evidence<u64> = Evidence::from_parts([], [ALICE], [ALICE]);
        assert_eq!(status_of(&mine), Status::Absent);
        let peer: Evidence<u64> = Evidence::from_parts([(47, BOB)], [BOB], [BOB]);
        assert_eq!(status_of(&mine.merged(&peer)), Status::Exact(47), "my absence did not survive");
    }

    // -- JoinHom.lean. the count ---------------------------------------------

    #[test]
    // mirrors JoinHom.no_count_merge_without_provenance — NO binary function on
    // the two raw counts can be exact. The input pair (1, 1) must answer 1 when
    // the replicas saw the same element and 2 when they saw different ones.
    fn no_count_merge_without_provenance() {
        // both replicas saw one mention — the SAME one
        let same_a: Evidence<&str> = Evidence::from_parts([("n1", ALICE)], [], []);
        let same_b: Evidence<&str> = Evidence::from_parts([("n1", BOB)], [], []);
        // both replicas saw one mention — DIFFERENT ones
        let diff_a: Evidence<&str> = Evidence::from_parts([("n1", ALICE)], [], []);
        let diff_b: Evidence<&str> = Evidence::from_parts([("n2", BOB)], [], []);

        assert_eq!(count_from_evidence(&same_a), 1);
        assert_eq!(count_from_evidence(&same_b), 1);
        assert_eq!(count_from_evidence(&diff_a), 1);
        assert_eq!(count_from_evidence(&diff_b), 1);

        let merged_same = count_from_evidence(&same_a.merged(&same_b));
        let merged_diff = count_from_evidence(&diff_a.merged(&diff_b));
        assert_eq!(merged_same, 1);
        assert_eq!(merged_diff, 2);
        assert_ne!(
            merged_same, merged_diff,
            "identical result pairs (1,1), different merged counts — so no m : Nat -> Nat -> Nat works"
        );
    }

    #[test]
    // mirrors JoinHom's `ReplicatesEvidence` / evidence_architecture_is_free —
    // the count position holds NO candidate until some source has spoken,
    // because a 0 published before anybody answers is `giveUpRender` at the
    // count layer.
    fn count_position_is_pending_before_anyone_speaks() {
        const DERIVED: Source = 99;
        let mut mentions: Evidence<&str> = Evidence::new();
        mentions.owe(ALICE).owe(BOB);
        assert_eq!(status_of(&count_position(&mentions, DERIVED)), Status::Pending);

        mentions.observe("n1", ALICE);
        assert_eq!(status_of(&count_position(&mentions, DERIVED)), Status::Provisional(1));

        mentions.observe("n2", BOB);
        mentions.certify(ALICE).certify(BOB);
        assert_eq!(status_of(&count_position(&mentions, DERIVED)), Status::Exact(2));
    }

    #[test]
    // mirrors JoinHom's classification of `card` as `needsEvidence` — the
    // summary-replicated count and the evidence-replicated count DISAGREE, and
    // the summary one is confidently, terminally wrong.
    fn replicating_the_summary_lands_on_a_wrong_exact() {
        // Both replicas counted 1, and they counted DIFFERENT notes.
        let mentions_a: Evidence<&str> = Evidence::from_parts([("n1", ALICE)], [ALICE, BOB], [ALICE]);
        let mentions_b: Evidence<&str> = Evidence::from_parts([("n2", BOB)], [ALICE, BOB], [BOB]);

        // WRONG: replicate the numbers. Both say 1, so `values` folds them to
        // one value and the position reports a confident `Exact(1)`.
        let summary: Evidence<usize> =
            Evidence::from_parts([(1, ALICE), (1, BOB)], [ALICE, BOB], [ALICE, BOB]);
        assert_eq!(status_of(&summary), Status::Exact(1));

        // RIGHT: replicate the evidence and recompute.
        let merged = mentions_a.merged(&mentions_b);
        assert_eq!(count_from_evidence(&merged), 2);
        assert_eq!(status_of(&count_position(&merged, 99)), Status::Exact(2));
    }
}
