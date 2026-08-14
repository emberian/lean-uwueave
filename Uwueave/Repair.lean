/-
# Uwueave.Repair — a repair is a typed transformation between promises, and its price is not a number.

**This file exists because codex's second review refused the shape we proposed.**
We had drafted exits as a flat `inductive Exit` with a `Nat` price. He objected on
two counts, and both objections are the design of this file:

  * **(a) Prices are multidimensional.** "Arbitration costs 0 meetings" is false.
    Era costs a trusted announcement and a rollback window; an MV-register
    changes the output contract from singular to plural; escrow costs rights
    allocation; retaining evidence costs storage and replay. Collapsing those to
    one `Nat` — a crossing count — **manufactures attractive false zeroes**, and
    `crossings_cannot_see_the_difference` below is that objection as a theorem:
    three repairs that differ in kind are *equal* when read through the crossing
    count alone.
  * **(b) A repair is a typed transformation between SPECIFICATIONS, not a value
    in a list.** "Arbitrate", "fork", "weaken the invariant" and "retain more
    metadata" do different things to the promise, and the failure mode is a
    solver that meets a budget by silently solving a **different** application
    problem. `Repair P Q` names both promises in its type; `PromiseRelation`
    records exactly which axes survived; and `weakened_chain_is_not_the_original`
    is the refutation that stops a weakening chain from being presented as
    satisfying what was originally promised.

## Relation to `Uwueave/Exits.lean` (sibling, landed)

`Exits.lean` is the **enumeration**: eight named exits over one promise, each
with an `Applies` predicate and a `Nat` price, assembled into an `ExitMenu` a
caller can read off. It answers *"what are my options?"*. This file is the
**typed successor**: an exit becomes a morphism `Repair P Q` between two
promises, its price becomes a record with one field per currency, and its effect
on the promise becomes a five-axis `PromiseRelation` that **composes**. Where the
menu prices `arbitration` and `fork` both at `0` and warns in a docstring that
the two zeroes are not the same zero (its own ⟨scope⟩ note), this file makes them
different *values* and proves it (`crossings_cannot_see_the_difference`). Neither
file subsumes the other's job: a menu is what a report shows a schema author, a
`Repair` is what a chain of them composes as. Nothing here imports `Exits.lean`.

## What is here

  * **§1 `Premise`** — the trust assumptions this tree actually contains, as an
    enumeration, so an assumption can be *charged* rather than mentioned.
  * **§2 `Price`** — eight fields, each tied to a semantic distinction, with a
    commutative monoid structure so chains accumulate.
  * **§4 `PromiseRelation`** — five independent Bool axes, composing by `&&`. The
    five names codex listed (equivalent · strengthened · weakened ·
    changed-observation · changed-trust) are recovered as inhabitants — and two
    of the four repairs below need **several of them at once** (arbitration needs
    three, forking needs two), which is a finding, not an encoding accident
    (`arbitration_needs_three_names`, `fork_is_changed_observation_and_weakened`).
    A fifth axis, `shrinkageKept`, is not on codex's list at all and is the one
    arbitration is most often reported without.
  * **§5 `Promise`** — an invariant, plus the observation context (`Demand` and
    `admits`) and trust context the axes need. Minimal: six fields, and every one
    is read by an axis or by a price field.
  * **§7 `Repair P Q`** — transform, relation, price, discharge, and one
    soundness obligation per axis, each *guarded by its flag*: you cannot claim
    an axis you have not proved, and `premisesCharged` is unconditional — every
    premise the target promise leans on that the source did not **must** appear
    in the price. `introduced_premise_forces_a_charge` turns that field into a
    theorem (a repair that introduces a premise cannot price at `Price.free`),
    and `no_free_arbitration` instantiates it at the exit codex's objection was
    about: quantified over **every** repair onto the arbitrated promise, by
    anyone, "arbitration costs nothing" is not a report this type can print.
  * **§8** the four typed repairs: seam, arbitration, fork, retain-evidence
    (plus a fifth, weakening, which exists to be refuted in §9).
  * **§9** composition, and the guard.

## The 2×2 the typing exposes

Two of the four repairs (**seam**, **retain-evidence**) are the *identity* on the
promise: same carrier, same invariant, same observation, same trust. Their entire
content is the `price` and the `discharge` — they are **deployment** changes.
The other two (**arbitration**, **fork**) change the promise itself, and their
relations say how. Before this file that distinction had nowhere to live: in a
flat enum all four are peers in one list.

## Non-claims, labelled

  * ⟨UNDONE U-0121, narrowed to unrestricted candidate discovery⟩ **No unrestricted
    search.** A `Repair` is a value someone *constructs*. Downstream
    `RepairSynthesis` and `FiniteRepairMenu` search an explicitly supplied finite
    catalog and return exhaustive refusal only inside it; they do not discover a
    non-trivial seam, an escrow partition, or a complete universe of repairs.
  * ⟨UNDONE U-0122⟩ **`Price.add` is a declared accumulation, not a minimum.** Chaining
    adds the fields. It is NOT claimed that the sum is the least price achievable
    for the composite: `SeamAlgebra.linked_segmented` is a case where two seams
    share one crossing, and codex's own structural verdict on our cost measure
    (`min_σ (c₁ + c₂) ≠ min_σ c₁ + min_σ c₂`) says a scalar minimum is not
    compositional at all. A cost *profile over the strategy space*, minimised only
    when the session closes, is what a budgeting language needs; this is not it.
  * ⟨UNDONE U-0123⟩ **`singularObservation` is the provable fragment of "the
    observation changed".** A full account would compare `Demand` types up to
    equivalence and say what downstream must rewrite. What is proved here is the
    one component this tree can refute: singularity of the read
    (`fork_loses_singularity`). A repair that changes the observation type while
    keeping singularity is not distinguished by this axis.
  * ⟨UNDONE U-0124⟩ **`rollbackWindow` is a declared bound, not a derived one.**
    `Era.final_view_immune` proves the exposure is confined to the *pending*
    suffix — that the window exists and is not everything. Nothing here computes
    its size from a log, so the field is an author's claim about their own
    deployment, checked by nothing.
  * ⟨TERMINAL⟩ **The carriers are miniatures.** Every promise below is built on
    a carrier that already lives in this tree (`Segmented.QuotaState`,
    `Seams.EpochState`, `MVRegister.MVReg`, `GSet Bool`, `GSet Nat`), because the
    point is to *cite* the theorems those files proved, not to re-prove them at
    scale. A refutation only has to be a refutation; the positive results of
    §§1–7 and §9 carry no carrier assumption at all.
  * ⟨TERMINAL⟩ **`Discharge` has three constructors and is not a classification
    theorem.** It records what a repair bought (global freedom / a seam /
    nothing); it does not prove that no better discharge exists.

Lineage: `Exits.lean` (the enumeration this types) · `Segmented`/`Seams`/`Cost`
(the seam and its price) · `Era`/`GatedEra` (arbitration, and the antitonicity it
spends) · `MVRegister` (the fork) · `JoinHom` (evidence versus summaries) ·
`Ancestral.clash_dichotomy` (which exits are live at all — and ⚠ read
`CODEXHELP.md` §0.1 erratum 2 before citing it: *accumulation* is where admission
control IS the answer, and the dichotomy licenses only "an LCA will not repair
it").
-/
import Uwueave.Seams
import Uwueave.GatedEra
import Uwueave.MVRegister
import Uwueave.JoinHom
import Uwueave.Cost

namespace Uwueave.Repair

open Uwueave Uwueave.Catalog Uwueave.Segmented

/-! ## §1. Premises — trust, enumerated so it can be charged

A premise is something a promise *assumes* rather than proves. Every constructor
below is a premise some theorem in this tree actually runs on; none is invented
for symmetry. The reason this type exists is `Seams.pinned_everywhere_iconfluent`
(§3.7): an invariant made **globally I-confluent** by assuming every replica
already knows every epoch's arbitration verdict. That repair costs zero
crossings. Without a charged premise it also costs zero *everything* — which is
exactly the false zero codex named. -/

/-- The trust assumptions this tree's repairs actually lean on. -/
inductive Premise where
  /-- Some trusted peer unilaterally announces epoch cuts, and replicas take
  them. ERA's mechanism (`Era.lean`; `Seams.lean` correction 3: nobody
  coordinates, the boundary is announced). -/
  | trustedAnnouncer
  /-- Every replica already knows the arbitration verdict for every epoch,
  including epochs it has never entered. This is the premise that makes
  `Seams.pinned_everywhere_iconfluent` free — and it is exactly the global
  knowledge whose absence is the duelling-admins problem. -/
  | verdictKnownEverywhere
  /-- The `actor` field of an op names who really issued it. `GatedEra.lean` is
  explicit that `actor` is a bare `Nat` anyone may write; authenticity is a
  premise there, not a theorem. -/
  | actorAuthentic
  /-- Replicas retain and replay source evidence rather than shipping computed
  summaries — `JoinHom`'s architecture (i). Free as a *theorem*
  (`evidence_architecture_is_free`), not free as a deployment. -/
  | evidenceRetained
  /-- Replicas hold the seam value `σ` fixed between explicit coordination
  events. `SegmentedIConfluent` is a theorem about same-fiber merges; that the
  deployment actually keeps replicas in one fiber is an assumption about the
  deployment. -/
  | seamHeldFixed
  deriving DecidableEq, Repr

/-! ## §2. Price — a record, because the currencies do not convert

Eight fields. Seven are justified by the named theorems in §3; the eighth,
`restrictsReachability`, is the currency a quota partition spends and is
witnessed precisely by `Repair.RestrictsReachability` at the typed escrow in
`RepairMenu`. There is deliberately **no** `meetings` field,
because `Cost.lean` counts seam crossings and says in its own header that it
models no attendance, coalescing, barriers or elapsed time (`CODEXHELP.md` §0.1
erratum 3 is us getting that wrong in print). `seamCrossings` is the honest name
for the only quantity with a floor theorem. -/

/-- **The price of a repair, in eight currencies that do not convert.**

There is no `total : Price → Nat`, and that absence is the point: any collapse to
a scalar re-creates the defect this file was written to fix
(`crossings_cannot_see_the_difference`). -/
structure Price where
  /-- Coordination events forced by leaving a seam fiber. Justified by
  `Cost.coordination_forced` (a floor holding for *every* seam in every
  universe) and instantiated tightly by `Cost.budget_cost_is_three`. This is
  the only field with a lower-bound theorem. -/
  seamCrossings : Nat
  /-- Exogenous arbitration announcements the repair consumes. Justified by
  `GatedEra.ge_duel_arbiter_flips`: the same five events with a different cut
  placement produce a different survivor, so the cut is a real *input* supplied
  by a trusted party, not a derived fact. -/
  arbiterCuts : Nat
  /-- How far already-permitted effect may be revoked by a later announcement.
  Justified by `GatedEra.ge_not_antitone` (an arriving event flips a verdict)
  and bounded — that the window is not "everything" — by
  `Era.final_view_immune` (a finalised prefix is immune to every pending
  event). ⟨UNDONE U-0125⟩ the *number* is declared, not derived. -/
  rollbackWindow : Nat
  /-- Resolution writes left for the application or the user to issue.
  Justified by `MVRegister.resolution_is_a_write`: a surfaced conflict is
  cleared only by a new write at a dominating clock — no merge clears it, so
  the write is exogenous work somebody must do. -/
  resolutionWrites : Nat
  /-- The deployment must retain and replay source evidence instead of shipping
  a computed summary. Justified by `JoinHom.card_not_incrementallyMergeable`
  and its sharp form `JoinHom.no_count_merge_without_provenance`: for a count,
  **no** binary combiner on the two results is exact, so evidence is forced. -/
  retainsEvidence : Bool
  /-- The downstream read becomes plural: more than one answer can be in view at
  once. Justified by `MVRegister.conflict_surfaces` (both concurrent writes
  surface after merge) and its ∀-general form
  `MVRegister.conflict_surfaces_general`. -/
  pluralRead : Bool
  /-- The deployment restricts which source-legal states remain admissible or
  reachable after the repair. This is not a seam crossing, meeting, or trust
  premise: escrow spends locally allocated rights by ruling out states that
  the unpartitioned promise allowed. `Repair.RestrictsReachability` gives the
  semantic witness shape; `RepairMenu.balanceEscrow_price_and_delta`
  exhibits it for the first typed escrow. -/
  restrictsReachability : Bool
  /-- Premises the repaired promise leans on that the original did not.
  Justified by `Seams.pinned_everywhere_iconfluent`: an invariant that is
  *globally free* precisely because it assumes global knowledge. Without this
  field that repair prices at zero in every other currency and reads as a
  bargain. -/
  assumptions : List Premise
  deriving DecidableEq, Repr

namespace Price

/-- **The only honest zero**: nothing spent in any currency.

⚠ Two things below carry it, and the pair is worth reading together: `Repair.id`,
which repairs nothing, and `weaken` (§8.5), which is free in every currency *and*
provably fails to deliver the original promise. So a price record alone is not a
safety property — the cheapest repair in this file is the one that solves a
different problem. What weakening costs is recorded in the **relation**, and the
guard that reads it is §9. -/
def free : Price :=
  { seamCrossings := 0, arbiterCuts := 0, rollbackWindow := 0,
    resolutionWrites := 0, retainsEvidence := false, pluralRead := false,
    restrictsReachability := false, assumptions := [] }

/-- Chained repairs pay both bills: counts add, flags disjoin, premises
accumulate. ⟨UNDONE U-0126⟩ this is a *declared* accumulation and is not claimed
minimal — see the module header. -/
def add (p q : Price) : Price :=
  { seamCrossings := p.seamCrossings + q.seamCrossings,
    arbiterCuts := p.arbiterCuts + q.arbiterCuts,
    rollbackWindow := p.rollbackWindow + q.rollbackWindow,
    resolutionWrites := p.resolutionWrites + q.resolutionWrites,
    retainsEvidence := p.retainsEvidence || q.retainsEvidence,
    pluralRead := p.pluralRead || q.pluralRead,
    restrictsReachability := p.restrictsReachability || q.restrictsReachability,
    assumptions := p.assumptions ++ q.assumptions }

@[simp] theorem free_add (p : Price) : add free p = p := by
  cases p; simp [add, free]

@[simp] theorem add_free (p : Price) : add p free = p := by
  cases p; simp [add, free]

/-- Prices associate, so a chain has one price however it is bracketed. -/
theorem add_assoc (p q r : Price) : add (add p q) r = add p (add q r) := by
  cases p; cases q; cases r
  simp [add, Nat.add_assoc, Bool.or_assoc, List.append_assoc]

end Price

/-! ## §3. The price currencies and their theorem witnesses

Each `example` below is a machine-checked citation: the price field named in its
docstring is justified by exactly this term. A number without a theorem is a lie
in this tree, so the citations are terms, not prose. -/

/-- §3.1 `seamCrossings`, the floor — for **every** segment type in every
universe and every valid seam onto it, three re-divisions of a shared budget
cost at least three crossings. This is `Cost.coordination_forced` at the
budget workload. -/
example : ∀ {Seg : Type} [DecidableEq Seg] (σ : QuotaState → Seg),
    SegmentedIConfluent σ (BudgetInv 10) →
    3 ≤ Cost.crossings σ (Cost.reallocStep 10) Cost.budgetStart Cost.budgetW :=
  Cost.budget_cost_is_three.1

/-- §3.1 `seamCrossings`, the achievement — the allocation-share seam pays
exactly three. Floor and achievement meet, so `seamPrice.seamCrossings = 3`
below is a measured number, not an estimate. -/
example : Cost.crossings (fun s : QuotaState => s.1 true) (Cost.reallocStep 10)
    Cost.budgetStart Cost.budgetW = 3 :=
  Cost.budget_cost_is_three.{0}.2

/-- §3.2 `arbiterCuts` — the arbiter's cut placement carries the verdict. Same
five events, one more announcement record, and the surviving op flips. So a cut
is an input somebody supplies and everybody trusts, and counting cuts is
counting exercises of that trust. -/
example :
    GatedEra.geGatedOps GatedEra.moveReq Era.setupCuts Era.duelLog
        GatedEra.duelOps GatedEra.opAlice
    ∧ ¬ GatedEra.geGatedOps GatedEra.moveReq Era.setupCuts Era.duelLog
        GatedEra.duelOps GatedEra.opBob
    ∧ ¬ GatedEra.geGatedOps GatedEra.moveReq Era.laterCuts Era.duelLog
        GatedEra.duelOps GatedEra.opAlice
    ∧ GatedEra.geGatedOps GatedEra.moveReq Era.laterCuts Era.duelLog
        GatedEra.duelOps GatedEra.opBob :=
  GatedEra.ge_duel_arbiter_flips

/-- §3.3 `rollbackWindow`, that it is real — event growth turns a denial into a
permission, so a system that arbitrates is not antitone and a permitted op is
not a fact about its own future. -/
example : ¬ GatedEra.AntitoneInEvents := GatedEra.ge_not_antitone

/-- §3.3 `rollbackWindow`, that it is bounded — delivering any batch of still
pending events changes **nothing** about the finalised view. The exposure is the
pending suffix and no more; that is what makes a window a number rather than
"everything". -/
example : ∀ (cuts : List Era.Cut) (log fresh : List Era.Event),
    (∀ e ∈ fresh, Era.finalized cuts e = false) →
    Era.resolveFinal cuts (log ++ fresh) = Era.resolveFinal cuts log :=
  Era.final_view_immune

/-- §3.4 `resolutionWrites` — a surfaced conflict is cleared by an ordinary
write at a dominating clock, and by nothing else. The merge has no resolution
case; somebody must issue the write. -/
example : ¬ MVRegister.InView MVRegister.sABR MVRegister.wA
    ∧ MVRegister.InView MVRegister.sABR MVRegister.wR :=
  MVRegister.resolution_is_a_write

/-- §3.5 `retainsEvidence` — **no** binary combiner on the two replicated counts
is exact, so a deployment that ships the number instead of the set answers
wrong. The evidence price is forced, not chosen. -/
example : ¬ IncrementallyMergeable JoinHom.card :=
  JoinHom.card_not_incrementallyMergeable

/-- §3.5 `retainsEvidence`, the other half — retaining evidence and recomputing
the view is correct for **every** interpreter, with no hypothesis. The price is
storage and replay, not correctness. -/
example : JoinHom.ReplicatesEvidence JoinHom.card :=
  JoinHom.evidence_architecture_is_free JoinHom.card

/-- §3.6 `pluralRead` — after merging two concurrent writes, both are in view.
The read is genuinely plural; LWW would show exactly one, with no trace of the
other. -/
example : MVRegister.InView MVRegister.sAB MVRegister.wA
    ∧ MVRegister.InView MVRegister.sAB MVRegister.wB :=
  MVRegister.conflict_surfaces

/-- §3.7 `assumptions` — the theorem that forces the field to exist. Pin every
epoch's claims to the arbiter and the invariant is **globally I-confluent**: no
clash, no seam, zero crossings. It is also question-begging, because it presumes
every replica already knows every epoch's verdict. Priced in crossings alone this
repair is free; `Premise.verdictKnownEverywhere` is what it actually costs. -/
example (arb : Nat → Nat) :
    IConfluent (S := Seams.EpochState) (fun s => ∀ e a, s.2 e a = true → a = arb e) :=
  Seams.pinned_everywhere_iconfluent arb

/-! ### §3.8 Five prices, and why a scalar cannot hold them

⚠ **One number in this section is measured; the rest are declared.** `seamPrice`'s
`3` is `Cost.budget_cost_is_three` — a floor holding for every seam in every
universe, met exactly by the allocation-share seam. Nothing comparable exists for
`arbiterCuts`, `rollbackWindow` or `resolutionWrites`: §3 proves those quantities
are *real* (an arbiter's cut decides the survivor, a pending suffix can be rolled
back, a fork closes only by a write) and this tree contains no theorem that
computes their size for a given workload. They are an author's claim about an
author's deployment, checked by `premisesCharged` and by nothing else. Saying
which of four numbers has a floor is the difference between a price and a
guess. -/

/-- The seam repair's price: three crossings, nothing else. The `3` is
`Cost.budget_cost_is_three` (§3.1) — floor **and** achievement, so it is the
workload's coordination frequency, not a bound on it. -/
def seamPrice : Price := { Price.free with seamCrossings := 3 }

/-- Arbitration's price: one trusted announcement, one epoch of rollback
exposure, two charged premises — **and zero crossings**. ⟨UNDONE U-0127⟩ the two `1`s
are declared; §3.2 and §3.3 prove the currencies are real, not that these are
their amounts. -/
def arbitrationPrice : Price :=
  { Price.free with
    arbiterCuts := 1, rollbackWindow := 1,
    assumptions := [Premise.trustedAnnouncer, Premise.verdictKnownEverywhere] }

/-- The fork's price: the read goes plural, and somebody must eventually write a
resolution — **and zero crossings**. ⟨UNDONE U-0128⟩ the `1` is declared; §3.4 proves
only that no merge issues the write. -/
def forkPrice : Price :=
  { Price.free with resolutionWrites := 1, pluralRead := true }

/-- Retaining evidence: storage and replay — **and zero crossings**. This is the
one price with no number to declare: §3.5 makes it a forced Bool. -/
def evidencePrice : Price := { Price.free with retainsEvidence := true }

/-- Restricting admission/reachability: no crossings or meetings are invented;
the price records that some source-legal state is no longer available. The
typed escrow in `RepairMenu` supplies the semantic witness. -/
def restrictionPrice : Price :=
  { Price.free with restrictsReachability := true }

/-- ⚠ **codex's objection (a), as a theorem.** Read through the crossing count
alone — the single `Nat` our first draft carried — arbitration, forking,
retaining evidence, and restricting reachability are **indistinguishable and
free**. They are none of those things: the prices differ in kind, and each is
distinct from the seam's. A scalar price is not a compression of this record;
it deletes seven of its eight fields. -/
theorem crossings_cannot_see_the_difference :
    arbitrationPrice.seamCrossings = 0
    ∧ forkPrice.seamCrossings = 0
    ∧ evidencePrice.seamCrossings = 0
    ∧ restrictionPrice.seamCrossings = 0
    ∧ restrictionPrice.restrictsReachability = true
    ∧ restrictionPrice ≠ Price.free
    ∧ arbitrationPrice ≠ forkPrice
    ∧ forkPrice ≠ evidencePrice
    ∧ arbitrationPrice ≠ evidencePrice
    ∧ restrictionPrice ≠ arbitrationPrice
    ∧ restrictionPrice ≠ forkPrice
    ∧ restrictionPrice ≠ evidencePrice
    ∧ seamPrice ≠ arbitrationPrice
    ∧ seamPrice ≠ forkPrice
    ∧ seamPrice ≠ evidencePrice
    ∧ seamPrice ≠ restrictionPrice := by decide

/-! ## §4. `PromiseRelation` — what the repair did to the promise

Five independent axes, each a Bool meaning "this survived". They compose by `&&`,
which is exactly right: each axis is preserved by a chain iff it is preserved by
every link, because implications compose and premises accumulate.

The five names codex asked for are inhabitants, not constructors — and that turns
out to matter: **two of the four repairs need several names at once**
(`arbitration_needs_three_names`, `fork_is_changed_observation_and_weakened`). A
five-constructor `inductive` could not have said that, and would have forced each
repair into whichever single name its author found most flattering. -/

/-- **What a repair did to the promise**, on five axes. Each field is certified
by the correspondingly-named obligation in `Repair`; a `false` field claims
nothing and proves nothing, which is why the guard in §9 is stated as a
refutation and not as bookkeeping. -/
structure PromiseRelation where
  /-- The repaired promise still delivers the original guarantee:
  `Q.inv (transform s) → P.inv s`. This is the axis a budget-meeting solver
  breaks when it solves a different problem. -/
  entailsOriginal : Bool
  /-- Everything the original allowed is still allowed:
  `P.inv s → Q.inv (transform s)`. Escrow and refinement spend this axis —
  states that were legal stop being reachable. -/
  admitsOriginal : Bool
  /-- The read is still singular: at most one demand is admitted at a legal
  state. Forking spends this axis, and the downstream contract changes with
  it. ⟨UNDONE U-0129⟩ this is the provable fragment of "the observation changed"; see
  the module header. -/
  singularObservation : Bool
  /-- Growth of the state never enlarges what is admitted —
  `Gated.gated_antitone`'s shape. Arbitration spends this axis, necessarily:
  `GatedEra.antitone_forbids_enabling` says a rule that shrinks under growth can
  never let an arriving event turn a denial into a permission, so no promotion,
  no re-grant, no repair. -/
  shrinkageKept : Bool
  /-- The repaired promise assumes no premise the original did not. -/
  trustPreserved : Bool
  deriving DecidableEq, Repr

namespace PromiseRelation

/-- Composition: an axis survives a chain iff it survives every link. -/
def comp (a b : PromiseRelation) : PromiseRelation :=
  { entailsOriginal := a.entailsOriginal && b.entailsOriginal,
    admitsOriginal := a.admitsOriginal && b.admitsOriginal,
    singularObservation := a.singularObservation && b.singularObservation,
    shrinkageKept := a.shrinkageKept && b.shrinkageKept,
    trustPreserved := a.trustPreserved && b.trustPreserved }

/-- **Equivalent**: the promise is untouched on every axis. The two *deployment*
repairs (seam, retain-evidence) sit here — they change the price and the
discharge and nothing else. -/
def equivalent : PromiseRelation := ⟨true, true, true, true, true⟩

/-- **Strengthened**: the repaired promise still entails the original and
promises more, so some previously-legal state is now refused. -/
def strengthened : PromiseRelation := ⟨true, false, true, true, true⟩

/-- **Weakened**: the repaired promise no longer entails the original. This is
the relation §9 refuses to let anyone present as satisfying the original. -/
def weakened : PromiseRelation := ⟨false, true, true, true, true⟩

/-- **Changed observation**: the read stops being singular; downstream must
handle plurality. -/
def changedObservation : PromiseRelation := ⟨true, true, false, true, true⟩

/-- **Changed trust**: the repaired promise leans on a premise the original did
not. -/
def changedTrust : PromiseRelation := ⟨true, true, true, true, false⟩

/-- **Changed monotonicity** — the axis codex's five names do not contain, and
the one arbitration spends alongside trust. -/
def changedMonotonicity : PromiseRelation := ⟨true, true, true, false, true⟩

/-- Neither direction survives: the two promises are simply different. -/
def incomparable : PromiseRelation := ⟨false, false, true, true, true⟩

@[simp] theorem equivalent_comp (a : PromiseRelation) : comp equivalent a = a := by
  cases a; simp [comp, equivalent]

@[simp] theorem comp_equivalent (a : PromiseRelation) : comp a equivalent = a := by
  cases a; simp [comp, equivalent]

/-- Relations associate, so a chain has one relation however it is bracketed. -/
theorem comp_assoc (a b c : PromiseRelation) :
    comp (comp a b) c = comp a (comp b c) := by
  cases a; cases b; cases c; simp [comp, Bool.and_assoc]

/-- Order of composition does not change what survived. -/
theorem comp_comm (a b : PromiseRelation) : comp a b = comp b a := by
  cases a; cases b; simp [comp, Bool.and_comm]

/-- **The composition table codex asked for.** `equivalent` is the identity;
weakening is absorbing on its own axis; and strengthening followed by weakening
is not "back where we started" but `incomparable` — neither promise entails the
other, which is precisely the state a solver reaches by strengthening in one
place and weakening in another to fit a budget. -/
theorem comp_table :
    comp equivalent weakened = weakened
    ∧ comp weakened equivalent = weakened
    ∧ comp weakened weakened = weakened
    ∧ comp strengthened weakened = incomparable
    ∧ comp equivalent equivalent = equivalent
    ∧ comp changedObservation changedTrust
        = ⟨true, true, false, true, false⟩ := by decide

end PromiseRelation

/-! ## §5. `Promise` — an invariant, plus exactly the context the axes read

Six fields. `State`/`mergeState`/`inv` are the judgement this library already
makes; `Demand`/`admits` are the observation context that `singularObservation`
and `shrinkageKept` read; `trust` is what `trustPreserved` and `premisesCharged`
read. Nothing else is here, and nothing here is unread. -/

/-- **A promise**: what a replicated specification guarantees, and to whom.

`admits s d` reads "at state `s`, demand `d` is in view / permitted / answered".
A singular register is a promise admitting at most one demand at a legal state; a
permission feed is a promise whose demands are ops. -/
structure Promise : Type 1 where
  /-- The replicated state. -/
  State : Type
  /-- Its merge. -/
  mergeState : MergeState State
  /-- What downstream asks about — the observation's index. -/
  Demand : Type
  /-- What the promise answers: which demands the state admits. -/
  admits : State → Demand → Prop
  /-- What the promise guarantees of the state. -/
  inv : Invariant State
  /-- What the promise assumes rather than proves. -/
  trust : List Premise

-- Low priority: this instance is stuck on `?P.State` for any concrete carrier, so
-- it can only ever fail there; tried last, it costs nothing downstream.
attribute [instance 100] Promise.mergeState

/-- The judgement this library computes, as a property of a promise. -/
def Promise.Free (P : Promise) : Prop := IConfluent P.inv

/-- **The observation is singular**: at a legal state, at most one demand is
admitted. This is the "the read returns one answer" contract that forking
spends. -/
def Promise.Singular (P : Promise) : Prop :=
  ∀ s, P.inv s → ∀ d d', P.admits s d → P.admits s d' → d = d'

/-- **The observation shrinks under growth** — `Gated.gated_antitone`'s shape at
the level of a promise: learning more never admits more. -/
def Promise.Shrinking (P : Promise) : Prop :=
  ∀ x y : P.State, x ⊑ y → ∀ d, P.admits y d → P.admits x d

/-- **Shrinkage forbids repair** — `GatedEra.antitone_forbids_enabling` in
promise vocabulary, and the reason `shrinkageKept` is an axis rather than a
footnote. If a promise's observation shrinks under state growth, a demand denied
at a state is denied at every larger state: no arriving information can ever turn
a denial into a permission, so no promotion, no re-grant, and no repair delivered
by the substrate itself. A system that wants arbitration to *fix* something must
give this up. -/
theorem shrinking_forbids_enabling (P : Promise) (h : P.Shrinking)
    {x y : P.State} (hxy : x ⊑ y) {d : P.Demand} (hno : ¬ P.admits x d) :
    ¬ P.admits y d :=
  fun hy => hno (h x y hxy d hy)

/-- The theorem the one above transposes, cited as a term: for ANY permission
rule antitone in event growth, an op denied on a sub-log is denied on every
extension. -/
example {P : List Era.Event → GatedEra.EOp → Prop}
    (hanti : ∀ l l' : List Era.Event, (∀ e ∈ l, e ∈ l') → ∀ o, P l' o → P l o)
    {l l' : List Era.Event} (hsub : ∀ e ∈ l, e ∈ l') {o : GatedEra.EOp}
    (hno : ¬ P l o) : ¬ P l' o :=
  GatedEra.antitone_forbids_enabling hanti hsub hno

/-! ## §6. `Discharge` — what the repair bought

A repair that changed nothing about the promise (seam, retain-evidence) is not
vacuous: its content is the price it declares and the *status* it buys. This is
that status, and it carries the proof. -/

/-- **What a repair bought.** The three answers this library computes, as
evidence rather than a label. -/
inductive Discharge (Q : Promise) : Type 1 where
  /-- Globally coordination-free, with the proof. -/
  | free (h : IConfluent Q.inv)
  /-- Free within the fibers of a seam, with the seam and the proof — merges of
  same-fiber legal states are legal *and stay in the fiber*. -/
  | seam (Seg : Type) (σ : Q.State → Seg) (h : SegmentedIConfluent σ Q.inv)
  /-- The repair bought something that is not freedom — a live op feed, a
  visible fork, a cheaper deployment — and the promise still escalates. Naming
  this is what stops a repair from implying a verdict it did not prove. -/
  | escalates

/-! ## §7. `Repair P Q` — the transformation, its soundness, its price, its relation

Both promises are in the type. Each axis of the relation has exactly one
obligation, **guarded by its own flag**, so a `true` you have not proved is not
constructible; and `premisesCharged` is unguarded, so a premise you introduced
and did not charge is not constructible either. -/

/-- **A repair**: a proof-carrying transformation from promise `P` to promise
`Q`. -/
structure Repair (P Q : Promise) : Type 1 where
  /-- How a state of the original promise becomes a state of the repaired one. -/
  transform : P.State → Q.State
  /-- What the repair did to the promise, on five axes. -/
  relation : PromiseRelation
  /-- What it costs, in eight currencies. -/
  price : Price
  /-- What it bought. -/
  discharge : Discharge Q
  /-- If you claim the original guarantee survives, prove it. -/
  entails : relation.entailsOriginal = true → ∀ s, Q.inv (transform s) → P.inv s
  /-- If you claim nothing legal was forbidden, prove it. -/
  admitsAll : relation.admitsOriginal = true → ∀ s, P.inv s → Q.inv (transform s)
  /-- If you claim the read is still singular, prove it. -/
  singular : relation.singularObservation = true → P.Singular → Q.Singular
  /-- If you claim growth still only shrinks the feed, prove it. -/
  shrinking : relation.shrinkageKept = true → P.Shrinking → Q.Shrinking
  /-- If you claim no new trust, prove it. -/
  trustKept : relation.trustPreserved = true → ∀ p, p ∈ Q.trust → p ∈ P.trust
  /-- **Unguarded, and the answer to the manufactured zero**: every premise the
  repaired promise leans on that the original did not must appear in the price.
  There is no flag to set `false` to escape this one. -/
  premisesCharged : ∀ p, p ∈ Q.trust → ¬ (p ∈ P.trust) → p ∈ price.assumptions

namespace Repair

variable {P Q R : Promise}

/-- **The claim a repair may be *presented* as making**: the repaired system
still satisfies what was originally promised. `entails` proves this when the flag
is set; §9 exhibits a repair where the flag is clear and the claim is FALSE. -/
def DeliversOriginal (r : Repair P Q) : Prop :=
  ∀ s, Q.inv (r.transform s) → P.inv s

/-- **The precise reachability/admission delta.** Some state admitted by the
source invariant is rejected after transformation by the target invariant.
This proposition is stronger than clearing `relation.admitsOriginal`: a clear
flag makes no claim, while this carries the actual counterexample. -/
def RestrictsReachability (r : Repair P Q) : Prop :=
  ∃ s, P.inv s ∧ ¬ Q.inv (r.transform s)

/-- The flag is sound: a repair claiming `entailsOriginal` delivers the
original. -/
theorem delivers_of_flag (r : Repair P Q) (h : r.relation.entailsOriginal = true) :
    r.DeliversOriginal := r.entails h

/-- ⚠ **The manufactured zero is not constructible.** A repair that introduces a
premise cannot price at `Price.free` — not "should not", not "by convention": the
charge is a *field*, so the term does not exist. This is codex's objection (a)
answered structurally rather than by discipline, and it is the one obligation in
`Repair` with no flag to clear.

Note what it does NOT say: nothing here forces the *other* six fields to be
right. A repair may still under-declare its rollback window or its resolution
writes, because this tree has no theorem computing those (§3.8). What it forbids
is the specific failure codex named — a repair that leans on a new trusted party
and reports itself as free. -/
theorem introduced_premise_forces_a_charge (r : Repair P Q)
    {p : Premise} (hq : p ∈ Q.trust) (hp : ¬ (p ∈ P.trust)) :
    r.price ≠ Price.free := by
  intro hfree
  have hm := r.premisesCharged p hq hp
  rw [hfree] at hm
  simp [Price.free] at hm

/-- The identity repair: it changes nothing, costs nothing, and buys nothing —
which is the honest relationship between "free" and "repair". (`weaken` in §8.5
is the other `Price.free` inhabitant, and it is free for a much worse reason.) -/
def id (P : Promise) : Repair P P where
  transform := fun s => s
  relation := PromiseRelation.equivalent
  price := Price.free
  discharge := .escalates
  entails := fun _ _ h => h
  admitsAll := fun _ _ h => h
  singular := fun _ h => h
  shrinking := fun _ h => h
  trustKept := fun _ _ h => h
  premisesCharged := fun _ hq hp => absurd hq hp

/-- **Repairs compose** — the theorem that makes this more than a record. The
transform composes, the relation composes axis-wise, the price accumulates, and
**every obligation is re-discharged**, not asserted: the composite's `entails`
runs the two links' `entails` in sequence, and its `premisesCharged` case-splits
on whether the premise entered at the first link or the second. The discharge is
the final link's, because that is the promise the chain ends at. -/
def comp (r : Repair P Q) (t : Repair Q R) : Repair P R where
  transform := fun s => t.transform (r.transform s)
  relation := r.relation.comp t.relation
  price := r.price.add t.price
  discharge := t.discharge
  entails := fun h s hR =>
    r.entails ((Bool.and_eq_true _ _).mp h).1 s
      (t.entails ((Bool.and_eq_true _ _).mp h).2 (r.transform s) hR)
  admitsAll := fun h s hP =>
    t.admitsAll ((Bool.and_eq_true _ _).mp h).2 (r.transform s)
      (r.admitsAll ((Bool.and_eq_true _ _).mp h).1 s hP)
  singular := fun h hP =>
    t.singular ((Bool.and_eq_true _ _).mp h).2
      (r.singular ((Bool.and_eq_true _ _).mp h).1 hP)
  shrinking := fun h hP =>
    t.shrinking ((Bool.and_eq_true _ _).mp h).2
      (r.shrinking ((Bool.and_eq_true _ _).mp h).1 hP)
  trustKept := fun h p hp =>
    r.trustKept ((Bool.and_eq_true _ _).mp h).1 p
      (t.trustKept ((Bool.and_eq_true _ _).mp h).2 p hp)
  premisesCharged := by
    intro p hpR hpP
    show p ∈ r.price.assumptions ++ t.price.assumptions
    by_cases hq : p ∈ Q.trust
    · exact List.mem_append_left _ (r.premisesCharged p hq hpP)
    · exact List.mem_append_right _ (t.premisesCharged p hpR hq)

/-- The chain's price is the sum of its links'. -/
@[simp] theorem comp_price (r : Repair P Q) (t : Repair Q R) :
    (r.comp t).price = r.price.add t.price := rfl

/-- The chain's relation is the axis-wise conjunction of its links'. -/
@[simp] theorem comp_relation (r : Repair P Q) (t : Repair Q R) :
    (r.comp t).relation = r.relation.comp t.relation := rfl

/-- Delivery composes, at the level of the property rather than the flag. -/
theorem comp_delivers (r : Repair P Q) (t : Repair Q R)
    (hr : r.DeliversOriginal) (ht : t.DeliversOriginal) :
    (r.comp t).DeliversOriginal :=
  fun s h => hr s (ht (r.transform s) h)

/-- **The guard, forward half**: one weakening link clears the whole chain's
flag. There is no bracketing, no reordering and no later strengthening that
restores it — `&&` is absorbing at `false`. -/
theorem comp_entails_false_left (r : Repair P Q) (t : Repair Q R)
    (h : r.relation.entailsOriginal = false) :
    (r.comp t).relation.entailsOriginal = false := by
  show (r.relation.entailsOriginal && t.relation.entailsOriginal) = false
  rw [h]; rfl

/-- The guard, forward half, other side. -/
theorem comp_entails_false_right (r : Repair P Q) (t : Repair Q R)
    (h : t.relation.entailsOriginal = false) :
    (r.comp t).relation.entailsOriginal = false := by
  show (r.relation.entailsOriginal && t.relation.entailsOriginal) = false
  rw [h]; exact Bool.and_false _

end Repair

/-! ## §8. The repairs, typed

Four repairs, each on a carrier this tree already reasons about, each citing the
theorems that make its price honest. The 2×2 the typing exposes: **seam** and
**retain-evidence** are `equivalent` — identities on the promise, changes to the
deployment — while **arbitration** and **fork** change the promise, and their
relations say exactly how. -/

/-! ### §8.1 The seam repair — equivalent promise, priced in crossings

The budgeted-quota promise: two devices spending against a shared budget of 10.
Globally it escalates (`Segmented.budget_not_iconfluent`: two legal allocations
merge over budget). The seam repair does **nothing** to the promise — same
carrier, same invariant, same observation, same trust — and buys
`SegmentedIConfluent` over the allocation. Its whole price is crossings, and the
number is `Cost.budget_cost_is_three`: floor three, achieved three. -/

/-- The budgeted promise: a device is admitted to spend while its spend is under
its quota. -/
def budgetPromise : Promise where
  State := QuotaState
  mergeState := inferInstance
  Demand := Bool
  admits := fun s b => s.2 b < s.1 b
  inv := BudgetInv 10
  trust := []

/-- ⚠ The budgeted promise escalates: two legal allocations (10+0 and 0+10 against
a budget of 10) merge to the pointwise-max 10+10, which busts the budget.
Re-allocation cannot be free. -/
theorem budget_escalates : ¬ budgetPromise.Free := by
  intro h; exact budget_not_iconfluent h

/-- **The seam repair.** Identity on the promise; `SegmentedIConfluent` over the
allocation as its discharge; three crossings as its price. Spends are free, only
re-allocation coordinates. -/
def seamRepair : Repair budgetPromise budgetPromise where
  transform := fun s => s
  relation := PromiseRelation.equivalent
  price := seamPrice
  discharge := .seam (Bool → Nat) Prod.fst (budget_segmented 10)
  entails := fun _ _ h => h
  admitsAll := fun _ _ h => h
  singular := fun _ h => h
  shrinking := fun _ h => h
  trustKept := fun _ _ h => h
  premisesCharged := fun _ hq hp => absurd hq hp

/-- The seam repair keeps the promise exactly, and its `3` is a theorem. -/
theorem seamRepair_relation : seamRepair.relation = PromiseRelation.equivalent := rfl

/-- The seam repair delivers the original promise — the flag is set and the
obligation is discharged. -/
theorem seamRepair_delivers : seamRepair.DeliversOriginal :=
  seamRepair.delivers_of_flag rfl

/-! ### §8.2 The arbitration repair — changed trust AND changed monotonicity

⚠ **This is the one people get wrong.** Arbitration is routinely priced at "0
meetings" because no replica waits for another: the boundary is announced
unilaterally and replicas never block (`Seams.lean` correction 3). Zero crossings
is *true*. It is also seven-eighths of the price missing.

What it actually spends: a trusted announcer and the assumption that the verdict
is known (`Premise.trustedAnnouncer`, `Premise.verdictKnownEverywhere` — charged
in `arbitrationPrice.assumptions`), a rollback window over the pending suffix,
and — the axis with no name in the usual five — **antitonicity**.
`GatedEra.antitone_forbids_enabling` is what makes that last one structural
rather than incidental: a rule that shrinks under growth can never let an
arriving event turn a denial into a permission, so *any* system that can promote
has given up shrinkage. Arbitration is exactly such a system. -/

/-- The unpinned epoch promise: at most one admin claimed in the current epoch,
with no arbitration. `Seams.sole_unpinned_not_segmented` proves this is not even
*segmented* over the epoch — the epoch is a batching structure, not an
arbitration policy. -/
def unpinnedEpochPromise : Promise where
  State := Seams.EpochState
  mergeState := inferInstance
  Demand := Nat
  admits := fun s a => s.2 s.1 a = true
  inv := fun s => ∀ m n, s.2 s.1 m = true → s.2 s.1 n = true → m = n
  trust := []

/-- The arbitrated epoch promise: every admin claim in the current epoch names
the arbitrated survivor. Two premises, both charged. -/
def arbitratedEpochPromise : Promise where
  State := Seams.EpochState
  mergeState := inferInstance
  Demand := Nat
  admits := fun s a => s.2 s.1 a = true
  inv := Seams.EpochSole Seams.demoArb
  trust := [Premise.trustedAnnouncer, Premise.verdictKnownEverywhere]

/-- ⚠ The unpinned promise is not repaired by the epoch alone: two replicas in
the SAME epoch each mint their own admin and merge without ever crossing the
seam. The seam exit is *unavailable* here, which is why arbitration is the
repair on offer. -/
theorem unpinned_has_no_epoch_seam :
    ¬ SegmentedIConfluent (S := Seams.EpochState) Prod.fst unpinnedEpochPromise.inv :=
  Seams.sole_unpinned_not_segmented

/-- ⚠ **The arbitrated promise is not shrinking** — an arriving announcement
turns a denial into a permission. A replica sitting at epoch 1 with no claims
admits nobody; the strictly larger state that has crossed into epoch 2 carrying
the arbitrated claim admits member 2. Growth of the state ENLARGED the feed. This
is `GatedEra.ge_not_antitone` on this carrier, and it is why
`arbitrate.relation.shrinkageKept` is `false` rather than unproved. -/
theorem arbitrated_not_shrinking : ¬ arbitratedEpochPromise.Shrinking := by
  intro hshr
  have h : ∀ x y : Seams.EpochState, x ⊑ y →
      ∀ d : Nat, y.2 y.1 d = true → x.2 x.1 d = true := hshr
  have hxy : ((1, fun _ _ => false) : Seams.EpochState)
      ⊑ ((2, fun e a => e == 2 && a == 2) : Seams.EpochState) := rfl
  exact absurd (h _ _ hxy 2 (by decide)) (by decide)

/-- **The arbitration repair.** Trust and shrinkage are spent; the original
guarantee survives (`Seams.epochSole_at_most_one`: a pinned state really does
have at most one admin in its current epoch) and so does singularity, which is
the same theorem. Some previously-legal state is now refused — a replica whose
claim disagrees with the arbiter — so `admitsOriginal` is clear too. -/
def arbitrate : Repair unpinnedEpochPromise arbitratedEpochPromise where
  transform := fun s => s
  relation :=
    PromiseRelation.strengthened.comp
      (PromiseRelation.changedTrust.comp PromiseRelation.changedMonotonicity)
  price := arbitrationPrice
  discharge := .seam Nat Prod.fst (Seams.epoch_segmented Seams.demoArb)
  entails := fun _ s h m n hm hn => Seams.epochSole_at_most_one h m n hm hn
  admitsAll := fun h => absurd h (by decide)
  singular := fun _ _ s h d d' hd hd' => Seams.epochSole_at_most_one h d d' hd hd'
  shrinking := fun h => absurd h (by decide)
  trustKept := fun h => absurd h (by decide)
  premisesCharged := fun _ hq _ => hq

/-- ⚠ **Arbitration needs THREE of codex's five names, not one.** It is
`strengthened` (a replica whose claim disagrees with the arbiter was legal and is
not any more) composed with `changedTrust` composed with `changedMonotonicity` —
and it equals none of the six named relations on its own. A five-constructor
enum would have had to pick one, and the one an author picks is the flattering
one; "arbitrate: 0 meetings" is that pick, printed. -/
theorem arbitration_needs_three_names :
    arbitrate.relation ≠ PromiseRelation.equivalent
    ∧ arbitrate.relation ≠ PromiseRelation.strengthened
    ∧ arbitrate.relation ≠ PromiseRelation.weakened
    ∧ arbitrate.relation ≠ PromiseRelation.changedObservation
    ∧ arbitrate.relation ≠ PromiseRelation.changedTrust
    ∧ arbitrate.relation ≠ PromiseRelation.changedMonotonicity
    ∧ arbitrate.relation
        = PromiseRelation.strengthened.comp
            (PromiseRelation.changedTrust.comp PromiseRelation.changedMonotonicity) := by
  decide

/-- Arbitration does still deliver the original promise — the flag is set and
`Seams.epochSole_at_most_one` discharges it. What it spends is trust and
shrinkage, not the guarantee. Saying that precisely is the whole point of having
five axes instead of one word. -/
theorem arbitrate_delivers : arbitrate.DeliversOriginal :=
  arbitrate.delivers_of_flag rfl

/-- ⚠ **"Arbitration costs nothing" is not a report this type can print.**
Quantified over **every** repair onto the arbitrated promise, whoever writes it
and however they price it: the price is not `Price.free`, and its `assumptions`
are not empty. `Premise.trustedAnnouncer` is in the target's trust and not in the
source's, so `premisesCharged` demands it appear — and it cannot appear in `[]`.
This is the false zero codex named, refuted for the exit he named it about. -/
theorem no_free_arbitration (r : Repair unpinnedEpochPromise arbitratedEpochPromise) :
    r.price ≠ Price.free ∧ r.price.assumptions ≠ [] := by
  have hq : Premise.trustedAnnouncer ∈ arbitratedEpochPromise.trust := by decide
  have hp : ¬ (Premise.trustedAnnouncer ∈ unpinnedEpochPromise.trust) := by decide
  refine ⟨Repair.introduced_premise_forces_a_charge r hq hp, ?_⟩
  intro hnil
  have hm := r.premisesCharged Premise.trustedAnnouncer hq hp
  rw [hnil] at hm
  simp at hm

/-! ### §8.3 The fork repair — the output contract changes, and downstream must handle it

Keep every write not causally superseded and surface concurrent writes as an
explicit conflict set. The promise "the register reads one value" is not weakened
into a vaguer version of itself — it is **replaced** by a promise of a different
shape, `Claim → NonemptySet Claim`, and every downstream reader must change. That
is what `singularObservation := false` records, and `fork_loses_singularity`
proves it against the real `MVRegister` carrier rather than a stand-in. -/

/-- The singular register promise: at most one write is in view. -/
def singularRegisterPromise : Promise where
  State := MVRegister.MVReg
  mergeState := inferInstance
  Demand := MVRegister.Write
  admits := MVRegister.InView
  inv := fun s => ∀ w w', MVRegister.InView s w → MVRegister.InView s w' → w = w'
  trust := []

/-- The forked register promise: the state is the same grow-only set of tagged
writes; the promise about the view is gone. -/
def forkedRegisterPromise : Promise where
  State := MVRegister.MVReg
  mergeState := inferInstance
  Demand := MVRegister.Write
  admits := MVRegister.InView
  inv := fun _ => True
  trust := []

/-- A one-write state is singular: the only write in view is the one present. -/
theorem single_is_singular (w : MVRegister.Write) :
    singularRegisterPromise.inv (MVRegister.single w) := by
  intro a b ha hb
  have ha' : a = w := by simpa [MVRegister.single] using ha.1
  have hb' : b = w := by simpa [MVRegister.single] using hb.1
  rw [ha', hb']

/-- ⚠ The singular register promise escalates: two replicas each holding one
concurrent write are each singular, and their merge holds both in view. This is
the clash the fork answers. -/
theorem singular_register_escalates : ¬ singularRegisterPromise.Free := by
  intro h
  have hmerge := h (MVRegister.single MVRegister.wA) (MVRegister.single MVRegister.wB)
    (single_is_singular _) (single_is_singular _)
  have hbad : MVRegister.wA = MVRegister.wB :=
    hmerge MVRegister.wA MVRegister.wB
      MVRegister.conflict_surfaces.1 MVRegister.conflict_surfaces.2
  exact absurd hbad (by decide)

/-- ⚠ **The fork loses singularity, against the real carrier.** After merging
Alice's and Bob's replicas both writes are in view, and they are distinct writes.
The read is plural; a downstream that renders one value is rendering a lie. -/
theorem fork_loses_singularity : ¬ forkedRegisterPromise.Singular := by
  intro h
  have hbad : MVRegister.wA = MVRegister.wB :=
    h MVRegister.sAB trivial MVRegister.wA MVRegister.wB
      MVRegister.conflict_surfaces.1 MVRegister.conflict_surfaces.2
  exact absurd hbad (by decide)

/-- **The fork repair.** The observation goes plural and the original guarantee
goes with it; nothing legal is forbidden, no trust is added, and — since the
carrier and the view are unchanged — whatever shrinkage the original had
survives. The promise it lands on is globally free, and `entailsOriginal = false`
is what stops that freedom from being read as a solution to the original
problem. -/
def fork : Repair singularRegisterPromise forkedRegisterPromise where
  transform := fun s => s
  relation := PromiseRelation.changedObservation.comp PromiseRelation.weakened
  price := forkPrice
  discharge := .free (fun _ _ _ _ => trivial)
  entails := fun h => absurd h (by decide)
  admitsAll := fun _ _ _ => trivial
  singular := fun h => absurd h (by decide)
  shrinking := fun _ h => h
  trustKept := fun _ _ h => h
  premisesCharged := fun _ hq hp => absurd hq hp

/-- ⚠ **Forking is changed-observation AND weakened.** The singular contract is
exactly what it drops, so the axis that records "the original guarantee survives"
must be clear too. Reporting a fork as "changed observation" alone — one name off
a five-name list — omits that the original promise is no longer delivered, which
is the fact a caller most needs. -/
theorem fork_is_changed_observation_and_weakened :
    fork.relation
      = PromiseRelation.changedObservation.comp PromiseRelation.weakened
    ∧ fork.relation.singularObservation = false
    ∧ fork.relation.entailsOriginal = false
    ∧ fork.relation ≠ PromiseRelation.changedObservation
    ∧ fork.relation ≠ PromiseRelation.weakened := by decide

/-! ### §8.4 The retain-evidence repair — equivalent promise, priced in storage and replay

The promise: answer the exact count. `JoinHom.card_not_incrementallyMergeable`
says no combiner on the two replicated counts is exact, and
`JoinHom.no_count_merge_without_provenance` says why — the pair `(1, 1)` must
answer `1` when the replicas saw the same element and `2` when they saw different
ones. So the promise is deliverable only by an architecture that ships the set.
The invariant does not move, the observation does not move, the trust does not
move; the deployment does, and `retainsEvidence` is the bill. -/

/-- The exact-count promise: demand `k` is admitted exactly when `k` IS the
count. -/
def exactCountPromise : Promise where
  State := GSet Bool
  mergeState := inferInstance
  Demand := Nat
  admits := fun s k => k = JoinHom.card s
  inv := fun _ => True
  trust := []

/-- ⚠ The summary deployment answers wrong: folding the two replicated counts
disagrees with the count of the merged evidence. -/
theorem summary_deployment_disagrees :
    JoinHom.card (Delta.joinAll JoinHom.sawA [JoinHom.sawB])
      ≠ Delta.joinAll (JoinHom.card JoinHom.sawA) ([JoinHom.sawB].map JoinHom.card) :=
  JoinHom.card_fold_disagrees

/-- **The retain-evidence repair.** Identity on the promise on all five axes;
the price is one Bool, and it is forced rather than chosen
(`JoinHom.card_not_incrementallyMergeable`). The discharge is real freedom,
because the evidence architecture is correct for **every** interpreter with no
hypothesis at all. -/
def retainEvidence : Repair exactCountPromise exactCountPromise where
  transform := fun s => s
  relation := PromiseRelation.equivalent
  price := evidencePrice
  discharge := .free (fun _ _ _ _ => trivial)
  entails := fun _ _ h => h
  admitsAll := fun _ _ h => h
  singular := fun _ h => h
  shrinking := fun _ h => h
  trustKept := fun _ _ h => h
  premisesCharged := fun _ hq hp => absurd hq hp

/-- The evidence price is forced: there is no combiner, so no deployment that
ships only results delivers this promise. -/
theorem evidence_price_is_forced : ¬ IncrementallyMergeable JoinHom.card :=
  JoinHom.card_not_incrementallyMergeable

/-- The retain-evidence repair keeps the promise exactly — same invariant, same
observation, same trust. Its entire content is the price and the discharge, which
is what an `equivalent` relation *means*. -/
theorem retainEvidence_is_equivalent :
    retainEvidence.relation = PromiseRelation.equivalent
    ∧ retainEvidence.price = evidencePrice
    ∧ retainEvidence.price ≠ Price.free := by decide

/-! ### §8.5 The weakening repair — present to be refuted

Weakening the invariant is a real exit (`Exits.lean` lists it, and
`Exits.weakenedInvariant_true_always_applies` observes that `True` always
applies). It is also the exit that makes the guard in §9 non-vacuous: a repair
whose flag is clear, and whose delivery of the original promise is provably
FALSE. -/

/-- The uniqueness-ceiling promise: at most one element in the set. Refuted by
`Ceiling.uniqueness_ceiling` in four costumes elsewhere in this tree. -/
def atMostOnePromise : Promise where
  State := GSet Nat
  mergeState := inferInstance
  Demand := Nat
  admits := fun s n => s n = true
  inv := fun s => ∀ m n, s m = true → s n = true → m = n
  trust := []

/-- The promise that promises nothing. -/
def anythingGoesPromise : Promise where
  State := GSet Nat
  mergeState := inferInstance
  Demand := Nat
  admits := fun s n => s n = true
  inv := fun _ => True
  trust := []

/-- **The weakening repair**: keep the carrier, drop the invariant. Free, cheap,
and it does not deliver what was promised. -/
def weaken : Repair atMostOnePromise anythingGoesPromise where
  transform := fun s => s
  relation := PromiseRelation.changedObservation.comp PromiseRelation.weakened
  price := Price.free
  discharge := .free (fun _ _ _ _ => trivial)
  entails := fun h => absurd h (by decide)
  admitsAll := fun _ _ _ => trivial
  singular := fun h => absurd h (by decide)
  shrinking := fun _ h => h
  trustKept := fun _ _ h => h
  premisesCharged := fun _ hq hp => absurd hq hp

/-! ## §9. The guard: a weakened chain cannot be presented as satisfying the original

The composition theorem (`Repair.comp`) is what makes the record a structure
rather than a report. This section is what makes the *relation* load-bearing: the
flag is **satisfiable** (`seamRepair_delivers`, `arbitrate_delivers`),
**refutable** (`weaken_does_not_deliver`), and **not provable in general** — the
three conditions a floor has to meet to be worth stating. -/

/-- ⚠ **The refutation.** `weaken`'s flag is clear, and the claim it would
license is FALSE: the two-element set `{0, 1}` satisfies the repaired promise
(which promises nothing) and violates the original (which promised at most one).
This is why §7's obligations are guarded by flags rather than merely documented —
a `false` flag is not conservatism, it marks a claim that would be a lie. -/
theorem weaken_does_not_deliver : ¬ weaken.DeliversOriginal := by
  intro h
  exact absurd (h (fun n => n == 0 || n == 1) trivial 0 1 (by decide) (by decide))
    (by decide)

/-- ⚠ **The guard, as a theorem about chains.** Compose the identity repair with
a weakening and the chain's `entailsOriginal` is clear, and the chain provably
does not deliver the original promise. No amount of further composition restores
it (`Repair.comp_entails_false_left`), so a chain that meets a budget by
weakening somewhere in the middle cannot be presented as satisfying what was
originally promised — which is codex's objection (b), discharged. -/
theorem weakened_chain_is_not_the_original :
    ((Repair.id atMostOnePromise).comp weaken).relation.entailsOriginal = false
    ∧ ¬ ((Repair.id atMostOnePromise).comp weaken).DeliversOriginal := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd (h (fun n => n == 0 || n == 1) trivial 0 1 (by decide) (by decide))
    (by decide)

/-- The positive half, so the guard is not merely a prohibition: a chain every
link of which keeps the original guarantee delivers it. `Repair.comp_delivers`
is the property-level statement; this is the flag-level one. -/
theorem chain_delivers_of_flags {P Q R : Promise}
    (r : Repair P Q) (t : Repair Q R)
    (hr : r.relation.entailsOriginal = true)
    (ht : t.relation.entailsOriginal = true) :
    (r.comp t).DeliversOriginal :=
  Repair.comp_delivers r t (r.delivers_of_flag hr) (t.delivers_of_flag ht)

/-- A worked chain: arbitrate the duel, then do nothing. The price is
arbitration's — one cut, one epoch of rollback, two charged premises, **zero
crossings** — and the relation still records that trust and shrinkage were spent.
Composition does not launder either. -/
def arbitrateThenNothing : Repair unpinnedEpochPromise arbitratedEpochPromise :=
  arbitrate.comp (Repair.id arbitratedEpochPromise)

/-- The chain's bill, in full. Note the `0` in `seamCrossings` sitting beside the
two charged premises: that is the shape a flat `Nat` price could not print. -/
theorem arbitrateThenNothing_price :
    arbitrateThenNothing.price
      = { seamCrossings := 0, arbiterCuts := 1, rollbackWindow := 1,
          resolutionWrites := 0, retainsEvidence := false, pluralRead := false,
          restrictsReachability := false,
          assumptions := [Premise.trustedAnnouncer, Premise.verdictKnownEverywhere] } := by
  decide

/-- And the chain's relation is arbitration's, unlaundered: trust and shrinkage
still clear, the original guarantee still delivered. -/
theorem arbitrateThenNothing_relation :
    arbitrateThenNothing.relation.trustPreserved = false
    ∧ arbitrateThenNothing.relation.shrinkageKept = false
    ∧ arbitrateThenNothing.relation.entailsOriginal = true := by decide

end Uwueave.Repair
