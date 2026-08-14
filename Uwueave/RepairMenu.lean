/-
# Uwueave.RepairMenu — the menu, GENERATED. `Exits` keeps its vocabulary and loses its authority.

**This file executes codex's verdict on the Repair/Exits split**, quoted whole:

> *Retire `Exits` as an independent semantic authority. Keep its menu UX as a
> generated projection of typed repair schemas.*

and his reason, which is the reason this file exists rather than a doc note:

> *A future theorem will improve `Repair` while an old `Exits` row continues
> printing a scalar zero with a docstring warning. Your entire language thesis
> is that a warning is not enough when the type can prevent the lie.*

`Exits.lean` defines, **independently of `Repair.lean`**, an applicability
proposition (`Exit.Applies`) and a `Nat` price (`Exit.price`) for eight named
exits. `Repair.lean` defines a typed transformation `Repair P Q` between
promises, with an eight-field `Price` record and a five-axis `PromiseRelation`,
each axis guarded by an obligation. The two agree today. Nothing makes them
agree tomorrow: `Exit.price` is a `Nat` a menu author writes down, and §6 of
this file exhibits the drift already present — the ceiling's hand seam row
prints `0` where the clash graph forces `1` under **every** valid seam.

## What is generated, and from what

Every authoritative row below comes from one of exactly three typed sources, and
`RepairCandidate` has exactly three constructors because there are exactly three:

  * **`available`** — a `Repair P Q`. The row's price *is* `r.price`; the row's
    promise-delta *is* `r.relation`. There is no other field to read.
  * **`conditional`** — a `RepairObligation P Q`: a repair minus one named,
    undecided proposition, plus the proof that the displayed price and delta are
    the price and delta of **every** repair the residual buys.
  * **`impossible`** — a `Refutation P`, whose three constructors each carry a
    ∀-quantified refutation (over every finite segment type, over every quota,
    over every repair onto a target). A row is impossible only when the design
    freedom is exhausted, never when one candidate failed.

`Exit` survives as the **display tag** — `RepairCandidate` carries one, and
`tag_and_label_cannot_move_the_price` is the theorem that says it is display and
nothing else: two rows built from one repair show one price whatever their tag
and label say. `Exit.Applies` and `Exit.price` stop being *sources of truth*, and
every worked row's tag has its availability stated beside it. ⚠ Two of the four
are re-derived from the row's own typed data — `ceiling_seam_tag_applies` is the
row's discharge (`Applies` for a seam **is** `SegmentedIConfluent`), and
`ceiling_arbitration_tag_applies` is the row's `admitsAll` witness read at a
merge. The other two are **not**, and that is a finding rather than an oversight:
`balance_escrow_tag_applies` needs `obs` to be a join-homomorphism and every
share to be positive, and `duel_rollback_tag_applies` needs the verdict to be
discard-only, and **no field of `Repair` carries either**. So retiring the *price*
does not mean the typed layer subsumes the *predicate*; those two rows keep
`Exits.lean`'s witnesses (`Exits.balance_escrow_applies`,
`Exits.arbKeep_rolls_back`) and this file says which clauses they are.

## The theorems that retire `Exits`

  * `menu_price_is_projection` — every price a row displays is the `price` field
    of a `Repair`, or of an obligation that agrees with every repair it
    discharges to. Case analysis over all three constructors; there is no fourth
    place a number can enter.
  * `menu_delta_is_projection` — the same for the five-axis delta.
  * `tag_and_label_cannot_move_the_price` / `..._delta` — the display vocabulary
    is inert.
  * `exit_price_is_an_independent_source` — the contrast, with the drift
    exhibited: a hand `0` beside a forced `1`.
  * `consequence_is_free_data` — `MenuEntry.consequence` is a `String` no
    proposition constrains. That is the hole the five surviving "meetings"
    literals sit in (§7).

## The three worked menus, regenerated

§6 rebuilds `Exits.ceilingMenu`, `Exits.balanceMenu` and `Exits.duelMenu` from
typed repairs, and states the row-by-row comparison as theorems rather than
prose. Three findings fall out of the comparison, and each is a theorem here:

  1. **The ceiling's seam row disagrees.** Hand price `0`, generated price `1`,
     and the `1` is forced under every valid seam by the clique the row carries
     (`ceiling_seam_row_disagrees`). `Exits.ceiling_seam_floor_is_zero`'s third
     conjunct already flagged the undercount in prose; here the row cannot print
     the low number at all, because its price comes from a `SeamFloor`.
  2. **Escrow and arbitration have the same crossing projection, not the same
     price, and differ on delivery.**
     `balanceEscrow` delivers the original promise (`balanceEscrow_delivers`);
     `pinArbitrate` and `duelArbitrate` provably do **not**
     (`pinArbitrate_does_not_deliver`, `duelArbitrate_does_not_deliver`) —
     an arbiter that rewrites the state makes its output legal by construction,
     so the output's legality certifies nothing about the input. The escrow now
     charges `Price.restrictsReachability`; one `Nat` per row cannot hold either
     distinction, while the typed price and `PromiseRelation` do.
  3. **The duel's two discriminating rows are ONE repair.** `arbitration` and
     `rollback` are the same map read twice (`Exits.rollback_is_an_arbitration`),
     and here they are literally the same `Repair` value under two tags
     (`duel_two_tags_one_repair`), so the two prices cannot drift apart.

And two rows appear that the hand menus do not have: the ceiling's and the
duel's **escrow** rows, `impossible` with `Exits.pin_escrow_starves` /
`Exits.duel_escrow_starves` — theorems quantified over every quota. In
`Exits.lean` those rows are *absent*. ⟨DONE downstream: the explicit universal
starvation witnesses and impossible-row constructors distinguish "nobody listed
it" from "the row is refuted".⟩ Here an absent row and a refuted row are different
constructors.

## The seam row takes all three constructors — the acceptance test

`seam_row_takes_all_three_constructors`: the **same** row schema is

  * `available` on the pin ceiling, where `MenuTotality.synth` returns a seam and
    the price is the clique-forced `1` (`ceilingSeamRow`);
  * `conditional` on the shared bound, where no covering pool exists at all
    (`balance_has_no_covering_pool` — proved, not assumed), so `synth` cannot be
    called and the row carries the segmentation obligation for a projection the
    caller hands in;
  * `impossible` on "at most one element of `Nat`", by the clique bound
    (`MenuTotality.atMostOne_seam_row_refuted_at_every_finite_segment`).

The obligation the conditional row carries is **satisfiable and refutable and
not provable**: `the_balance_seam_obligation_is_open` discharges it at the
identity seam and refutes it at `Exits.balTotal`.

## Non-claims, labelled

  * ⚠ ⟨scope⟩ **An unsatisfiable residual makes an obligation's price free
    data.** `unsatisfiable_obligation_prices_anything` exhibits it: with
    `residual := False` both agreement fields hold vacuously and the row may
    display any price. The seam obligation does not rely on them for its number
    — `seamObligation_price_is_forced` bounds it below by the carried clique
    under every valid seam, residual or no residual — but a `RepairObligation`
    built by hand with an empty residual is exactly the hole `Exit.seam`'s floor
    is, moved. It is stated, not hidden.
  * **Escrow's reachability restriction is now charged.**
    `Price.restrictsReachability` is a separate Bool currency, not a crossing or
    meeting count. `balanceEscrow_price_and_delta` couples that price projection
    to the exact `PromiseRelation.strengthened` delta and a concrete source-legal
    state the escrowed promise forbids.
  * ⟨SCOPE U-0131, narrowed to unrestricted candidate discovery⟩ **No unrestricted
    menu search.** `MenuTotality.synth` searches for a seam over a covering pool,
    while downstream `FiniteRepairMenu` chooses from an explicitly supplied,
    checked finite catalog. The escrow partition and candidate universe are still
    handed in rather than discovered.
  * ✅ **Done downstream, within a declared finite grammar.**
    `FiniteProductClosure.ClosedScope.mem_menuEntries_iff` and
    `mem_catalog_iff` prove exact soundness and completeness for the closed
    seam/escrow/exposed-fork/full-coordination grammar, and
    `four_constructor_catalog_has_six_rows` checks the worked scope. This does
    not enumerate arbitrary `Repair` values: executable refusal remains exact
    only for the resource-admitted finite scope.
  * ⟨scope⟩ **The full-coordination row's number is a ceiling, not a floor.**
    `full_price_is_the_ceiling` cites `Cost.crossings_le_length`. It is the one
    generated price with no clique behind it, and it is the one number a caller
    may always afford.
  * ⟨scope⟩ **Everything is at `Type`.** Carriers are `Type 0` as in
    `Exits.lean`; `RepairCandidate` lands in `Type 2` only because it carries a
    `Promise`, which is `Type 1`.
  * ⟨scope⟩ **Classical logic: two new uses, and some inherited.** New here:
    `atMostOneSeamRow` and `balance_has_no_covering_pool` each supply a
    `DecidableEq` by `Classical.typeDecidableEq` (as
    `MenuTotality.atMostOne_floor_is_not_vacuous` does), which is what lets the
    refutation quantify over *every* list-covered segment type rather than only
    the decidable ones. Inherited: `ceilingSeamRow` takes it through
    `MenuTotality.synth`, and the worked-menu comparisons take it through
    `Exits.lean`'s own proofs. `#print axioms` on the two headline theorems,
    `menu_price_is_projection` and `menu_delta_is_projection`, reports
    `[propext, Quot.sound]` — neither needs choice, `sorryAx`, nor the pinned
    Lean 4.30 `native_decide` axiom family `_native.native_decide.ax_…`.

## TRANSPORTS row (VIII, repairs and menus)

**`Exits` menu row → `RepairMenu` row** ⚠
*transport* `transport` / `transport_preserves_the_hand_number` — a hand row
becomes a generated row when a typed repair backs it and the repair's
`seamCrossings` **is** the hand `Nat`; the transport is the projection
`Price.seamCrossings`.
*needs* **a typed repair whose crossing count equals the hand number**.
*without it* the first survivor in this file:
`the_ceiling_seam_hand_price_has_no_forced_backing` — the hand `0` is below the
clique-forced `1`, so no `SeamFloor`-priced row can display it. A different
failure survives even when the crossing projection matches:
`ceiling_arbitration_agrees_only_on_crossings` and `no_free_pin_arbitration`
show that the hand row's `0` is also the repair's `seamCrossings`, while the
full price is not free and must charge a trusted-announcer premise. The
transport can succeed there; the scalar reading cannot retain what justified it.

Lineage: `Repair.lean` (the semantic authority this projects FROM) ·
`Exits.lean` (the UX this regenerates, and its witnesses, kept) ·
`MenuTotality.lean` (`synth`, `Clique`, `CertifiedSeam`, the clique bound) ·
`SeamColoring.lean` (`greedySeamFor`, `jointCost`) · `Ancestral.clash_dichotomy`
(cited at the duel, where the ancestral exit is dead).
-/
import Uwueave.Repair
import Uwueave.MenuTotality

namespace Uwueave.RepairMenu

open Uwueave Uwueave.Catalog Uwueave.Segmented
open Uwueave.Repair (Promise Price PromiseRelation Premise Discharge Repair)
open Uwueave.Exits (Exit MenuEntry ExitMenu)
open Uwueave.MenuTotality (Clique)
open Uwueave.SeamColoring (jointCost greedySeamFor ProperColoring)

universe v

/-! ## §1. `SeamFloor` — the number, computed from the clash graph.

`Exits.lean` says its own `Exit.seam` floor is free data and calls that "a hole
in the type"; `MenuTotality.seam_applies_ignores_the_floor` proves it is
(`Iff.rfl`), and `MenuTotality.CertifiedSeam` closes it by computing the floor
from a carried clique. A generated seam row never takes a `Nat`: it takes one of
these. -/

/-- **A forced floor**: a concurrent workload from a common start whose stream
endpoints pairwise clash. The number is `streams.length - 1`, *computed*, and
`SeamFloor.forced` proves it bounds the joint crossing count under **every**
valid seam for the promise — not merely under the one a row happens to offer.

This is `MenuTotality.CertifiedSeam` with the projection removed: a generated row
gets its σ from `MenuTotality.synth` or from the caller, and only ever gets its
number from here. -/
structure SeamFloor (P : Promise) : Type 1 where
  /-- The op alphabet of the workload the floor is quoted against. -/
  Op : Type
  /-- The local transition. -/
  step : P.State → Op → P.State
  /-- The common start. -/
  start : P.State
  /-- The concurrent streams. -/
  streams : List (List Op)
  /-- **The certificate**: their endpoints pairwise clash. -/
  clique : Clique P.inv (streams.map (Cost.run step start))

/-- The floor, computed from the clique rather than supplied. -/
def SeamFloor.floor {P : Promise} (f : SeamFloor P) : Nat := f.streams.length - 1

/-- **The floor is forced** — `MenuTotality.clique_joint_floor` at a promise. At
most one stream can stay in the start fiber, because two streams sitting in one
fiber would have their endpoints certified mergeable by the seam, and the clique
says they are not. -/
theorem SeamFloor.forced {P : Promise} (f : SeamFloor P) {Seg : Type v}
    [DecidableEq Seg] (τ : P.State → Seg) (hτ : SegmentedIConfluent τ P.inv) :
    f.floor ≤ jointCost τ f.step f.start f.streams :=
  MenuTotality.clique_joint_floor hτ f.streams f.clique

/-! ## §2. `Refutation` — an impossible row carries a proof, not a label.

Each constructor is quantified over the design freedom its exit has. A candidate
that failed is not a refutation: `Exits.balance_total_not_a_seam` kills one
projection and is *not* enough to build an `impossible` row here. -/

/-- **Why a row is impossible.** Three constructors, one per refutation this
tree actually proves, each ∀-quantified:

  * `noFiniteSeam` — no projection into any finite segment type is a seam.
    `MenuTotality.atMostOne_seam_row_refuted_at_every_finite_segment` is the
    inhabitant, and it comes from cliques of every size.
  * `escrowStarves` — at the given per-replica charge, **no** quota gives every
    index a positive share. `Exits.pin_escrow_starves` and
    `Exits.duel_escrow_starves` are the inhabitants: a bound of one does not
    divide.
  * `noFreeRepair` — **every** repair onto the named target has a non-free
    price. `Repair.introduced_premise_forces_a_charge` is what makes this
    constructible, and it is the shape of `Repair.no_free_arbitration`. -/
inductive Refutation (P : Promise) : Type 1 where
  /-- No seam into any finite segment type. -/
  | noFiniteSeam
      (h : ∀ (Seg : Type) (C : List Seg), (∀ g : Seg, g ∈ C) →
             ∀ σ : P.State → Seg, ¬ SegmentedIConfluent σ P.inv)
  /-- No positive-share escrow at this charge, for any quota. -/
  | escrowStarves {ι : Type} (obs : P.State → Escrow ι)
      (h : ∀ q : ι → Nat, ¬ (Exit.escrow (S := P.State) ι q obs).Applies P.inv)
  /-- No repair onto this target is free. -/
  | noFreeRepair (target : Promise) (h : ∀ r : Repair P target, r.price ≠ Price.free)

/-! ## §3. `RepairObligation` — a repair minus one named proposition.

The conditional constructor is what a menu prints where a *search* would go.
`Exits.lean`'s historical "a menu is not a solver" gap is discharged downstream
by `FiniteProductClosure.ClosedScope.synthesizeCoupledCapped` over its admitted
finite grammar. Its code axis is sound and complete exactly for applicable
rows, and `inapplicable_candidate_is_not_returned` checks that a false residual
cannot masquerade as a found repair. This structure is the typed residual that
boundary searches: the row is a repair whose only missing piece is named, and
the displayed price and delta are pinned to the repair the residual buys. -/

/-- **A typed synthesis obligation.** `discharge` is a repair the moment
`residual` is proved, and the two agreement fields stop the row from advertising
a price or a delta the discharge will not honour.

⚠ Both agreement fields are `∀ h : residual, …` and therefore hold vacuously when
`residual` is unsatisfiable — see `unsatisfiable_obligation_prices_anything`.
A conditional row whose number must survive that reads it off a `SeamFloor`
instead (`seamObligation_price_is_forced`). -/
structure RepairObligation (P Q : Promise) : Type 1 where
  /-- The residual proposition nothing here decides. -/
  residual : Prop
  /-- The repair, complete the moment the residual is proved. -/
  discharge : residual → Repair P Q
  /-- The price the row displays. -/
  price : Price
  /-- The promise-delta the row displays. -/
  delta : PromiseRelation
  /-- The displayed price is the price of every repair the residual buys. -/
  priceAgrees : ∀ h : residual, (discharge h).price = price
  /-- …and likewise the delta. -/
  deltaAgrees : ∀ h : residual, (discharge h).relation = delta

/-- The obligation with an empty residual: it discharges nothing and agrees with
everything. Constructed to be refuted, immediately below. -/
def emptyObligation (P Q : Promise) (p : Price) (d : PromiseRelation) :
    RepairObligation P Q where
  residual := False
  discharge := fun h => h.elim
  price := p
  delta := d
  priceAgrees := fun h => h.elim
  deltaAgrees := fun h => h.elim

/-- ⚠ **The hole in the conditional constructor, exhibited rather than
described.** With an unsatisfiable residual, `priceAgrees` and `deltaAgrees` hold
for *any* price and *any* delta, so those two fields alone do not make a
conditional row's number honest. This is `Exit.seam`'s free floor
(`MenuTotality.applies_certifies_no_floor`) reappearing one level up, and it is
why the seam obligation of §5 carries a `SeamFloor`. -/
theorem unsatisfiable_obligation_prices_anything (P Q : Promise) (p : Price)
    (d : PromiseRelation) :
    (emptyObligation P Q p d).price = p
    ∧ (emptyObligation P Q p d).delta = d
    ∧ ¬ (emptyObligation P Q p d).residual :=
  ⟨rfl, rfl, fun h => h⟩

/-! ## §4. `RepairCandidate` and `Menu` — the generated row, and the list.

codex's shape, with one addition: the `Exit` and the label ride along as display
data, and `tag_and_label_cannot_move_the_price` is the theorem that they are
display data. -/

/-- **A menu row, generated from a typed source.** The three constructors are
the three typed sources and there is not a fourth: an available repair, a
synthesis obligation, or an impossibility proof.

`tag` and `label` are the display vocabulary — `Exits.lean`'s eight names, kept.
Neither is read by `price` or `delta`. -/
inductive RepairCandidate (P : Promise) : Type 2 where
  /-- A repair exists: the row shows its price and its relation. -/
  | available (tag : Exit P.State) (label : String) (target : Promise)
      (repair : Repair P target)
  /-- A repair exists conditionally on a named residual. -/
  | conditional (tag : Exit P.State) (label : String) (target : Promise)
      (obligation : RepairObligation P target)
  /-- The row is refuted, with the refutation. -/
  | impossible (tag : Exit P.State) (label : String) (reason : Refutation P)

/-- Which constructor a row took, as data a theorem can compare. -/
inductive Shape where
  /-- A repair was exhibited. -/
  | available
  /-- An obligation was exhibited. -/
  | conditional
  /-- A refutation was exhibited. -/
  | impossible
  deriving DecidableEq, Repr

/-- The row's constructor, as a value. -/
def RepairCandidate.shape {P : Promise} : RepairCandidate P → Shape
  | .available .. => Shape.available
  | .conditional .. => Shape.conditional
  | .impossible .. => Shape.impossible

/-- **The price a row displays** — read off the typed source and nowhere else.
An impossible row has no price, which is the honest answer and not a `0`. -/
def RepairCandidate.price {P : Promise} : RepairCandidate P → Option Price
  | .available _ _ _ r => some r.price
  | .conditional _ _ _ o => some o.price
  | .impossible _ _ _ => none

/-- **The promise-delta a row displays** — five axes, each guarded by an
obligation in `Repair`. `Exits.lean`'s corresponding field is a `String`. -/
def RepairCandidate.delta {P : Promise} : RepairCandidate P → Option PromiseRelation
  | .available _ _ _ r => some r.relation
  | .conditional _ _ _ o => some o.delta
  | .impossible _ _ _ => none

/-- The row's price in `Exits.lean`'s single currency, for comparison with a
hand menu. This projection is the whole of what an `Exit.price` could ever have
said. -/
def RepairCandidate.crossings {P : Promise} (c : RepairCandidate P) : Option Nat :=
  c.price.map Price.seamCrossings

/-- Whether a row charges an admission/reachability restriction. This remains
a separate projection from crossings: neither currency converts to the other. -/
def RepairCandidate.reachabilityRestriction {P : Promise}
    (c : RepairCandidate P) : Option Bool :=
  c.price.map Price.restrictsReachability

/-- **⚑ THE THEOREM THAT RETIRES `Exits`, price half.** Every price any row
displays is the `price` field of a `Repair`, or of an obligation that agrees with
the price of every repair its residual buys. The proof is a case analysis over
the whole type: there is no constructor through which an independent `Nat` can
enter a menu. -/
theorem menu_price_is_projection {P : Promise} (c : RepairCandidate P) (p : Price)
    (h : c.price = some p) :
    (∃ (Q : Promise) (r : Repair P Q), r.price = p)
      ∨ (∃ (Q : Promise) (o : RepairObligation P Q),
            o.price = p ∧ ∀ hres : o.residual, (o.discharge hres).price = p) := by
  cases c with
  | available _ _ Q r =>
      exact Or.inl ⟨Q, r, Option.some.inj h⟩
  | conditional _ _ Q o =>
      refine Or.inr ⟨Q, o, Option.some.inj h, ?_⟩
      intro hres
      rw [o.priceAgrees hres]
      exact Option.some.inj h
  | impossible _ _ _ => simp [RepairCandidate.price] at h

/-- **⚑ THE THEOREM THAT RETIRES `Exits`, delta half.** Every promise-delta any
row displays is the `relation` field of a `Repair`, or of an obligation that
agrees with every repair its residual buys. `Exits.lean` has no delta at all —
its `MenuEntry.consequence` is a `String` (§7). -/
theorem menu_delta_is_projection {P : Promise} (c : RepairCandidate P)
    (d : PromiseRelation) (h : c.delta = some d) :
    (∃ (Q : Promise) (r : Repair P Q), r.relation = d)
      ∨ (∃ (Q : Promise) (o : RepairObligation P Q),
            o.delta = d ∧ ∀ hres : o.residual, (o.discharge hres).relation = d) := by
  cases c with
  | available _ _ Q r =>
      exact Or.inl ⟨Q, r, Option.some.inj h⟩
  | conditional _ _ Q o =>
      refine Or.inr ⟨Q, o, Option.some.inj h, ?_⟩
      intro hres
      rw [o.deltaAgrees hres]
      exact Option.some.inj h
  | impossible _ _ _ => simp [RepairCandidate.delta] at h

/-- **The display vocabulary is inert, price half.** Two rows built from one
repair show one price, whatever tag and label they carry. So `Exit` may keep
naming the eight exits without being able to influence a number. -/
theorem tag_and_label_cannot_move_the_price {P Q : Promise} (r : Repair P Q)
    (t t' : Exit P.State) (l l' : String) :
    (RepairCandidate.available t l Q r).price
      = (RepairCandidate.available t' l' Q r).price := rfl

/-- The display vocabulary is inert, delta half. -/
theorem tag_and_label_cannot_move_the_delta {P Q : Promise} (r : Repair P Q)
    (t t' : Exit P.State) (l l' : String) :
    (RepairCandidate.available t l Q r).delta
      = (RepairCandidate.available t' l' Q r).delta := rfl

/-- **Every row keeps its flag's promise.** For an available row, the claim
`entailsOriginal` licenses is discharged by `Repair.delivers_of_flag`; for a
conditional row it is discharged for every repair the residual buys; an
impossible row claims nothing. Total over the type — no row can be listed that
would license the claim without proving it. -/
def RepairCandidate.DeliversOnItsFlag {P : Promise} : RepairCandidate P → Prop
  | .available _ _ _ r => r.relation.entailsOriginal = true → r.DeliversOriginal
  | .conditional _ _ _ o =>
      ∀ h : o.residual, (o.discharge h).relation.entailsOriginal = true →
        (o.discharge h).DeliversOriginal
  | .impossible _ _ _ => True

theorem delivers_on_its_flag {P : Promise} (c : RepairCandidate P) :
    c.DeliversOnItsFlag := by
  cases c with
  | available _ _ _ r => exact fun h => r.delivers_of_flag h
  | conditional _ _ _ o => exact fun hres h => (o.discharge hres).delivers_of_flag h
  | impossible _ _ _ => exact trivial

/-! ### §4.1 The two unconditional rows, generated

`Exits.ExitMenu.entries` appends a fork row and a full-coordination row to every
menu, so `menu_nonempty` is a theorem about every menu rather than a property
each menu must remember to have. The same discipline here, with the two rows
carrying repairs instead of `Applies` terms. -/

/-- The promise that promises nothing, on the same carrier: `Repair.lean`'s
`forkedRegisterPromise` shape, for an arbitrary promise. -/
def forkedPromise (P : Promise) : Promise := { P with inv := fun _ => True }

/-- **The fork repair, for every promise.** Keep both branches and stop
promising; the target is globally free and `entailsOriginal = false` is what
stops that freedom from reading as a solution to the original problem. The price
is `Repair.forkPrice` — zero crossings, one resolution write, a plural read —
and `Repair.lean` §3.4/§3.6 are the theorems behind those fields. -/
def forkRepair (P : Promise) : Repair P (forkedPromise P) where
  transform := fun s => s
  relation := PromiseRelation.changedObservation.comp PromiseRelation.weakened
  price := Uwueave.Repair.forkPrice
  discharge := .free (fun _ _ _ _ => trivial)
  entails := fun h => absurd h (by decide)
  admitsAll := fun _ _ _ => trivial
  singular := fun h => absurd h (by decide)
  shrinking := fun _ h => h
  trustKept := fun _ _ h => h
  premisesCharged := fun _ hq hp => absurd hq hp

/-- **The full-coordination repair, for every promise.** The identity seam is a
seam for every invariant (`Exits.identity_seam_segmented`), so this row is
unconditional exactly as `Exits.fullCoordination_applies` is — and it carries
that theorem as its discharge rather than as an availability proof.

⚠ Its `n` is the workload length: a **ceiling** (`full_price_is_the_ceiling`),
not a floor. It is the one generated price with no clique behind it. -/
def fullCoordinationRepair (P : Promise) (n : Nat) : Repair P P where
  transform := fun s => s
  relation := PromiseRelation.equivalent
  price := { Price.free with seamCrossings := n }
  discharge := .seam P.State (fun s => s) (Exits.identity_seam_segmented P.inv)
  entails := fun _ _ h => h
  admitsAll := fun _ _ h => h
  singular := fun _ h => h
  shrinking := fun _ h => h
  trustKept := fun _ _ h => h
  premisesCharged := fun _ hq hp => absurd hq hp

/-- **The ceiling, cited**: no workload ever costs more than its length, so the
full-coordination row's price is the number a caller can always afford and never
needs to exceed (`Cost.crossings_le_length`, which is what
`Exits.fullCoordination_is_the_ceiling` reads). -/
theorem full_price_is_the_ceiling {P : Promise} {Op Seg : Type} [DecidableEq Seg]
    (σ : P.State → Seg) (step : P.State → Op → P.State) (s : P.State) (w : List Op) :
    Cost.crossings σ step s w
      ≤ (fullCoordinationRepair P w.length).price.seamCrossings :=
  Cost.crossings_le_length σ step s w

/-- The fork row. -/
def forkCandidate (P : Promise) : RepairCandidate P :=
  .available Exit.exposedFork "exposedFork" (forkedPromise P) (forkRepair P)

/-- The full-coordination row. -/
def fullCandidate (P : Promise) (n : Nat) : RepairCandidate P :=
  .available (Exit.fullCoordination n) "fullCoordination" P (fullCoordinationRepair P n)

/-! ### §4.2 The menu -/

/-- **The generated menu for a clash**: the two replicas that refute
I-confluence, the workload the ceiling is quoted against, and the discriminating
rows. The two unconditional rows are appended by `Menu.rows`, exactly as
`Exits.ExitMenu.entries` does, so no menu can forget them and none has to prove
them. -/
structure Menu (P : Promise) : Type 2 where
  /-- One legal replica of the clash. -/
  x : P.State
  /-- The other. -/
  y : P.State
  /-- `x` is legal … -/
  hx : P.inv x
  /-- … `y` is legal … -/
  hy : P.inv y
  /-- … and the merge is not. -/
  hbad : ¬ P.inv (x ⊔ y)
  /-- The workload the full-coordination ceiling is quoted against. -/
  workload : Nat
  /-- The rows that distinguish this clash from another. -/
  discriminating : List (RepairCandidate P)

/-- The menu as a list: the discriminating rows, then the two unconditional
ones. -/
def Menu.rows {P : Promise} (m : Menu P) : List (RepairCandidate P) :=
  m.discriminating ++ [forkCandidate P, fullCandidate P m.workload]

/-- The prices a caller compares, in `Exits.lean`'s single currency. An
`impossible` row shows `none`, which is the information a `0` destroyed. -/
def Menu.crossings {P : Promise} (m : Menu P) : List (Option Nat) :=
  m.rows.map RepairCandidate.crossings

/-- The reachability-restriction currency for every row, kept separate from
`Menu.crossings`. -/
def Menu.reachabilityRestrictions {P : Promise} (m : Menu P) : List (Option Bool) :=
  m.rows.map RepairCandidate.reachabilityRestriction

/-- **There is always a row, and both guaranteed rows carry repairs.** The
list-level argument is bookkeeping; the content is that `forkRepair` and
`fullCoordinationRepair` are total constructions over every promise, so no clash
leaves a caller with an empty menu and no menu is padded with a row that carries
nothing. -/
theorem menu_nonempty {P : Promise} (m : Menu P) :
    m.rows ≠ []
    ∧ forkCandidate P ∈ m.rows
    ∧ fullCandidate P m.workload ∈ m.rows := by
  have hfork : forkCandidate P ∈ m.rows :=
    List.mem_append_right _ List.mem_cons_self
  have hfull : fullCandidate P m.workload ∈ m.rows :=
    List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨?_, hfork, hfull⟩
  intro hnil
  rw [hnil] at hfork
  exact absurd hfork (List.not_mem_nil)

/-- Both guaranteed rows are `available` — the menu is never padded with a row
that has nothing behind it. -/
theorem guaranteed_rows_are_available (P : Promise) (n : Nat) :
    (forkCandidate P).shape = Shape.available
    ∧ (fullCandidate P n).shape = Shape.available := ⟨rfl, rfl⟩

/-- **The generated menu is sound.** Three conjuncts, and the first is the one
that retires the hand menu:

  1. every price the menu shows is a projection of a typed source
     (`menu_price_is_projection` at every row);
  2. every row keeps its flag's promise (`delivers_on_its_flag`);
  3. the invariant the menu is *for* really does fail I-confluence, recovered
     from the carried pair — so a menu is never advice about a free promise.
     This is `Exits.menu_sound`'s honest conjunct, at the typed level. -/
theorem menu_sound {P : Promise} (m : Menu P) :
    (∀ c ∈ m.rows, ∀ p : Price, c.price = some p →
        (∃ (Q : Promise) (r : Repair P Q), r.price = p)
          ∨ (∃ (Q : Promise) (o : RepairObligation P Q),
              o.price = p ∧ ∀ hres : o.residual, (o.discharge hres).price = p))
    ∧ (∀ c ∈ m.rows, c.DeliversOnItsFlag)
    ∧ ¬ P.Free :=
  ⟨fun c _ p hp => menu_price_is_projection c p hp,
   fun c _ => delivers_on_its_flag c,
   fun hconf => m.hbad (hconf m.x m.y m.hx m.hy)⟩

/-! ## §5. The seam row — one schema, three constructors.

The row that demonstrates the whole type. Its projection comes from
`MenuTotality.synth` where a covering pool exists, from the caller where none
does, and its number always comes from a `SeamFloor`. -/

/-- **The seam repair.** Identity on the promise — same carrier, same invariant,
same observation, same trust — with `SegmentedIConfluent` as its discharge and
the clique-forced floor as its whole price. This is `Repair.lean` §8.1's shape,
with the number taken from the clash graph instead of written down. -/
def seamRepair (P : Promise) (Seg : Type) (σ : P.State → Seg)
    (hσ : SegmentedIConfluent σ P.inv) (f : SeamFloor P) : Repair P P where
  transform := fun s => s
  relation := PromiseRelation.equivalent
  price := { Price.free with seamCrossings := f.floor }
  discharge := .seam Seg σ hσ
  entails := fun _ _ h => h
  admitsAll := fun _ _ h => h
  singular := fun _ h => h
  shrinking := fun _ h => h
  trustKept := fun _ _ h => h
  premisesCharged := fun _ hq hp => absurd hq hp

/-- **The seam row's price is forced under every valid seam** — not merely under
the one it offers. `Exits.seam_price_is_forced` is the sequential form of this
obligation, discharged per menu by hand; here it is a property of the row's own
data. -/
theorem seamRepair_price_is_forced {P : Promise} (Seg : Type) (σ : P.State → Seg)
    (hσ : SegmentedIConfluent σ P.inv) (f : SeamFloor P) {Seg' : Type v}
    [DecidableEq Seg'] (τ : P.State → Seg') (hτ : SegmentedIConfluent τ P.inv) :
    (seamRepair P Seg σ hσ f).price.seamCrossings
      ≤ jointCost τ f.step f.start f.streams :=
  f.forced τ hτ

/-- **The seam obligation**: the row a menu prints for a projection it was
handed and cannot decide. `Exits.lean`'s ⟨DEBT-REF U-0094⟩ — *"it reports that a seam exit
exists for a σ you hand it; it does not synthesize the σ"* — with a type. -/
def seamObligation (P : Promise) (Seg : Type) (σ : P.State → Seg)
    (f : SeamFloor P) : RepairObligation P P where
  residual := SegmentedIConfluent σ P.inv
  discharge := fun h => seamRepair P Seg σ h f
  price := { Price.free with seamCrossings := f.floor }
  delta := PromiseRelation.equivalent
  priceAgrees := fun _ => rfl
  deltaAgrees := fun _ => rfl

/-- **The conditional row's number survives an empty residual.** Its two
agreement fields would go vacuous (`unsatisfiable_obligation_prices_anything`);
the clique does not — the displayed `seamCrossings` is a lower bound on the
carried workload's joint cost under **every** valid seam whether the residual is
provable or not. -/
theorem seamObligation_price_is_forced {P : Promise} (Seg : Type)
    (σ : P.State → Seg) (f : SeamFloor P) {Seg' : Type v} [DecidableEq Seg']
    (τ : P.State → Seg') (hτ : SegmentedIConfluent τ P.inv) :
    (seamObligation P Seg σ f).price.seamCrossings
      ≤ jointCost τ f.step f.start f.streams :=
  f.forced τ hτ

/-- **The conditional seam row is waiting for fiber stability, and nothing else.**
Over a covering pool the row's residual — the segmentation judgement itself —
is *equivalent* to `SeamStableOn`, because the colouring half is a theorem for
every carrier, every decidable invariant and every pool
(`SeamColoring.greedySeamFor_properColoring`). This is
`MenuTotality.seam_row_dichotomy`'s location of the failure, carried by the row's
type instead of stated about the search. -/
theorem seam_residual_is_stability (P : Promise) [DecidableEq P.State]
    [DecidablePred P.inv] (V : List P.State) (hV : ∀ s : P.State, s ∈ V)
    (f : SeamFloor P) :
    (seamObligation P Nat (greedySeamFor P.inv V) f).residual
      ↔ SeamAlgebra.SeamStableOn P.inv (greedySeamFor P.inv V) := by
  constructor
  · intro h
    exact ((SeamColoring.segmented_iff_properColoring hV).mp h).2
  · intro h
    exact (SeamColoring.segmented_iff_properColoring hV).mpr
      ⟨SeamColoring.greedySeamFor_properColoring P.inv V, h⟩

/-- **The seam row, dispatched by the synthesiser.** Over a covering pool
`MenuTotality.synth` either returns a seam — and the row is `available`, carrying
that seam and the clique-forced floor — or returns nothing, in which case the
colouring clause still holds unconditionally
(`SeamColoring.greedySeamFor_properColoring`) and what the `conditional` row is
waiting for is exactly fiber stability (`seam_residual_is_stability`).

⚠ Read the `none` branch at `MenuTotality.seam_row_dichotomy`'s scope: it says
the *greedy* colouring is not fiber-stable, not that no seam exists. -/
def seamRow (P : Promise) [DecidableEq P.State] [DecidablePred P.inv]
    (V : List P.State) (hV : ∀ s : P.State, s ∈ V) (f : SeamFloor P) :
    RepairCandidate P :=
  match MenuTotality.synth P.inv V hV with
  | some ⟨Seg, ⟨σ, hσ⟩⟩ =>
      .available (Exit.seam Seg σ f.floor) "seam (synthesised)" P
        (seamRepair P Seg σ hσ f)
  | none =>
      .conditional (Exit.seam Nat (greedySeamFor P.inv V) f.floor)
        "seam (colouring proper, stability outstanding)" P
        (seamObligation P Nat (greedySeamFor P.inv V) f)

/-- A synthesised seam makes the row `available`. -/
theorem seamRow_available_of_synth (P : Promise) [DecidableEq P.State]
    [DecidablePred P.inv] (V : List P.State) (hV : ∀ s : P.State, s ∈ V)
    (f : SeamFloor P) (h : (MenuTotality.synth P.inv V hV).isSome = true) :
    (seamRow P V hV f).shape = Shape.available := by
  unfold seamRow
  split
  · rfl
  · next hnone => rw [hnone] at h; exact Bool.noConfusion h

/-- The row a menu prints where the search does not exist: the caller's
projection, the clique's number, and the segmentation obligation outstanding. -/
def handedSeamRow (P : Promise) (Seg : Type) (σ : P.State → Seg)
    (f : SeamFloor P) : RepairCandidate P :=
  .conditional (Exit.seam Seg σ f.floor) "seam (candidate handed in, undecided)" P
    (seamObligation P Seg σ f)

/-- The row a menu prints where the exit is refuted for every projection. -/
def refutedSeamRow (P : Promise)
    (h : ∀ (Seg : Type) (C : List Seg), (∀ g : Seg, g ∈ C) →
           ∀ σ : P.State → Seg, ¬ SegmentedIConfluent σ P.inv) :
    RepairCandidate P :=
  .impossible (Exit.seam Bool (fun _ => true) 0)
    "seam (refuted at every finite segment type)" (.noFiniteSeam h)

/-! ## §6. The three worked menus, regenerated.

`Exits.lean` §6 builds three menus by hand for three real clashes. Here they are
rebuilt from typed repairs, and the row-by-row comparison is stated as theorems.
Every clash witness, every availability theorem and every refutation is
`Exits.lean`'s — that file keeps its witnesses; what it loses is the price and
the delta. -/

/-! ### §6.1 The uniqueness ceiling — pins, at most one -/

/-- The pin ceiling as a promise. The observation is "which node is pinned", so
`Promise.Singular` at this promise **is** the invariant — the read is singular
exactly when at most one node is pinned (`ceiling_is_singular`). -/
def ceilingPromise : Promise where
  State := Cost.PinSet
  mergeState := inferInstance
  Demand := Bool
  admits := fun s b => s b = true
  inv := Cost.pinInv
  trust := []

instance : DecidableEq ceilingPromise.State := SeamColoring.instDecidableEqPinSet
instance : DecidablePred ceilingPromise.inv := SeamColoring.instDecidablePinInv

/-- The observation is singular, and the proof is the invariant itself. -/
theorem ceiling_is_singular : ceilingPromise.Singular :=
  fun _ h d d' hd hd' => h d d' hd hd'

/-- ⚠ **…and it does not shrink under growth.** A replica holding nothing admits
nobody; the strictly larger state that has pinned `true` admits `true`. So the
`shrinkageKept` axis is discharged at this promise by the two sides being the
same predicate, not by the predicate holding — stated here so the flag is not
read as a claim about the pin feed. -/
theorem ceiling_is_not_shrinking : ¬ ceilingPromise.Shrinking := by
  intro h
  have hle : Cost.emptyPin ⊑ SeamColoring.pinT := by
    show Cost.emptyPin ⊔ SeamColoring.pinT = SeamColoring.pinT
    funext b
    cases b <;> rfl
  have hadm : ceilingPromise.admits SeamColoring.pinT true := rfl
  exact Bool.noConfusion (h Cost.emptyPin SeamColoring.pinT hle true hadm)

/-- The arbitrated ceiling: the same carrier, the same guarantee, and a trusted
announcer in the promise's `trust`. -/
def arbitratedCeilingPromise : Promise where
  State := Cost.PinSet
  mergeState := inferInstance
  Demand := Bool
  admits := fun s b => s b = true
  inv := Cost.pinInv
  trust := [Premise.trustedAnnouncer]

theorem arbitratedCeiling_singular : arbitratedCeilingPromise.Singular :=
  fun _ h d d' hd hd' => h d d' hd hd'

/-- The arbiter's canonicalisation makes **every** state legal: only the
announced winner's pin survives. This is the fact `Exits.pinKeepTrue_arbitrates`
is built from, isolated. -/
theorem pinKeepTrue_legal (s : Cost.PinSet) : Cost.pinInv (Exits.pinKeepTrue s) := by
  intro m n hm hn
  have hm' : (s m && m) = true := hm
  have hn' : (s n && n) = true := hn
  rw [((Bool.and_eq_true _ _).mp hm').2, ((Bool.and_eq_true _ _).mp hn').2]

/-- **The ceiling's arbitration repair.** Trust is spent (`trustedAnnouncer`,
charged in `assumptions`), the announcement and its rollback window are the
price, and — the axis a `Nat` cannot hold — `entailsOriginal` is **clear**,
because the arbiter *rewrites*: the output is legal by construction, so its
legality says nothing about the input (`pinArbitrate_does_not_deliver`).

The discharge is `escalates`: the arbitrated promise is still not I-confluent at
the lattice level. What the arbiter buys is a canonical post-merge verdict, and
naming that as `escalates` is what stops the row implying a verdict it did not
prove. -/
def pinArbitrate : Repair ceilingPromise arbitratedCeilingPromise where
  transform := Exits.pinKeepTrue
  relation := PromiseRelation.weakened.comp PromiseRelation.changedTrust
  price := { Price.free with
             arbiterCuts := 1, rollbackWindow := 1,
             assumptions := [Premise.trustedAnnouncer] }
  discharge := .escalates
  entails := fun h => absurd h (by decide)
  admitsAll := fun _ s _ => pinKeepTrue_legal s
  singular := fun _ _ => arbitratedCeiling_singular
  shrinking := fun _ h => h
  trustKept := fun h => absurd h (by decide)
  premisesCharged := fun _ hq _ => hq

/-- ⚠ **The typed arbitration does not deliver the original promise.** Both nodes
pinned is illegal; the arbiter's output for that state is legal. So
`Q.inv (transform s) → P.inv s` is false, and the flag is clear rather than
unproved. `Exits.ceilingMenu` prints this row at `0` beside the escrow-shaped
zeros, and no `Nat` distinguishes it from a row that *does* deliver. -/
theorem pinArbitrate_does_not_deliver : ¬ pinArbitrate.DeliversOriginal := by
  intro h
  exact absurd (h (fun _ => true) (pinKeepTrue_legal (fun _ => true))) (by decide)

/-- **The display tag's availability is re-derived, not asserted.**
`Exits.pinKeepTrue_arbitrates` is exactly the row's own `admitsAll` obligation
read at a merge — so the tag adds no evidence the typed row does not already
carry. -/
theorem ceiling_arbitration_tag_applies :
    (Exit.arbitration (S := Cost.PinSet) Exits.pinKeepTrue).Applies ceilingPromise.inv :=
  fun x y _ _ => pinKeepTrue_legal (x ⊔ y)

/-- The ceiling's forced floor: two streams from the empty pin, endpoints
`{true}` and `{false}`, which clash. The clique is
`MenuTotality.ceilingCertificate`'s, cited rather than re-proved. -/
def ceilingFloor : SeamFloor ceilingPromise where
  Op := Bool
  step := Cost.pinStep
  start := Cost.emptyPin
  streams := [[true], [false]]
  clique := MenuTotality.ceilingCertificate.clique

/-- The floor is `1`, and `1` is forced under every valid seam — the joint
crossing count of the two pin streams. -/
theorem ceilingFloor_is_one :
    ceilingFloor.floor = 1
    ∧ ∀ {Seg : Type} [DecidableEq Seg] (τ : Cost.PinSet → Seg),
        SegmentedIConfluent τ Cost.pinInv →
        1 ≤ jointCost τ Cost.pinStep Cost.emptyPin [[true], [false]] :=
  ⟨rfl, fun τ hτ => ceilingFloor.forced τ hτ⟩

/-- **The ceiling's seam row — `available`, through `MenuTotality.synth`.** The
projection is computed by greedily colouring the clash graph over the four-state
pool; the number is the clique's. -/
def ceilingSeamRow : RepairCandidate ceilingPromise :=
  seamRow ceilingPromise SeamColoring.pinStates SeamColoring.pinStates_complete
    ceilingFloor

/-- The synthesiser really does return a seam here, so the row is `available`. -/
theorem ceilingSeamRow_is_available : ceilingSeamRow.shape = Shape.available :=
  seamRow_available_of_synth _ _ _ _ MenuTotality.synth_pin_isSome

/-- The seam tag's availability, re-derived from the row's own discharge:
`Exit.Applies` for a seam row **is** `SegmentedIConfluent`, so the projection the
synthesiser returned is the tag's evidence, at **every** quoted `n`. The tag's
`Nat` gets no such derivation — that is the whole difference
(`exit_price_is_an_independent_source`). -/
theorem ceiling_seam_tag_applies (n : Nat) :
    (Exit.seam (S := Cost.PinSet) Nat
        (greedySeamFor Cost.pinInv SeamColoring.pinStates) n).Applies ceilingPromise.inv :=
  SeamColoring.pin_synthesized_segmented

/-- The ceiling's escrow row: **impossible**, for every quota, by
`Exits.pin_escrow_starves`. `Exits.ceilingMenu` has no escrow row at all, and its
own ⟨DEBT-REF U-0130⟩ says an absent row means "nobody proved it". -/
def ceilingEscrowRow : RepairCandidate ceilingPromise :=
  .impossible (Exit.escrow (S := Cost.PinSet) Bool (fun _ => 1) Exits.pinCharge)
    "escrow (starves a slot at every quota)"
    (.escrowStarves Exits.pinCharge Exits.pin_escrow_starves)

/-- The ceiling refutation is universal over the quota design freedom. This is
strictly stronger than failing to find one quota: every quota is ruled out. -/
theorem ceiling_escrow_refutation_is_universal :
    ∀ q : Bool → Nat,
      ¬ (Exit.escrow (S := Cost.PinSet) Bool q Exits.pinCharge).Applies
          ceilingPromise.inv :=
  Exits.pin_escrow_starves

/-- The ceiling escrow row records a refutation, rather than merely disappearing
from the menu when no candidate was found. -/
theorem ceilingEscrowRow_is_impossible :
    ceilingEscrowRow.shape = Shape.impossible :=
  rfl

/-- **The ceiling's menu, generated.** Three discriminating rows — a synthesised
seam at the forced floor, the arbitration with its charged premise, and the
escrow *refuted* — plus the two unconditional rows. -/
def ceilingMenu : Menu ceilingPromise where
  x := Exits.pinT
  y := Exits.pinF
  hx := Exits.pinT_legal
  hy := Exits.pinF_legal
  hbad := Exits.pin_clash
  workload := 2
  discriminating :=
    [ ceilingSeamRow,
      .available (Exit.arbitration Exits.pinKeepTrue) "arbitration"
        arbitratedCeilingPromise pinArbitrate,
      ceilingEscrowRow ]

/-- The universally refuted ceiling escrow is still an explicit menu row. -/
theorem ceilingEscrowRow_is_present : ceilingEscrowRow ∈ ceilingMenu.rows := by
  simp [ceilingMenu, Menu.rows]

/-- ⚠ **The ceiling's seam row DISAGREES with the hand menu, and by how much.**
`Exits.ceilingMenu` prints `0`; the generated row prints the clique-forced `1`;
and the `1` is a lower bound on the joint crossing count under every valid seam.
`Exits.ceiling_seam_floor_is_zero`'s third conjunct (`Cost.no_seam_frees_both`)
already said the per-stream `0` undercounts — in a docstring, beside a row that
kept printing the `0`. -/
theorem ceiling_seam_row_disagrees :
    ceilingSeamRow.crossings = some 1
    ∧ (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 0).price = 0
    ∧ ∀ {Seg : Type} [DecidableEq Seg] (τ : Cost.PinSet → Seg),
        SegmentedIConfluent τ Cost.pinInv →
        ¬ jointCost τ Cost.pinStep Cost.emptyPin [[true], [false]] = 0 := by
  refine ⟨rfl, rfl, fun τ hτ hz => ?_⟩
  have h : ceilingFloor.floor ≤ jointCost τ Cost.pinStep Cost.emptyPin [[true], [false]] :=
    ceilingFloor.forced τ hτ
  have h1 : ceilingFloor.floor = 1 := rfl
  omega

/-- **The ceiling's arbitration row agrees on crossings and nowhere else.** The
hand row's `0` is the generated row's `seamCrossings`, and the other seven
currencies are where the price actually is: one announcement, one epoch of
rollback exposure, one charged premise — so the price is not `Price.free` and
the two zeros `Exits.lean`'s ⟨scope⟩ note distinguishes in prose are now
different *values*. -/
theorem ceiling_arbitration_agrees_only_on_crossings :
    pinArbitrate.price.seamCrossings
      = (Exit.arbitration (S := Cost.PinSet) Exits.pinKeepTrue).price
    ∧ pinArbitrate.price ≠ Price.free
    ∧ pinArbitrate.price.assumptions = [Premise.trustedAnnouncer]
    ∧ pinArbitrate.relation.entailsOriginal = false
    ∧ pinArbitrate.relation.trustPreserved = false := by decide

/-- The generated ceiling menu's price list beside the hand menu's. The `none` is
the escrow row: an impossibility, which a list of `Nat`s has no way to say. -/
theorem ceiling_menu_crossings :
    ceilingMenu.crossings = [some 1, some 0, none, some 0, some 2]
    ∧ Exits.ceilingMenu.prices = [0, 0, 0, 2] :=
  ⟨rfl, rfl⟩

/-! ### §6.2 The shared bound — escrow ✓, and the seam row nobody can decide -/

/-- The two-device shared bound as a promise. The observation is "device `d` may
still spend", which is genuinely plural — and genuinely shrinking, because a
larger spend record admits fewer devices. -/
def balancePromise : Promise where
  State := Exits.Balance
  mergeState := inferInstance
  Demand := Bool
  admits := fun f d => f d < 10
  inv := Exits.balanceInv
  trust := []

/-- The observation shrinks under growth: merging takes the pointwise max, so a
device that may still spend in the merged record could already spend in each
replica. Unlike the ceiling's, this axis is inhabited at this promise. -/
theorem balance_is_shrinking : balancePromise.Shrinking := by
  intro x y hxy d hy
  have hmax : Nat.max (x d) (y d) = y d := congrFun hxy d
  have hxd : x d ≤ y d := by
    rw [← hmax]
    exact Nat.le_max_left _ _
  have hy' : y d < 10 := hy
  show x d < 10
  omega

/-- The escrowed promise: each device gets five. Same carrier, same observation,
a strictly stronger invariant. -/
def escrowedBalancePromise : Promise where
  State := Exits.Balance
  mergeState := inferInstance
  Demand := Bool
  admits := fun f d => f d < 10
  inv := fun f => ∀ i, f i ≤ 5
  trust := []

/-- Staying inside the share keeps the shared bound — the entailment
`Exits.balance_escrow_applies` proves, isolated so the repair can cite it twice. -/
theorem escrowed_entails_balance (f : Exits.Balance) (h : ∀ i, f i ≤ 5) :
    Exits.balanceInv f := by
  have h1 := h true
  have h2 := h false
  show f true + f false ≤ 10
  omega

/-- **The escrow repair.** `Catalog.escrow_local_bound_iconfluent` is the
discharge — genuine global freedom — and the original guarantee survives.

What escrow spends is *reachability*: some source-legal state stops being
representable (`escrow_forbids_balX` names it). The price therefore charges
`restrictionPrice`, whose `restrictsReachability` flag is true, while the exact
promise delta is `PromiseRelation.strengthened`. No seam crossing or meeting is
manufactured for this restriction. -/
def balanceEscrow : Repair balancePromise escrowedBalancePromise where
  transform := fun f => f
  relation := PromiseRelation.strengthened
  price := Uwueave.Repair.restrictionPrice
  discharge := .free (Catalog.escrow_local_bound_iconfluent (fun _ => 5))
  entails := fun _ f h => escrowed_entails_balance f h
  admitsAll := fun h => absurd h (by decide)
  singular := fun _ hP f hQ d d' hd hd' =>
    hP f (escrowed_entails_balance f hQ) d d' hd hd'
  shrinking := fun _ h => h
  trustKept := fun _ _ h => h
  premisesCharged := fun _ hq hp => absurd hq hp

/-- The escrow delivers the original promise — the flag is set and the
entailment discharges it. -/
theorem balanceEscrow_delivers : balanceEscrow.DeliversOriginal :=
  balanceEscrow.delivers_of_flag rfl

/-- ⚠ **The state the escrow forbids, named.** One device spending the whole
budget was legal and is not reachable inside the split. -/
theorem escrow_forbids_balX : ¬ escrowedBalancePromise.inv Exits.balX := by
  intro h
  exact absurd (h true) (by decide)

/-- **The escrow's price and promise delta, together.** It charges the distinct
reachability-restriction currency, is therefore not free, reports exactly the
`strengthened` relation, and carries the concrete source-legal state excluded by
the target. A scalar crossing projection remains `0`, but it is no longer the
whole advertised price. -/
theorem balanceEscrow_price_and_delta :
    balanceEscrow.price = Uwueave.Repair.restrictionPrice
    ∧ balanceEscrow.price.restrictsReachability = true
    ∧ balanceEscrow.price ≠ Price.free
    ∧ balanceEscrow.price.seamCrossings = 0
    ∧ balanceEscrow.relation = PromiseRelation.strengthened
    ∧ balanceEscrow.RestrictsReachability := by
  refine ⟨rfl, rfl, by decide, rfl, rfl, ?_⟩
  exact ⟨Exits.balX, Exits.balX_legal, escrow_forbids_balX⟩

/-- ⚠ **The escrow tag's availability is `Exits.balance_escrow_applies`, KEPT —
not re-derived.** Its other two clauses — that `obs` is a join-homomorphism, and
that every share is positive — are content **no field of `Repair` carries**, so
this tag is not recoverable from this row's repair the way the seam and
arbitration tags are. What the row stops taking from the tag is the *price*. -/
theorem balance_escrow_tag_applies :
    (Exit.escrow (S := Exits.Balance) Bool (fun _ => 5) id).Applies balancePromise.inv :=
  Exits.balance_escrow_applies

/-- Spending the whole budget on one device, as a workload step. -/
def balStep (f : Exits.Balance) (d : Bool) : Exits.Balance :=
  f ⊔ (fun b => if b = d then 10 else 0)

/-- Nothing spent. -/
def balZero : Exits.Balance := fun _ => 0

theorem run_balStep_true : Cost.run balStep balZero [true] = Exits.balX := by
  funext b
  cases b <;> rfl

theorem run_balStep_false : Cost.run balStep balZero [false] = Exits.balY := by
  funext b
  cases b <;> rfl

/-- The shared bound's forced floor: two devices each spending the whole budget
from a common empty start, and their endpoints clash (`Exits.balance_clash`). -/
def balanceFloor : SeamFloor balancePromise where
  Op := Bool
  step := balStep
  start := balZero
  streams := [[true], [false]]
  clique := by
    show List.Pairwise _ [Cost.run balStep balZero [true], Cost.run balStep balZero [false]]
    rw [run_balStep_true, run_balStep_false]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
    intro v hv
    have hv' : v = Exits.balY := by simpa using hv
    subst hv'
    exact ⟨Exits.balX_legal, Exits.balY_legal, Exits.balance_clash⟩

/-- ⚠ **No finite pool covers the shared bound's carrier — so `synth` cannot be
called here at all.** `MenuTotality.synth` takes `hV : ∀ s, s ∈ V`; on
`Escrow Bool` the constant records `fun _ => k` are pairwise distinct for every
`k`, so a covering list would have to be longer than itself. This is why the
balance seam row is `conditional` and not merely undecided by accident: the
search that decides the ceiling's row is unavailable, by theorem. -/
theorem balance_has_no_covering_pool (V : List Exits.Balance) :
    ¬ (∀ s : Exits.Balance, s ∈ V) := by
  intro hV
  have hdec : DecidableEq Exits.Balance := Classical.typeDecidableEq _
  have hnd : ((List.range (V.length + 1)).map (fun k => (fun _ => k : Exits.Balance))).Nodup := by
    show List.Pairwise (· ≠ ·) _
    rw [List.pairwise_map]
    exact List.nodup_range.imp (fun hab heq => hab (congrFun heq true))
  have hsub : ∀ s ∈ (List.range (V.length + 1)).map (fun k => (fun _ => k : Exits.Balance)),
      s ∈ V := fun s _ => hV s
  have h := @MenuTotality.nodup_length_le_of_subset _ hdec _ V hnd hsub
  rw [List.length_map, List.length_range] at h
  omega

/-- **The shared bound's seam row — `conditional`.** The projection is the
caller's, the number is the clique's, and the residual is the segmentation
judgement itself. -/
def balanceSeamRow (Seg : Type) (σ : Exits.Balance → Seg) :
    RepairCandidate balancePromise :=
  handedSeamRow balancePromise Seg σ balanceFloor

theorem balanceSeamRow_is_conditional (Seg : Type) (σ : Exits.Balance → Seg) :
    (balanceSeamRow Seg σ).shape = Shape.conditional := rfl

/-- ⚑ **The obligation is satisfiable, refutable, and not provable in general** —
the three conditions a residual has to meet to be worth carrying. It holds at the
identity seam (which is `Exit.fullCoordination` wearing the seam constructor,
`Exits.fullCoordination_has_a_seam`, so the discharge is real but the row it buys
is the expensive one), and it fails at the obvious projection
`Exits.balTotal` (`Exits.balance_total_not_a_seam`). A row that is available at
one candidate and refuted at another is exactly a row nothing decides. -/
theorem the_balance_seam_obligation_is_open :
    (seamObligation balancePromise Exits.Balance (fun s => s) balanceFloor).residual
    ∧ ¬ (seamObligation balancePromise Nat Exits.balTotal balanceFloor).residual :=
  ⟨Exits.identity_seam_segmented Exits.balanceInv,
   fun h => Exits.balance_total_not_a_seam 0 h⟩

/-- **The shared bound's menu, generated.** The escrow, available and delivering;
the seam, conditional at the caller's projection; and the two unconditional rows.
`Exits.balanceMenu` has one discriminating row and no seam row at all. -/
def balanceMenu (Seg : Type) (σ : Exits.Balance → Seg) : Menu balancePromise where
  x := Exits.balX
  y := Exits.balY
  hx := Exits.balX_legal
  hy := Exits.balY_legal
  hbad := Exits.balance_clash
  workload := 2
  discriminating :=
    [ .available (Exit.escrow Bool (fun _ => 5) id) "escrow"
        escrowedBalancePromise balanceEscrow,
      balanceSeamRow Seg σ ]

/-- The generated balance menu beside the hand menu. The escrow row **agrees**
on crossings (`0 = 0`) while its separate reachability-restriction projection
is `true`; the seam row is new — `Exits.balanceMenu` has none, because the
obvious projection was refuted and nothing was printed in its place. -/
theorem balance_menu_crossings (Seg : Type) (σ : Exits.Balance → Seg) :
    (balanceMenu Seg σ).crossings = [some 0, some 1, some 0, some 2]
    ∧ Exits.balanceMenu.prices = [0, 0, 2] :=
  ⟨rfl, rfl⟩

/-- The typed menu preserves the currency the hand `Nat` menu cannot show:
only the escrow row restricts reachability. -/
theorem balance_menu_reachability_restrictions
    (Seg : Type) (σ : Exits.Balance → Seg) :
    (balanceMenu Seg σ).reachabilityRestrictions =
      [some true, some false, some false, some false] := rfl

/-! ### §6.3 The duelling admins — two hand rows, one repair -/

/-- The duel as a promise. The observation is "which id holds an admin grant",
so `Promise.Singular` here **is** `Authority.SoleAdmin`. -/
def duelPromise : Promise where
  State := Authority.GrantSet
  mergeState := inferInstance
  Demand := Nat
  admits := fun s i => ∃ σ, s (i, 0, σ) = true
  inv := Authority.SoleAdmin
  trust := []

/-- The arbitrated duel: the same carrier and guarantee, one announced winner. -/
def arbitratedDuelPromise : Promise where
  State := Authority.GrantSet
  mergeState := inferInstance
  Demand := Nat
  admits := fun s i => ∃ σ, s (i, 0, σ) = true
  inv := Authority.SoleAdmin
  trust := [Premise.trustedAnnouncer]

theorem arbitratedDuel_singular : arbitratedDuelPromise.Singular := by
  intro _ h d d' hd hd'
  obtain ⟨σ, hσ⟩ := hd
  obtain ⟨σ', hσ'⟩ := hd'
  exact h d σ d' σ' hσ hσ'

/-- Pruning to the announced winner makes **every** state sole-ruled: the
surviving root grants all carry the winner's id. -/
theorem arbKeep_sole (w : Nat) (s : Authority.GrantSet) :
    Authority.SoleAdmin (Exits.arbKeep w s) := by
  intro i σ i' σ' h h'
  have h1 : (s (i, 0, σ) && (!((0 : Nat) == 0) || (i == w))) = true := h
  have h2 : (s (i', 0, σ') && (!((0 : Nat) == 0) || (i' == w))) = true := h'
  have hi : i = w := by
    have h3 : (!((0 : Nat) == 0) || (i == w)) = true := ((Bool.and_eq_true _ _).mp h1).2
    rw [show (!((0 : Nat) == 0)) = false from rfl, Bool.false_or] at h3
    exact eq_of_beq h3
  have hi' : i' = w := by
    have h4 : (!((0 : Nat) == 0) || (i' == w)) = true := ((Bool.and_eq_true _ _).mp h2).2
    rw [show (!((0 : Nat) == 0)) = false from rfl, Bool.false_or] at h4
    exact eq_of_beq h4
  rw [hi, hi']

/-- **The duel's arbitration repair** — and `Exits.duelMenu`'s *two*
discriminating rows are both this one value (`duel_two_tags_one_repair`). Trust
is spent and charged; `entailsOriginal` is clear for the same reason as the
ceiling's: the arbiter rewrites, so the output's legality certifies nothing about
the input.

⚠ As at the ceiling (`ceiling_is_not_shrinking`), `shrinkageKept` is discharged
here by the two sides being the *same* predicate — same carrier, same
observation — and is not a claim that the grant feed shrinks under growth. It
does not: grants only accumulate. -/
def duelArbitrate : Repair duelPromise arbitratedDuelPromise where
  transform := Exits.arbKeep 1
  relation := PromiseRelation.weakened.comp PromiseRelation.changedTrust
  price := { Price.free with
             arbiterCuts := 1, rollbackWindow := 1,
             assumptions := [Premise.trustedAnnouncer] }
  discharge := .escalates
  entails := fun h => absurd h (by decide)
  admitsAll := fun _ s _ => arbKeep_sole 1 s
  singular := fun _ _ => arbitratedDuel_singular
  shrinking := fun _ h => h
  trustKept := fun h => absurd h (by decide)
  premisesCharged := fun _ hq _ => hq

/-- ⚠ The duel's arbitration does not deliver the original promise either: the
merged duel state is illegal and its arbitrated image is legal. -/
theorem duelArbitrate_does_not_deliver : ¬ duelArbitrate.DeliversOriginal := by
  intro h
  exact Exits.duel_clash
    (h (Authority.aliceRoot ⊔ Authority.bobRoot)
      (arbKeep_sole 1 (Authority.aliceRoot ⊔ Authority.bobRoot)))

/-- ⚠ **The rollback tag's extra content is `Exits.arbKeep_rolls_back`, KEPT.**
That the same map only ever *discards* (`keep s ⊑ s`) is what makes
`Exits.rollback_loses_a_replica` available — and
`Exits.duel_rollback_loses_a_duellist` is that loss at the duel pair — and it is
the second clause `Repair` has no field for. The tag keeps the witness; it no
longer keeps a price. -/
theorem duel_rollback_tag_applies :
    (Exit.rollback (S := Authority.GrantSet) (Exits.arbKeep 1)).Applies duelPromise.inv :=
  Exits.arbKeep_rolls_back 1

/-- The duel's escrow row: **impossible** for every quota
(`Exits.duel_escrow_starves`) — one admin does not divide among many ids. -/
def duelEscrowRow : RepairCandidate duelPromise :=
  .impossible (Exit.escrow (S := Authority.GrantSet) Nat (fun _ => 1) Exits.grantCharge)
    "escrow (starves every id but one, at every quota)"
    (.escrowStarves Exits.grantCharge Exits.duel_escrow_starves)

/-- The duel refutation is universal over the quota design freedom. This is not
the weaker observation that one attempted quota failed. -/
theorem duel_escrow_refutation_is_universal :
    ∀ q : Nat → Nat,
      ¬ (Exit.escrow (S := Authority.GrantSet) Nat q Exits.grantCharge).Applies
          duelPromise.inv :=
  Exits.duel_escrow_starves

/-- The duel escrow row records a refutation, rather than merely disappearing
from the menu when no candidate was found. -/
theorem duelEscrowRow_is_impossible : duelEscrowRow.shape = Shape.impossible :=
  rfl

/-- **The duel's menu, generated.** The arbitration and the rollback are two
display tags over **one** repair; the escrow is refuted; the two unconditional
rows follow. -/
def duelMenu : Menu duelPromise where
  x := Authority.aliceRoot
  y := Authority.bobRoot
  hx := Authority.aliceRoot_sole
  hy := Authority.bobRoot_sole
  hbad := Exits.duel_clash
  workload := 2
  discriminating :=
    [ .available (Exit.arbitration (Exits.arbKeep 1)) "arbitration"
        arbitratedDuelPromise duelArbitrate,
      .available (Exit.rollback (Exits.arbKeep 1)) "rollback"
        arbitratedDuelPromise duelArbitrate,
      duelEscrowRow ]

/-- The universally refuted duel escrow is still an explicit menu row. -/
theorem duelEscrowRow_is_present : duelEscrowRow ∈ duelMenu.rows := by
  simp [duelMenu, Menu.rows]

/-- ⚑ **The duel's two hand rows are one repair.** `Exits.duelMenu` prints an
arbitration row and a rollback row, both at `0`, and its own docstring says they
are "the same map, read twice" (`Exits.rollback_is_an_arbitration`). Here they
are the same *value*, so the two prices and the two deltas cannot drift apart —
which is precisely the drift a second hand-written `Nat` invites. -/
theorem duel_two_tags_one_repair :
    (RepairCandidate.available (Exit.arbitration (Exits.arbKeep 1)) "arbitration"
        arbitratedDuelPromise duelArbitrate).price
      = (RepairCandidate.available (Exit.rollback (Exits.arbKeep 1)) "rollback"
        arbitratedDuelPromise duelArbitrate).price
    ∧ (RepairCandidate.available (Exit.arbitration (Exits.arbKeep 1)) "arbitration"
        arbitratedDuelPromise duelArbitrate).delta
      = (RepairCandidate.available (Exit.rollback (Exits.arbKeep 1)) "rollback"
        arbitratedDuelPromise duelArbitrate).delta :=
  ⟨rfl, rfl⟩

/-- The generated duel menu beside the hand menu: the two arbitration-shaped
rows agree on crossings (`0 = 0`), the escrow row is the refutation the hand menu
left absent, and the unconditional rows agree exactly. -/
theorem duel_menu_crossings :
    duelMenu.crossings = [some 0, some 0, none, some 0, some 2]
    ∧ Exits.duelMenu.prices = [0, 0, 0, 2] :=
  ⟨rfl, rfl⟩

/-! ## §7. What `Exits` keeps, and what it stops being.

Two theorems about the hand menu's remaining fields, and one about what replaced
them. Neither is a criticism of `Exits.lean`'s proofs — every refutation and
every availability theorem cited above is that file's. -/

/-- ⚠ **`Exit.price` is an independent source, and the drift is already here.**
The hand seam row for the pin ceiling is available at *any* floor
(`MenuTotality.seam_applies_ignores_the_floor`), prints `0`, and `0` is strictly
below the number the clash graph forces. A generated row cannot do this: its
number comes from a `SeamFloor`, and `seamRepair_price_is_forced` bounds it. -/
theorem exit_price_is_an_independent_source :
    (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 0).Applies Cost.pinInv
    ∧ (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 5).Applies Cost.pinInv
    ∧ (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 0).price
        ≠ (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 5).price :=
  ⟨Cost.seamFalse_segmented, Cost.seamFalse_segmented, by decide⟩

/-- ⚠ **`MenuEntry.consequence` is free data.** Two rows with the same exit and
the same availability proof carrying contradictory sentences are both
constructible and distinct, so no proposition constrains the string. That is the
hole the five surviving "meetings" literals sit in — `Exits.forkEntry`,
`Exits.fullEntry`, and the `arbitration`/`escrow`/`arbitration` rows of
`Exits.ceilingMenu`, `Exits.balanceMenu`, `Exits.duelMenu` — and it is
why a generated row's delta is a `PromiseRelation` and not a sentence: five
Bools, each guarded by an obligation in `Repair`, and a `true` you have not
proved is not constructible. -/
theorem consequence_is_free_data {S : Type} [MergeState S] {I : Invariant S}
    (e : Exit S) (h : e.Applies I) (s t : String) (hst : s ≠ t) :
    (⟨e, h, s⟩ : MenuEntry I).exit = (⟨e, h, t⟩ : MenuEntry I).exit
      ∧ (⟨e, h, s⟩ : MenuEntry I) ≠ (⟨e, h, t⟩ : MenuEntry I) :=
  ⟨rfl, fun heq => hst (congrArg MenuEntry.consequence heq)⟩

/-! ## §8. TRANSPORT: an `Exits` row → a `RepairMenu` row.

The transport is the projection `Price.seamCrossings`; the hypothesis is that a
typed repair backs the hand row at that number. The two examples below separate
two failures: the seam row has no forced backing at its hand number, while the
arbitration row can match that number and still lose every non-crossing price
when read through the scalar projection. -/

/-- **The transport.** A hand row becomes a generated row when a typed repair
backs it and the repair's crossing count is the hand row's `Nat`. -/
def transport {P : Promise} (e : MenuEntry P.inv) (Q : Promise) (r : Repair P Q)
    (_h : r.price.seamCrossings = e.exit.price) : RepairCandidate P :=
  .available e.exit "transported from Exits" Q r

/-- The transported row shows the repair's price — all eight fields. -/
theorem transport_shows_the_repairs_price {P : Promise} (e : MenuEntry P.inv)
    (Q : Promise) (r : Repair P Q) (h : r.price.seamCrossings = e.exit.price) :
    (transport e Q r h).price = some r.price := rfl

/-- …and its crossing projection is exactly the hand row's number, so the hand
menu's `Nat` is recovered and never re-authored. -/
theorem transport_preserves_the_hand_number {P : Promise} (e : MenuEntry P.inv)
    (Q : Promise) (r : Repair P Q) (h : r.price.seamCrossings = e.exit.price) :
    (transport e Q r h).crossings = some e.exit.price := by
  show some r.price.seamCrossings = some e.exit.price
  rw [h]

/-- ⚠ **Counterexample 1 — a hand price no *forced* row can back.**
`Exits.ceilingMenu`'s seam row prints `0`. The clique the same clash carries
forces `1` under every valid seam, so a generated seam row, whose number comes
from a `SeamFloor`, can never display the hand number. The transport's hypothesis
fails, and the failure is the finding. -/
theorem the_ceiling_seam_hand_price_has_no_forced_backing :
    (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 0).price = 0
    ∧ ceilingFloor.floor = 1
    ∧ ceilingFloor.floor ≠ (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 0).price :=
  ⟨rfl, rfl, by decide⟩

/-- ⚠ **Counterexample 2 — matching the hand number does not make the repair
free.** `Exits.ceilingMenu`'s arbitration row prints `0`, and
`ceiling_arbitration_agrees_only_on_crossings` proves that a typed arbitration
repair can have the same `seamCrossings`, so this is **not** a counterexample to
`transport`'s hypothesis. It is the counterexample to reading that scalar as a
complete price. Quantified over **every** repair onto the arbitrated ceiling
promise, however anyone prices it: the price is not `Price.free` and its
`assumptions` are not empty, because `Premise.trustedAnnouncer` is in the
target's trust and not in the source's, and `premisesCharged` has no flag to
clear. This is `Repair.no_free_arbitration` at the exit whose crossing projection
is zero. -/
theorem no_free_pin_arbitration (r : Repair ceilingPromise arbitratedCeilingPromise) :
    r.price ≠ Price.free ∧ r.price.assumptions ≠ [] := by
  have hq : Premise.trustedAnnouncer ∈ arbitratedCeilingPromise.trust := by decide
  have hp : ¬ (Premise.trustedAnnouncer ∈ ceilingPromise.trust) := by decide
  refine ⟨Uwueave.Repair.Repair.introduced_premise_forces_a_charge r hq hp, ?_⟩
  intro hnil
  have hm := r.premisesCharged Premise.trustedAnnouncer hq hp
  rw [hnil] at hm
  simp at hm

/-- The refutation as a row, so the counterexample is a value a menu could
print: "arbitration, free" is impossible on the ceiling. -/
def freeArbitrationIsImpossible : Refutation ceilingPromise :=
  .noFreeRepair arbitratedCeilingPromise (fun r => (no_free_pin_arbitration r).1)

/-! ## §9. The acceptance test — one row schema, three constructors. -/

/-- The at-most-one ceiling over `Nat`, as a promise: `MenuTotality.atMostOne`,
whose clash graph has cliques of every size. -/
def atMostOnePromise : Promise where
  State := GSet Nat
  mergeState := inferInstance
  Demand := Nat
  admits := fun s n => s n = true
  inv := MenuTotality.atMostOne
  trust := []

/-- **The at-most-one ceiling's seam row — `impossible`**, by the clique bound.
No projection into any finite segment type is a seam, so this is a refutation of
the exit and not of a candidate. -/
def atMostOneSeamRow : RepairCandidate atMostOnePromise :=
  refutedSeamRow atMostOnePromise
    (fun Seg C hC σ hσ =>
      @MenuTotality.atMostOne_seam_values_are_infinite Seg (Classical.typeDecidableEq Seg)
        σ hσ C (fun s _ => hC (σ s)))

/-- ⚑ **THE ACCEPTANCE TEST.** The same row — the seam row — takes all three
constructors, and what decides which is not a menu author's judgement but the
promise:

  * `available` on the pin ceiling, because `MenuTotality.synth` returns a seam
    over the four-state pool and a clique forces the number;
  * `conditional` on the shared bound, because no finite pool covers the carrier
    (`balance_has_no_covering_pool`), so the search that decided the ceiling
    cannot run and the projection is the caller's;
  * `impossible` on the at-most-one ceiling over `Nat`, because cliques of every
    size refute every finite seam.

`MenuTotality.the_element_type_decides_the_seam_row` is the same discrimination
one level down: the *same* invariant shape over `Bool` and over `Nat`. -/
theorem seam_row_takes_all_three_constructors :
    ceilingSeamRow.shape = Shape.available
    ∧ (balanceSeamRow Nat Exits.balTotal).shape = Shape.conditional
    ∧ atMostOneSeamRow.shape = Shape.impossible :=
  ⟨ceilingSeamRow_is_available, rfl, rfl⟩

/-- …and the three carry evidence, not labels: a forced floor of `1` under every
valid seam on the ceiling, an obligation that is satisfiable and refutable on the
shared bound, and a refutation quantified over every finite segment type. -/
theorem the_three_constructors_carry_evidence :
    ceilingSeamRow.crossings = some 1
    ∧ (balanceSeamRow Nat Exits.balTotal).crossings = some 1
    ∧ atMostOneSeamRow.crossings = none
    ∧ (seamObligation balancePromise Exits.Balance (fun s => s) balanceFloor).residual
    ∧ ¬ (seamObligation balancePromise Nat Exits.balTotal balanceFloor).residual
    ∧ ∀ (σ : GSet Nat → Bool) (n : Nat),
        ¬ (Exit.seam (S := GSet Nat) Bool σ n).Applies MenuTotality.atMostOne :=
  ⟨rfl, rfl, rfl, the_balance_seam_obligation_is_open.1,
   the_balance_seam_obligation_is_open.2,
   MenuTotality.the_element_type_decides_the_seam_row.2⟩

/-! ## §10. What became true — collected.

Five statements, one per deliverable, so the module docstring's claims have an
audit trail that is a term. -/

/-- **The five verdicts, as one term.**

  1. Every displayed price is a projection of a typed source (§4).
  2. Every displayed delta likewise, and the display tag moves neither.
  3. The three worked menus are generated, and their crossing lists sit beside
     the hand menus' (§6).
  4. The seam row takes all three constructors (§9).
  5. The hand menu's two remaining authorities — `Exit.price` and
     `MenuEntry.consequence` — are free data, and the transport into this file
     has two surviving counterexamples (§7, §8). -/
theorem what_became_true :
    (∀ {P : Promise} (c : RepairCandidate P) (p : Price), c.price = some p →
      (∃ (Q : Promise) (r : Repair P Q), r.price = p)
        ∨ (∃ (Q : Promise) (o : RepairObligation P Q),
            o.price = p ∧ ∀ hres : o.residual, (o.discharge hres).price = p))
    ∧ ceilingMenu.crossings = [some 1, some 0, none, some 0, some 2]
    ∧ (∀ (Seg : Type) (σ : Exits.Balance → Seg),
        (balanceMenu Seg σ).crossings = [some 0, some 1, some 0, some 2])
    ∧ (∀ (Seg : Type) (σ : Exits.Balance → Seg),
        (balanceMenu Seg σ).reachabilityRestrictions =
          [some true, some false, some false, some false])
    ∧ duelMenu.crossings = [some 0, some 0, none, some 0, some 2]
    ∧ ceilingSeamRow.shape = Shape.available
    ∧ atMostOneSeamRow.shape = Shape.impossible
    ∧ (∀ r : Repair ceilingPromise arbitratedCeilingPromise, r.price ≠ Price.free) :=
  ⟨fun c p h => menu_price_is_projection c p h,
   rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, ceilingSeamRow_is_available, rfl,
   fun r => (no_free_pin_arbitration r).1⟩

end Uwueave.RepairMenu
