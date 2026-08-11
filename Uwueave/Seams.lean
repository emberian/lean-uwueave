/-
# Uwueave.Seams — seams two and three: the segmented pattern as a tool.

`Segmented.lean` proved one seam (the budget: spends free, re-allocation the
coordination point) and `Spec.budgetSegVerdict` packaged it. One instance is a
museum piece; this file adds the second and third seams so `SegmentedIConfluent`
is a *design recipe* — when the DSL hands you a clash, hunt for the σ your
application can hold fixed between explicit coordination events.

  * **The epoch seam (§1)** — ERA's architecture read through Whittaker's lens.
    `Authority.lean` proves the duelling-admins clash twice
    (`sole_admin_not_iconfluent`, `duelling_revocations_not_iconfluent`) and
    honestly declines to fix it: fail-closed annihilates both duellists. ERA
    (Kegan Dougal, "ERA: Epoch-Resolved Arbitration for Duelling Admins in
    Group Management CRDTs", PaPoC 2026, arXiv:2601.22963) buys a survivor with
    epoch-batched external arbitration; Whittaker–Hellerstein ("Interactive
    Checks for Coordination Avoidance", VLDB'19) supply the judgement that says
    *where* the buying happens. Read together: σ = the epoch, the arbitration
    verdict rides the seam, and within an epoch admin state merges freely.
    §1 proves that reading on a miniature carrier — including, as a named dead
    end, that the epoch *alone* fixes nothing (`sole_unpinned_not_segmented`):
    it is the arbitration verdict the seam carries, not the seam itself, that
    dissolves the duel. That is ERA's thesis, machine-checked at toy scale.
  * **The schema-version seam (§2)** — the flag day. A store whose
    well-formedness reads the schema version fails I-confluence globally when a
    migration *tightens* a constraint (an old-version replica's legal data
    poisons the new schema), yet is segmented over σ = the version: same-version
    replicas gossip freely, and crossing versions is the coordination point —
    which is precisely what deployment practice calls a flag day. The honest
    surprise found on the way: a *widening* migration needs no seam at all
    (`schema_widening_iconfluent`) — the proof-shaped reason expand/contract
    migrations deploy by rolling upgrade while `NOT NULL`-style tightenings
    take an outage window.
  * **§3** packages both as `SegVerdict` inhabitants (`epochSegVerdict`,
    `schemaSegVerdict`), so the DSL's seam row now has three: budget, epoch,
    schema.

## What is claimed, and on what carrier

Both carriers are miniatures in the house style (`Nat`-indexed, `GSet` fibers,
`decide`-checked witnesses). ERA's actual protocol — how replicas *learn* an
epoch's arbitration verdict, how an epoch change is proposed and settled — is
not formalized; here the verdict stream is an oracle parameter `arb : Nat → Nat`
and an epoch change is nothing but a change of σ. What IS proved: the coherence
invariants below fail I-confluence globally with duelling-shaped witnesses, and
hold it within every fiber of their seam. The modal reading ("so coordination
is needed exactly at the seam") is Bailis et al.'s necessity theorem, cited not
re-proved — the discipline of `Confluence.lean` §2.
-/
import Uwueave.Spec
import Uwueave.Authority

namespace Uwueave.Seams

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.Spec

/-! ## §1. The epoch seam — duelling admins, arbitrated at the boundary -/

/-- The epoch-indexed authority state: the current epoch, and for every epoch
the grow-only set of admin claims recorded for it — `s.2 e a = true` reads
"`a` is claimed as an admin of epoch `e`". The epoch merges by `max` (a replica
never returns to a settled epoch), the claim fibers pointwise by union; both
instances are inherited, nothing new is proved. The *current* epoch selects
which claim-set is authoritative — claims parked at other epochs are latent. -/
abbrev EpochState := Nat × (Nat → GSet Nat)

example : MergeState EpochState := inferInstance

/-- ⚠ **Dead end, proved: the epoch seam alone does not dissolve the duel.**
"At most one admin claim in the current epoch" — Authority's `SoleAdmin`, read
in the current fiber — is not even *segmented* over the epoch: two replicas in
the SAME epoch each mint their own admin (the `aliceRoot`/`bobRoot` scenario of
`Authority.sole_admin_not_iconfluent`, re-witnessed in this carrier), and their
merge holds both claims without ever crossing the seam. Epochs are a batching
structure, not an arbitration policy; an unpinned fiber duels exactly as freely
as an unpinned world. What repairs it is pinning the fiber to a verdict —
`EpochSole` below — which is ERA's actual design: the epoch exists to *carry*
an arbitration result. -/
theorem sole_unpinned_not_segmented :
    ¬ SegmentedIConfluent (S := EpochState) Prod.fst
      (fun s => ∀ m n, s.2 s.1 m = true → s.2 s.1 n = true → m = n) := by
  intro h
  have hmerge := (h (0, fun _ a => a == 1) (0, fun _ a => a == 2)
    rfl
    (fun m n hm hn => by simp at hm hn; omega)
    (fun m n hm hn => by simp at hm hn; omega)).1
  exact absurd (hmerge 1 2 (by decide) (by decide)) (by decide)

/-- **Dead end at the other extreme, proved: pin every fiber and no seam is
left.** If well-formedness demands every epoch's claims — latent ones included —
match the arbiter, the invariant is per-element monotone information and plain
I-confluent: no clash, no seam, nothing to coordinate. But this invariant
presumes every replica already knows every epoch's arbitration verdict,
including epochs it has never entered — exactly the global knowledge whose
absence is the duelling-admins problem. Free, and question-begging; the honest
invariant polices only the authority a replica currently *exercises*
(`EpochSole`). -/
theorem pinned_everywhere_iconfluent (arb : Nat → Nat) :
    IConfluent (S := EpochState) (fun s => ∀ e a, s.2 e a = true → a = arb e) := by
  intro x y hx hy e a ha
  have ha' : (x.2 e a || y.2 e a) = true := ha
  cases (Bool.or_eq_true _ _).mp ha' with
  | inl hxa => exact hx e a hxa
  | inr hya => exact hy e a hya

/-- **Epoch-sole authority, arbitrated**: every admin claim in the *current*
epoch names the arbitrated survivor `arb s.1`. The verdict stream
`arb : Nat → Nat` is ERA's external arbiter as an oracle parameter — how a
replica learns it is protocol, outside this model (the same premise discipline
as `Authority.UniqueGrant`). Claims at non-current epochs are deliberately
unconstrained: they are authority not being exercised, and policing them is the
question-begging dead end above. -/
def EpochSole (arb : Nat → Nat) : Invariant EpochState := fun s =>
  ∀ a, s.2 s.1 a = true → a = arb s.1

/-- The pin subsumes the duel-shaped ceiling: an `EpochSole` state has at most
one distinct admin claimed in its current epoch — `Authority.SoleAdmin`'s shape,
recovered in the fiber, now as a *theorem* of the pinned invariant rather than
an unpreservable extra conjunct. -/
theorem epochSole_at_most_one {arb : Nat → Nat} {s : EpochState}
    (h : EpochSole arb s) (m n : Nat)
    (hm : s.2 s.1 m = true) (hn : s.2 s.1 n = true) : m = n :=
  (h m hm).trans (h n hn).symm

/-- The demo arbitration stream: epoch `e` is ruled by member `e` — so epoch 1
belongs to Alice (member 1), epoch 2 to Bob (member 2). Any `arb` with
`arb 1 ≠ arb 2` tells the same story; this one keeps every witness `decide`-able. -/
def demoArb : Nat → Nat := fun e => e

/-- ⚠ **Globally, arbitrated epoch-sole authority is NOT I-confluent — the
duelling-admins clash, re-witnessed across the seam.** Alice's partition sits in
epoch 1 (where arbitration made her admin) and writes her claim into every
epoch's fiber — "Alice, forever", legal on her replica because only the current
fiber is policed. Bob's partition has crossed the seam to epoch 2, whose
arbitration verdict appointed Bob. The merge lands in epoch 2 holding both
claims, and Alice's contradicts the arbiter: two locally-coherent replicas, one
incoherent union — `Authority.sole_admin_not_iconfluent`'s scenario with the
duel displaced onto the seam crossing itself. This is the clash that prices
epoch *changes*; `epoch_segmented` proves it is confined to them. -/
theorem epoch_sole_not_iconfluent :
    ¬ IConfluent (S := EpochState) (EpochSole demoArb) := by
  intro h
  have hmerge := h (1, fun _ a => a == 1) (2, fun e a => e == 2 && a == 2)
    (fun a ha => by simp at ha; exact ha)
    (fun a ha => by simp at ha; exact ha)
  exact absurd (hmerge 1 (by decide)) (by decide)

/-- **Within an epoch, admin state merges freely** — `EpochSole` is segmented
over σ = the epoch, for EVERY arbitration stream: same-epoch replicas share the
current verdict, so their unions of claims stay pinned to it, and `max` of
equal epochs cannot cross the seam. Operationally this is ERA's architecture
through Whittaker's lens: run coordination-free inside an epoch; coordinate
exactly to change epoch, and let the change carry the arbitrated survivor. -/
theorem epoch_segmented (arb : Nat → Nat) :
    SegmentedIConfluent (S := EpochState) Prod.fst (EpochSole arb) := by
  intro x y hσ hx hy
  have hmax : Nat.max x.1 y.1 = x.1 := by rw [hσ, nat_max_def]; simp
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha' : (x.2 (Nat.max x.1 y.1) a || y.2 (Nat.max x.1 y.1) a) = true := ha
    rw [hmax] at ha'
    show a = arb (Nat.max x.1 y.1)
    rw [hmax]
    cases (Bool.or_eq_true _ _).mp ha' with
    | inl hxa => exact hx a hxa
    | inr hya =>
      have hya' : y.2 y.1 a = true := by rw [← hσ]; exact hya
      rw [hσ]
      exact hy a hya'
  · show Nat.max x.1 y.1 = x.1
    exact hmax

/-- The clash this seam answers, cited as a term: Authority's duelling-admins
refutation, entry side. `Authority.lean` proves the price of fail-closed;
this file's seam is the *other* branch — ERA's — priced at the boundary. -/
example : ¬ IConfluent (S := Authority.GrantSet)
    (fun s => Authority.WF 9 s ∧ Authority.SoleAdmin s) :=
  Authority.sole_admin_not_iconfluent

/-! ## §2. The schema-version seam — migration is a flag day -/

/-- The versioned store: the schema version, and the grow-only set of records —
`s.2 n = true` reads "a record with value `n` has been written". Version merges
by `max` (upgrades don't un-happen), records by union; both instances
inherited. Well-formedness reads the version: which records are legal is the
schema's business, and the schema is state. -/
abbrev SchemaState := Nat × GSet Nat

example : MergeState SchemaState := inferInstance

/-- Version-dependent well-formedness: every record obeys the CURRENT schema's
bound. `bound` is the migration policy — `bound 0 = 20, bound 1 = 10` is a
tightening migration (version 1 deprecates large values), `bound 0 = 10,
bound 1 = 20` a widening one; the classification below splits on exactly that
difference. -/
def SchemaWF (bound : Nat → Nat) : Invariant SchemaState := fun s =>
  ∀ n, s.2 n = true → n ≤ bound s.1

/-- **A widening migration needs no seam** — with a monotone bound, `SchemaWF`
is plainly I-confluent: the merged version is one of the two versions, each
record was legal under its writer's bound, and widening carries it forward.
This was the first schema-seam candidate ("v0 bounded by 10, v1 by 20") and it
is a proved dead end for clash-hunting — there is no counterexample to find.
The practice it explains: purely additive/widening migrations (the *expand*
half of expand/contract) deploy by rolling upgrade, no coordination, no outage. -/
theorem schema_widening_iconfluent (bound : Nat → Nat)
    (hmono : ∀ v w, v ≤ w → bound v ≤ bound w) :
    IConfluent (S := SchemaState) (SchemaWF bound) := by
  intro x y hx hy n hn
  have hn' : (x.2 n || y.2 n) = true := hn
  show n ≤ bound (Nat.max x.1 y.1)
  cases (Bool.or_eq_true _ _).mp hn' with
  | inl h => exact Nat.le_trans (hx n h) (hmono _ _ (Nat.le_max_left _ _))
  | inr h => exact Nat.le_trans (hy n h) (hmono _ _ (Nat.le_max_right _ _))

/-- The dead end, concrete: the original candidate policy — version 0 bounded
by 10, version 1 by 20, `bound v = 10 * (v + 1)` — is globally free. A seam
verdict for it would be claiming coordination where none is needed. -/
theorem widening_needs_no_seam :
    IConfluent (S := SchemaState) (SchemaWF (fun v => 10 * (v + 1))) :=
  schema_widening_iconfluent _ (fun v w h => by
    show 10 * (v + 1) ≤ 10 * (w + 1)
    omega)

/-- The tightening migration policy: version 0 admits records up to 20,
version 1 tightens the bound to 10 — the new schema deprecates large values.
The non-monotone step is where the flag day lives. -/
def tightBound : Nat → Nat := fun v => if v = 0 then 20 else 10

/-- ⚠ **A tightening migration is NOT I-confluent — two versions merge into
incoherence.** A version-0 replica legally holds a record of 20; a version-1
replica legally holds a record of 10; their merge is a version-1 store
containing 20 — well-formed nowhere. Neither replica did anything wrong: the
old data is legal under the old schema, and gossip carried it into the new one.
This is the proof-shaped reason a tightening migration cannot be deployed by
rolling upgrade: version-0 writers must be stopped and their data migrated
*before* the bump is visible — a flag day. -/
theorem schema_tightening_not_iconfluent :
    ¬ IConfluent (S := SchemaState) (SchemaWF tightBound) := by
  intro h
  have hmerge := h (0, fun n => n == 20) (1, fun n => n == 10)
    (fun n hn => by simp at hn; subst hn; decide)
    (fun n hn => by simp at hn; subst hn; decide)
  exact absurd (hmerge 20 (by decide)) (by decide)

/-- **Within a version, the store merges freely** — `SchemaWF` is segmented
over σ = the version, for EVERY migration policy: same-version replicas share a
bound, unions of individually-legal records stay legal, and `max` of equal
versions cannot bump the schema. So the coordination a tightening migration
needs is confined to the version crossing: freeze σ, migrate, bump — the
*contract* half of expand/contract, with the flag day now a theorem-shaped
boundary instead of an operational superstition. (That the seam proof is
uniform in `bound` while only non-monotone `bound`s clash is the point:
segmentation says where coordination CAN be confined; the clash says whether
any is needed.) -/
theorem schema_segmented (bound : Nat → Nat) :
    SegmentedIConfluent (S := SchemaState) Prod.fst (SchemaWF bound) := by
  intro x y hσ hx hy
  have hmax : Nat.max x.1 y.1 = x.1 := by rw [hσ, nat_max_def]; simp
  refine ⟨?_, ?_⟩
  · intro n hn
    have hn' : (x.2 n || y.2 n) = true := hn
    show n ≤ bound (Nat.max x.1 y.1)
    rw [hmax]
    cases (Bool.or_eq_true _ _).mp hn' with
    | inl h => exact hx n h
    | inr h => rw [hσ]; exact hy n h
  · show Nat.max x.1 y.1 = x.1
    exact hmax

/-! ## §3. The seam row of the DSL — three inhabitants -/

/-- **The epoch seam, packaged**: the duelling-admins clash of
`epoch_sole_not_iconfluent` (Alice-forever at epoch 1 vs Bob's arbitrated
epoch 2) plus the seam of `epoch_segmented`. Reading: admin operations never
wait inside an epoch; replicas coordinate exactly to cross an epoch boundary,
and the crossing carries the arbitration verdict. -/
def epochSegVerdict : SegVerdict (EpochSole demoArb) Nat where
  σ := Prod.fst
  seamFree := epoch_segmented demoArb
  x := (1, fun _ a => a == 1)
  y := (2, fun e a => e == 2 && a == 2)
  hx := fun a ha => by simp at ha; exact ha
  hy := fun a ha => by simp at ha; exact ha
  hbad := fun hgood => absurd (hgood 1 (by decide)) (by decide)

/-- **The schema seam, packaged**: the tightening-migration clash of
`schema_tightening_not_iconfluent` (a legal version-0 record of 20 poisoning a
version-1 store) plus the seam of `schema_segmented`. Reading: same-version
replicas gossip freely; the version bump is the flag day. -/
def schemaSegVerdict : SegVerdict (SchemaWF tightBound) Nat where
  σ := Prod.fst
  seamFree := schema_segmented tightBound
  x := (0, fun n => n == 20)
  y := (1, fun n => n == 10)
  hx := fun n hn => by simp at hn; subst hn; decide
  hy := fun n hn => by simp at hn; subst hn; decide
  hbad := fun hgood => absurd (hgood 20 (by decide)) (by decide)

/-- The seam row, evaluated side by side: budget (`Spec.budgetSegVerdict`),
epoch, schema — each demotes to an honest clash for a binary consumer. -/
example :
    (budgetSegVerdict.toClash.isFree,
     epochSegVerdict.toClash.isFree,
     schemaSegVerdict.toClash.isFree) = (false, false, false) := rfl

/-- Escalation reading, recovered from the packaged witnesses. -/
example : ¬ IConfluent (EpochSole demoArb) := epochSegVerdict.escalatesGlobally
example : ¬ IConfluent (SchemaWF tightBound) := schemaSegVerdict.escalatesGlobally

/-- Free-running reading: same-epoch replicas sync safely — admin operations
never wait between coordination events. -/
example (a b : EpochState) (hσ : a.1 = b.1)
    (ha : EpochSole demoArb a) (hb : EpochSole demoArb b) :
    EpochSole demoArb (a ⊔ b) :=
  epochSegVerdict.freeWithinSeam hσ ha hb

/-- Closure reading: a same-version sync cannot bump the schema behind your
back — the flag day can never happen by accident. -/
example (a b : SchemaState) (hσ : a.1 = b.1)
    (ha : SchemaWF tightBound a) (hb : SchemaWF tightBound b) :
    (a ⊔ b).1 = a.1 :=
  schemaSegVerdict.staysInSeam hσ ha hb

end Uwueave.Seams
