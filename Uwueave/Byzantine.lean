/-
# Uwueave.Byzantine — equivocation, forgery, and withholding.

The ordinary delivery model asks when already-issued information reaches every
replica.  A Byzantine producer has three strictly larger powers:

* **equivocate** — issue two different ids for one `(author, sequence)` slot;
* **forge** — cause a replica to accept an artifact under somebody else's
  author, grant, or already-announced event id;
* **withhold** — keep an issued artifact out of a recipient's delivered log.

This file keeps those powers separate.  In particular, eventual delivery is
not an authenticity theorem, and authenticity is not a liveness theorem.

There are three connections to the existing development.

1. `Causality.ForkEvidence` is reused exactly.  Once both branches are
   admitted, evidence is permanent under every gossip extension and
   I-confluent under merge.  Attribution, however, additionally assumes that
   admitted `(author, sequence, id)` records really were issued by that
   author.  Without that premise, a forger can frame an honest peer.
2. `Gated.gatedOps` proves authorization of a cited grant, not authenticity of
   the submitter.  A concrete Mallory submission citing Alice's live root grant
   passes the gate, because submitter identity is deliberately absent from
   `Gated.GOp`.
3. `EraCertificate`'s issuance counterexample is closed by two explicit
   authenticity premises: announcements name ids already present in the issued
   pool, and an id binds at most one event payload.  Under those premises a
   settled ERA view is stable across issuance.  The existing forged-id witness
   violates collision freedom and reverses the finalised verdict.

No cryptography is proved here.  `SignatureAuthentic`, `IdAuthentic`, and
`AnnouncementsGrounded` are the exact handoff points to a signature/hash-DAG
implementation.  The delivery predicates remain independent obligations.
-/
import Uwueave.Causality
import Uwueave.Gated
import Uwueave.EraCertificate

namespace Uwueave.Byzantine

open Uwueave Uwueave.Catalog

/-! ## §1. Equivocation evidence under gossip -/

/-- The admitted observation set is exactly Causality's grow-only carrier. -/
abbrev Observation := Causality.EntrySet

/-- A gossip step only adds admitted observations.  This is deliberately a
delivery relation: it says nothing about who really authored an observation. -/
def Gossip (before after : Observation) : Prop :=
  ∀ e, before e = true → after e = true

theorem gossip_refl (B : Observation) : Gossip B B :=
  fun _ h => h

theorem gossip_trans {A B C : Observation} (hAB : Gossip A B)
    (hBC : Gossip B C) : Gossip A C :=
  fun e he => hBC e (hAB e he)

theorem gossip_left (A B : Observation) : Gossip A (A ⊔ B) := by
  intro e he
  show (A e || B e) = true
  simp [he]

theorem gossip_right (A B : Observation) : Gossip B (A ⊔ B) := by
  intro e he
  show (A e || B e) = true
  simp [he]

/-- **Permanent fork evidence.** Once a replica has both branches, every
gossip extension still has the same proof.  Withholding can delay assembly of
the proof, but no later gossip can erase it. -/
theorem fork_evidence_permanent {B B' : Observation} {p : Nat}
    (hg : Gossip B B') (hf : Causality.ForkEvidence B p) :
    Causality.ForkEvidence B' p := by
  obtain ⟨s, i₁, i₂, hne, h₁, h₂⟩ := hf
  exact ⟨s, i₁, i₂, hne, hg _ h₁, hg _ h₂⟩

/-- The merge-shaped statement is Causality's existing theorem, not a second
equivocation calculus. -/
theorem fork_evidence_iconfluent (p : Nat) :
    IConfluent (S := Observation) (fun B => Causality.ForkEvidence B p) :=
  Causality.fork_evidence_iconfluent p

/-- What an external verifier says was genuinely issued by each author. -/
abbrev IssuedBy := Nat → Nat → Nat → Prop

/-- The signature handoff: every admitted triple is attributable to its
claimed author.  This is independent of whether it is ever delivered. -/
def SignatureAuthentic (B : Observation) (issued : IssuedBy) : Prop :=
  ∀ p s i, B (p, s, i) = true → issued p s i

/-- Actual equivocation by author `p`, stated against the external issuance
relation rather than against an unauthenticated receive buffer. -/
def Equivocated (issued : IssuedBy) (p : Nat) : Prop :=
  ∃ s i₁ i₂, i₁ ≠ i₂ ∧ issued p s i₁ ∧ issued p s i₂

/-- Fork evidence attributes blame exactly when admitted authorship is
authentic. -/
theorem fork_evidence_attributes_author {B : Observation} {issued : IssuedBy}
    {p : Nat} (ha : SignatureAuthentic B issued)
    (hf : Causality.ForkEvidence B p) : Equivocated issued p := by
  obtain ⟨s, i₁, i₂, hne, h₁, h₂⟩ := hf
  exact ⟨s, i₁, i₂, hne, ha p s i₁ h₁, ha p s i₂ h₂⟩

/-! ### A concrete equivocator, and a concrete framing attack -/

def leftBranch : Observation := fun e => e == (17, 4, 101)
def rightBranch : Observation := fun e => e == (17, 4, 102)
def forkedGossip : Observation := leftBranch ⊔ rightBranch

theorem left_branch_alone_is_not_evidence :
    ¬ Causality.ForkEvidence leftBranch 17 := by
  rintro ⟨s, i₁, i₂, hne, h₁, h₂⟩
  simp [leftBranch] at h₁ h₂
  exact hne (h₁.2.trans h₂.2.symm)

theorem right_branch_alone_is_not_evidence :
    ¬ Causality.ForkEvidence rightBranch 17 := by
  rintro ⟨s, i₁, i₂, hne, h₁, h₂⟩
  simp [rightBranch] at h₁ h₂
  exact hne (h₁.2.trans h₂.2.symm)

theorem concrete_equivocation_assembles_under_gossip :
    Gossip leftBranch forkedGossip
      ∧ Gossip rightBranch forkedGossip
      ∧ Causality.ForkEvidence forkedGossip 17 := by
  refine ⟨gossip_left _ _, gossip_right _ _, 4, 101, 102, by decide, ?_, ?_⟩
  · decide
  · decide

/-- In the framing world only the left branch was genuinely issued by peer 17;
the right branch was injected by a forger. -/
def honestIssuance : IssuedBy :=
  fun p s i => (p, s, i) = (17, 4, 101)

theorem honest_issuance_did_not_equivocate :
    ¬ Equivocated honestIssuance 17 := by
  rintro ⟨s, i₁, i₂, hne, h₁, h₂⟩
  simp [honestIssuance] at h₁ h₂
  exact hne (h₁.2.trans h₂.2.symm)

/-- **Authenticity is load-bearing.** The receive buffer contains perfectly
valid-shaped fork evidence, yet the claimed author did not equivocate.  The
missing signature premise is exhibited by the forged right branch. -/
theorem forged_branch_can_frame_without_authentication :
    Causality.ForkEvidence forkedGossip 17
      ∧ ¬ Equivocated honestIssuance 17
      ∧ ¬ SignatureAuthentic forkedGossip honestIssuance := by
  refine ⟨concrete_equivocation_assembles_under_gossip.2.2,
    honest_issuance_did_not_equivocate, ?_⟩
  intro h
  have hforged := h 17 4 102 (by decide)
  simp [honestIssuance] at hforged

/-! ## §2. The gated authorization seam -/

/-- The transport layer knows a submitter; `Gated.GOp` intentionally does not.
This wrapper makes the information lost at the gate explicit. -/
structure Submission where
  submitter : Nat
  op : Gated.GOp
  deriving DecidableEq, Repr

/-- A tiny external ownership policy for the witness: grant 1 belongs to
Alice.  A real deployment discharges this with signatures over the operation. -/
def CitationAuthentic (s : Submission) : Prop :=
  s.op.cite = 1 → s.submitter = Era.alice

/-- Mallory submits an operation citing Alice's root grant. -/
def mallorySubmission : Submission :=
  ⟨3, { t := 99, node := 7, dest := none, cite := 1 }⟩

/-- The gate sees the valid chain, no revocations, and the injected operation;
it has no submitter channel to inspect. -/
def malloryGateState : Gated.GatedState :=
  (Authority.demoChain,
    (Authority.noRevs, fun o => o == mallorySubmission.op))

/-- Authorization is not authentication: the citation is externally forged,
yet the operation passes `gatedOps` because the cited grant is active and its
scope covers node 7.  This is not a bug in the gate; it identifies the exact
signature premise the caller must supply. -/
theorem unauthenticated_submission_can_pass_the_gate :
    ¬ CitationAuthentic mallorySubmission
      ∧ Gated.gatedOps malloryGateState mallorySubmission.op := by
  refine ⟨?_, ?_⟩
  · intro h
    have hbad := h rfl
    simp [mallorySubmission, Era.alice] at hbad
  refine ⟨by decide, 0, 9, ?_, by decide⟩
  exact .root (by decide) (by decide)

/-! ## §3. Withholding is a delivery failure, not a forgery -/

open EraCertificate

/-- An issued event is being withheld from this replica at this snapshot. -/
def Withholds (w : EraWorld) (e : Era.Event) : Prop :=
  e ∈ w.pool ∧ e ∉ w.log

/-- Delivery completeness is exactly the absence of a withheld event. -/
theorem not_quiesced_iff_withheld {w : EraWorld} :
    ¬ Quiesced w ↔ ∃ e, Withholds w e := by
  constructor
  · intro hn
    apply Classical.byContradiction
    intro hnone
    apply hn
    intro e he
    apply Classical.byContradiction
    intro hnot
    exact hnone ⟨e, he, hnot⟩
  · rintro ⟨e, hepool, helog⟩ hq
    exact helog (hq e hepool)

/-- In the standard pre-delivery ERA world, Alice's demote is concretely
withheld.  It is issued but absent from this replica's log. -/
theorem concrete_withholding : Withholds wPre Era.e4 := by
  exact ⟨by decide, by decide⟩

/-! ## §4. Authentic announced ids -/

/-- An event id binds one payload throughout an issued pool.  This is the
abstract content-address/signature premise absent from the miniature ERA
carrier.  Duplicate deliveries of the same payload remain allowed. -/
def IdAuthentic (pool : List Era.Event) : Prop :=
  ∀ a ∈ pool, ∀ b ∈ pool, a.eid = b.eid → a = b

/-- Every announcement names an id already represented in the issued pool.
This excludes an arbiter pre-blessing a bare number that an attacker can later
populate. -/
def AnnouncementsGrounded (w : EraWorld) : Prop :=
  ∀ c ∈ w.cuts, ∃ e ∈ w.pool, e.eid = c.2

/-- The authenticity bundle is entirely orthogonal to delivery: it constrains
accepted names and payloads, not when the named payloads arrive. -/
def AuthenticAtCut (w : EraWorld) : Prop :=
  AnnouncementsGrounded w ∧ IdAuthentic w.pool

/-- A newly accepted event reuses an old event's already-finalised id for a
different payload.  This is the exact forgery performed by
`EraCertificate.eForged`. -/
def AnnouncedIdForgery (w t : EraWorld) : Prop :=
  ∃ forged ∈ t.pool, forged ∉ w.pool ∧
    ∃ original ∈ w.pool,
      forged.eid = original.eid ∧ forged ≠ original ∧
      Era.finalized w.cuts forged = true

/-- A finalised event has a corresponding announcement record. -/
theorem finalized_has_cut {cuts : List Era.Cut} {e : Era.Event}
    (hf : Era.finalized cuts e = true) :
    ∃ k, (k, e.eid) ∈ cuts := by
  obtain ⟨k, hk⟩ := epochOf_some_of_finalized hf
  exact ⟨k, Era.epochOf_some_mem hk⟩

/-- Under grounded announcements and id authenticity, issuance cannot smuggle
a new event directly into an already-finalised epoch.  `Issuance` remains a
separate hypothesis: authenticity does not promise that anything is sent. -/
theorem authentic_issuance_has_no_new_finalised_event {w t : EraWorld}
    (hs : Settled w) (hg : AnnouncementsGrounded w)
    (ha : IdAuthentic t.pool) (hi : Issuance w t)
    {e : Era.Event} (he : e ∈ t.log)
    (hf : Era.finalized t.cuts e = true) : e ∈ w.log := by
  have hfin : Era.finalized w.cuts e = true := by
    rw [finalized_congr (fun c => (hi.1 c).symm) e]
    exact hf
  obtain ⟨k, hk⟩ := finalized_has_cut hfin
  obtain ⟨original, hopool, hoid⟩ := hg (k, e.eid) hk
  have hotpool : original ∈ t.pool := hi.2.1 original hopool
  have hetpool : e ∈ t.pool := hi.2.2.2 e he
  have heq : e = original := ha e hetpool original hotpool hoid.symm
  rw [heq]
  exact hs original hopool (by simpa [heq] using hfin)

/-- **ERA safety with the authenticity premise stated.** A settled finalised
view is stable not only under delivery, but under issuance whose announced ids
are grounded and collision-free.  This is exactly the theorem falsified by an
event born finalised when ids are forgeable. -/
theorem authentic_issuance_preserves_finality {w t : EraWorld}
    (hs : Settled w) (hg : AnnouncementsGrounded w)
    (ha : IdAuthentic t.pool) (hi : Issuance w t) :
    finalView t = finalView w := by
  symm
  apply resolveFinal_congr (fun c => (hi.1 c).symm)
  intro e
  have hfin : Era.finalized w.cuts e = Era.finalized t.cuts e :=
    finalized_congr (fun c => (hi.1 c).symm) e
  constructor
  · rintro ⟨he, hf⟩
    exact ⟨hi.2.2.1 e he, by rw [← hfin]; exact hf⟩
  · rintro ⟨he, hf⟩
    have hwf : Era.finalized w.cuts e = true := by rw [hfin]; exact hf
    exact ⟨authentic_issuance_has_no_new_finalised_event hs hg ha hi he hf, hwf⟩

/-- Exact contrapositive: under a settled, grounded cut, any issuance that
changes ERA's finalised view is evidence that accepted ids were not authentic.
No delivery-fairness premise appears. -/
theorem finality_failure_refutes_id_authenticity {w t : EraWorld}
    (hs : Settled w) (hg : AnnouncementsGrounded w) (hi : Issuance w t)
    (hchange : finalView t ≠ finalView w) : ¬ IdAuthentic t.pool :=
  fun ha => hchange (authentic_issuance_preserves_finality hs hg ha hi)

/-- Any concrete reuse of an old id for a distinct newly accepted payload
refutes id authenticity. -/
theorem announced_id_forgery_refutes_authenticity {w t : EraWorld}
    (hi : Issuance w t) (hf : AnnouncedIdForgery w t) :
    ¬ IdAuthentic t.pool := by
  rintro ha
  obtain ⟨forged, hft, -, original, how, hid, hne, -⟩ := hf
  exact hne (ha forged hft original (hi.2.1 original how) hid)

/-! ### The concrete ERA forgery -/

theorem later_announcements_are_grounded :
    AnnouncementsGrounded wAheadAll := by
  intro c hc
  simp [wAheadAll, Era.laterCuts, Era.setupCuts, Era.advance] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨Era.e1, by decide, rfl⟩
  · exact ⟨Era.e2, by decide, rfl⟩
  · exact ⟨Era.e3, by decide, rfl⟩
  · exact ⟨Era.e5, by decide, rfl⟩

theorem concrete_announced_id_forgery :
    AnnouncedIdForgery wAheadAll wForged := by
  refine ⟨eForged, by decide, by decide, Era.e5, by decide, rfl, by decide, by decide⟩

/-- **The exact failure.** The cut set is unchanged and grounded, the starting
world is settled, and the transition is a valid ERA issuance.  One payload
forged under announced id 5 violates authenticity and reverses Alice's
finalised role.  Thus delivery liveness cannot repair an authenticity failure:
both endpoint worlds are already quiesced. -/
theorem forged_announced_id_breaks_era_finality :
    Settled wAheadAll
      ∧ Quiesced wAheadAll
      ∧ Quiesced wForged
      ∧ Issuance wAheadAll wForged
      ∧ AnnouncementsGrounded wAheadAll
      ∧ AnnouncedIdForgery wAheadAll wForged
      ∧ ¬ IdAuthentic wForged.pool
      ∧ (finalView wAheadAll).role Era.alice = Era.reader
      ∧ (finalView wForged).role Era.alice = Era.admin
      ∧ finalView wForged ≠ finalView wAheadAll := by
  have hid : ¬ IdAuthentic wForged.pool :=
    announced_id_forgery_refutes_authenticity issuance_wAheadAll_wForged
      concrete_announced_id_forgery
  refine ⟨settled_of_quiesced (by decide), by decide, by decide, issuance_wAheadAll_wForged,
    later_announcements_are_grounded, concrete_announced_id_forgery, hid,
    by decide, by decide, ?_⟩
  intro heq
  have hrole := congrArg (fun v => v.role Era.alice) heq
  exact absurd hrole (by decide)

/-! ## §5. Authenticity and delivery are independent obligations -/

/-- The ordinary pre-delivery world has unique, grounded ids even while it is
withholding events. -/
theorem pre_world_is_authentic : AuthenticAtCut wPre := by
  constructor
  · intro c hc
    simp [wPre, Era.setupCuts] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨Era.e1, by decide, rfl⟩
    · exact ⟨Era.e2, by decide, rfl⟩
    · exact ⟨Era.e3, by decide, rfl⟩
  · intro a ha b hb hid
    simp [wPre, Era.duelLog] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [Era.e1, Era.e2, Era.e3, Era.e4, Era.e5,
        Era.joinEv, Era.promoteEv, Era.demoteEv]

/-- **Separation theorem.** Authentic data can be withheld, and completely
delivered data can be forged.  Therefore a protocol needs both a cryptographic
admission premise and a delivery/fairness premise; neither subsumes the other. -/
theorem authenticity_and_delivery_are_independent :
    (AuthenticAtCut wPre ∧ ∃ e, Withholds wPre e)
      ∧ (Quiesced wForged ∧ ¬ AuthenticAtCut wForged) := by
  refine ⟨⟨pre_world_is_authentic, Era.e4, concrete_withholding⟩,
    by decide, ?_⟩
  intro h
  exact announced_id_forgery_refutes_authenticity issuance_wAheadAll_wForged
    concrete_announced_id_forgery h.2

end Uwueave.Byzantine
