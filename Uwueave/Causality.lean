/-
# Uwueave.Causality — vector clocks and fork evidence.

Two constructions a multiplayer weave needs around its merge:

  * **Vector clocks** — and the theorem that makes them trustworthy: the
    vector-clock order is *exactly* the lattice order of the merge
    (`vclock_leq_iff`), so "x happened-before y" is "merging x into y changes
    nothing", and sync (the join) is the *least* state above both replicas
    (`merge_le_iff` in `Confluence.lean`) — it can neither drop nor invent
    knowledge.

  * **Fork (equivocation) evidence** — the accountable-BFT primitive for
    multiplayer: a peer that presents two different blocks at the same
    (author, sequence) slot has forked, and the pair *is* the proof. The
    theorem worth having is that this evidence is a *monotone* fact of a
    grow-only set — hence I-confluent (`fork_evidence_iconfluent`): once any
    replica holds a fork proof, every future merge of every future state
    still holds it. Detection is permanent; a Byzantine peer cannot gossip
    its way back to innocence. (Almeida–Shapiro's blocklace §5 in miniature;
    Kleppmann's BFT-CRDT paper reaches the same architecture.)

The dual is also stated: evidence requires *both* branches
(`no_unilateral_evidence`) — an honest replica holding one block of a slot
frames nobody.
-/
import Uwueave.Catalog

namespace Uwueave.Causality

open Uwueave Uwueave.Catalog

/-! ## §1. Vector clocks -/

/-- A vector clock is a G-Counter read causally: per-replica event counts,
merged by pointwise max. Same carrier, different questions. -/
abbrev VClock (ι : Type) := GCounter ι

/-- **The vector-clock order is the lattice order.** `x ⊑ y` (merging `x`
into `y` is a no-op) holds iff every component of `x` is ≤ the corresponding
component of `y` — the textbook "x happened before or equals y" test. This is
the bridge between the algebra (`⊑`, defined from the merge alone) and the
operational reading (per-replica counters), and it is what licenses using
component comparison to answer causality questions about states. -/
theorem vclock_leq_iff {ι : Type} (x y : VClock ι) :
    x ⊑ y ↔ ∀ i, x i ≤ y i := by
  constructor
  · intro h i
    have hi : Nat.max (x i) (y i) = y i := congrFun h i
    rw [nat_max_def] at hi
    split at hi <;> omega
  · intro h
    funext i
    show Nat.max (x i) (y i) = y i
    rw [nat_max_def]
    split
    · rfl
    · have := h i; omega

/-- Two states are concurrent when neither subsumes the other. -/
def Concurrent {ι : Type} (x y : VClock ι) : Prop := ¬ x ⊑ y ∧ ¬ y ⊑ x

/-- Merging genuinely concurrent states produces something **strictly** above
both — progress is real, not a relabeling: the join equals neither input. -/
theorem concurrent_merge_strict {ι : Type} {x y : VClock ι}
    (h : Concurrent x y) : x ⊔ y ≠ x ∧ x ⊔ y ≠ y := by
  constructor
  · intro heq
    exact h.2 (heq ▸ le_merge_right x y)
  · intro heq
    exact h.1 (heq ▸ le_merge_left x y)

/-! ## §2. Fork evidence -/

/-- The observation set of a replica: (author, seq, block-id) triples it has
seen. Grow-only; in a content-addressed weave the block-id is the hash, and
"same (author, seq), different id" is a signed self-contradiction. -/
abbrev EntrySet := GSet (Nat × Nat × Nat)

/-- Fork evidence against author `p`: two *different* blocks at the same
sequence slot. The pair is the proof — no protocol run, no quorum, just two
signed artifacts that cannot both exist honestly. -/
def ForkEvidence (B : EntrySet) (p : Nat) : Prop :=
  ∃ s i₁ i₂, i₁ ≠ i₂ ∧ B (p, s, i₁) = true ∧ B (p, s, i₂) = true

/-- **Evidence is forever.** Fork evidence is upward-closed in the observation
set, hence I-confluent by `gset_monotone_iconfluent`: merges — any number, any
order, any partition schedule — preserve it. A forked peer's proof survives
all future gossip. This is the safety half of "Byzantine-repelling"; the
crypto half (ids bind content, signatures bind authors) is the usual explicit
premise, not a theorem here. -/
theorem fork_evidence_iconfluent (p : Nat) :
    IConfluent (S := EntrySet) (fun B => ForkEvidence B p) := by
  apply gset_monotone_iconfluent
  intro s t hsub ⟨sq, i₁, i₂, hne, h₁, h₂⟩
  exact ⟨sq, i₁, i₂, hne, hsub _ h₁, hsub _ h₂⟩

/-- **No unilateral framing.** A replica holding a single block at a slot
holds no evidence: `ForkEvidence` needs both branches. (So honest singletons
are safe, and evidence can only ever be *assembled* from the equivocator's own
signed blocks.) -/
theorem no_unilateral_evidence :
    ¬ ForkEvidence (fun e => e == (7, 0, 5)) 7 := by
  intro ⟨s, i₁, i₂, hne, h₁, h₂⟩
  simp at h₁ h₂
  omega

end Uwueave.Causality
