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

Between them sits the **concrete clock kit** (§2): the two-replica clock
`Nat × Nat` that `MVRegister` and `Undo` tag writes with, one shared
definition of "dominates" (`Clock.lt` — exactly `MVRegister.Dom`'s content)
and "concurrent" (`Clock.Concurrent`), decidable, with the small algebra
everyone re-derives — and the bridge theorems (`Clock.le_iff_toVClock` and
friends) certifying the kit against the abstract vector-clock order of §1
under the evident encoding. One vocabulary, not three encodings.

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

/-! ## §2. The concrete two-replica clock kit

Downstream files (`MVRegister`, `Undo`) keep their vector clocks *concrete* —
`Nat × Nat`, one count per replica — so every story is decidable. This section
is the single vocabulary for that clock. It is not a parallel theory: the
bridge theorems at the end show `Clock.le`/`Clock.lt`/`Clock.Concurrent` are
*exactly* the §1 lattice order (and its strict/incomparable forms) under the
evident encoding into `VClock Bool`, so the kit is certified against
`vclock_leq_iff`'s world rather than sitting beside it. -/

/-- The concrete two-replica clock: one event count per replica. -/
abbrev Clock := Nat × Nat

namespace Clock

/-- Componentwise order: everything the write carrying `c` had seen, the write
carrying `c'` has also seen. -/
def le (c c' : Clock) : Prop := c.1 ≤ c'.1 ∧ c.2 ≤ c'.2

/-- Strict domination: componentwise `≤` and not equal — `c'` has seen
strictly more than `c`. This is exactly the content of `MVRegister.Dom`,
which is an abbreviation for it. -/
def lt (c c' : Clock) : Prop := c.1 ≤ c'.1 ∧ c.2 ≤ c'.2 ∧ c ≠ c'

/-- Concurrent clocks: incomparable — neither has seen everything the other
has. Symmetric (`concurrent_symm`); never relates a clock to itself, since
concurrent clocks are distinct (`concurrent_ne`). -/
def Concurrent (c c' : Clock) : Prop := ¬ le c c' ∧ ¬ le c' c

instance (c c' : Clock) : Decidable (le c c') := by
  unfold le; infer_instance

instance (c c' : Clock) : Decidable (lt c c') := by
  unfold lt; infer_instance

instance (c c' : Clock) : Decidable (Concurrent c c') := by
  unfold Concurrent; infer_instance

/-- `lt` is `le` plus distinctness — the repackaging proofs reach for. -/
theorem lt_iff_le_ne {c c' : Clock} : lt c c' ↔ (le c c' ∧ c ≠ c') :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

theorem le_refl (c : Clock) : le c c := ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem le_trans {c₁ c₂ c₃ : Clock} (h : le c₁ c₂) (h' : le c₂ c₃) :
    le c₁ c₃ := ⟨Nat.le_trans h.1 h'.1, Nat.le_trans h.2 h'.2⟩

theorem le_antisymm {c c' : Clock} (h : le c c') (h' : le c' c) : c = c' := by
  have h1 : c.1 = c'.1 := Nat.le_antisymm h.1 h'.1
  have h2 : c.2 = c'.2 := Nat.le_antisymm h.2 h'.2
  cases c; cases c'; simp_all

/-- No clock strictly dominates itself. -/
theorem lt_irrefl (c : Clock) : ¬ lt c c := fun h => h.2.2 rfl

/-- Two writes cannot each strictly dominate the other. -/
theorem lt_asymm {c c' : Clock} (h : lt c c') : ¬ lt c' c := fun h' =>
  h.2.2 (le_antisymm ⟨h.1, h.2.1⟩ ⟨h'.1, h'.2.1⟩)

/-- Supersession chains: strict domination is transitive. -/
theorem lt_trans {c₁ c₂ c₃ : Clock} (h : lt c₁ c₂) (h' : lt c₂ c₃) :
    lt c₁ c₃ := by
  refine ⟨Nat.le_trans h.1 h'.1, Nat.le_trans h.2.1 h'.2.1, fun heq => ?_⟩
  subst heq
  exact lt_asymm h h'

/-- "Incomparable" has no direction. -/
theorem concurrent_symm {c c' : Clock} (h : Concurrent c c') :
    Concurrent c' c := ⟨h.2, h.1⟩

/-- Concurrent clocks are distinct (`le` is reflexive). -/
theorem concurrent_ne {c c' : Clock} (h : Concurrent c c') : c ≠ c' :=
  fun heq => h.1 (heq ▸ le_refl c)

/-! ### The bridge — the kit is §1's order, not a lookalike -/

/-- The evident encoding of a concrete clock as a `Bool`-indexed vector
clock: replica `true` holds the first count, replica `false` the second. -/
def toVClock (c : Clock) : VClock Bool := fun b => cond b c.1 c.2

/-- The encoding is injective — no two concrete clocks collapse. -/
theorem toVClock_inj {c c' : Clock} (h : toVClock c = toVClock c') : c = c' := by
  have h1 : c.1 = c'.1 := congrFun h true
  have h2 : c.2 = c'.2 := congrFun h false
  cases c; cases c'; simp_all

/-- **The bridge for `le`.** The concrete componentwise order is exactly the
lattice order `⊑` of the abstract vector-clock world under `toVClock` — by
`vclock_leq_iff`, which equates `⊑` with the pointwise test the two
components spell out. -/
theorem le_iff_toVClock {c c' : Clock} :
    le c c' ↔ toVClock c ⊑ toVClock c' := by
  rw [vclock_leq_iff]
  constructor
  · intro h b
    cases b
    · exact h.2
    · exact h.1
  · intro h
    exact ⟨h true, h false⟩

/-- **The bridge for `lt`**: strict domination is the strict lattice order —
`⊑` plus distinctness, carried across the injective encoding. -/
theorem lt_iff_toVClock {c c' : Clock} :
    lt c c' ↔ (toVClock c ⊑ toVClock c' ∧ toVClock c ≠ toVClock c') := by
  rw [lt_iff_le_ne, le_iff_toVClock]
  constructor
  · exact fun h => ⟨h.1, fun heq => h.2 (toVClock_inj heq)⟩
  · exact fun h => ⟨h.1, fun heq => h.2 (congrArg toVClock heq)⟩

/-- **The bridge for `Concurrent`**: concrete concurrency is §1's
`Concurrent` on the encoded clocks — "concurrent" means one thing. -/
theorem concurrent_iff_toVClock {c c' : Clock} :
    Concurrent c c' ↔
      Uwueave.Causality.Concurrent (toVClock c) (toVClock c') :=
  ⟨fun h => ⟨fun hle => h.1 (le_iff_toVClock.mpr hle),
             fun hle => h.2 (le_iff_toVClock.mpr hle)⟩,
   fun h => ⟨fun hle => h.1 (le_iff_toVClock.mp hle),
             fun hle => h.2 (le_iff_toVClock.mp hle)⟩⟩

end Clock

/-! ## §3. Fork evidence -/

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
