/-
# Uwueave.BoundedEraAnnouncement -- exhaustive certificates for a finite ERA cut pool

`EraCertificate.Announcement` is intentionally unbounded: the arbiter may add a
fresh cut not named by any replica-local inventory.  This module does not erase
that fact.  Instead it defines `AnnouncementWithin available`, exhaustively
materialises the finite cut/delivery choice space, and decides stability of the
canonical final execution trace over exactly that space.

The trace classifier is exact at trace level.  Equal final traces imply equal
`finalView`s, so acceptance is sound for bounded announcements.  The converse
is not claimed at view level: distinct no-op traces can materialise the same
function-valued view.  `no_finite_pool_covers_unrestricted` closes the other
direction honestly by constructing a fresh cut outside every finite pool.

The finite pool is caller-supplied data.  Nothing here proves deployment-pool
completeness, authenticates an announcement, persists a pool, or licenses
stability under unrestricted future announcements.
-/
import Uwueave.EraCertificate

namespace Uwueave.BoundedEraAnnouncement

open Uwueave.EraCertificate

/-! ## 1. The bounded future -/

/-- An ERA announcement whose complete cut set stays inside the base cut set
plus the caller-supplied finite pool.  Delivery may still advance within the
world's already finite event pool, exactly as in `Announcement`. -/
def AnnouncementWithin (available : List Era.Cut) (w t : EraWorld) : Prop :=
  Announcement w t ∧
    ∀ c ∈ t.cuts, c ∈ w.cuts ∨ c ∈ available

theorem announcementWithin_is_announcement {available : List Era.Cut}
    {w t : EraWorld} (h : AnnouncementWithin available w t) :
    Announcement w t :=
  h.1

/-! ## 2. Canonical finite choices and materialisation -/

/-- All list subsets, in stable include/exclude order.  We apply this only to
duplicate-free canonical pools, so each extensional subset has one choice. -/
def subsets {alpha : Type} : List alpha → List (List alpha)
  | [] => [[]]
  | x :: xs =>
      let rest := subsets xs
      rest ++ rest.map (x :: ·)

theorem filter_mem_subsets {alpha : Type} (p : alpha → Bool) :
    ∀ xs : List alpha, xs.filter p ∈ subsets xs := by
  intro xs
  induction xs with
  | nil => simp [subsets]
  | cons x xs ih =>
      cases hp : p x <;> simp [subsets, hp, ih]

theorem mem_of_mem_subsets {alpha : Type} {choice source : List alpha}
    (h : choice ∈ subsets source) : ∀ x ∈ choice, x ∈ source := by
  induction source generalizing choice with
  | nil =>
      simp [subsets] at h
      subst choice
      simp
  | cons a source ih =>
      simp only [subsets, List.mem_append, List.mem_map] at h
      rcases h with h | ⟨tail, htail, rfl⟩
      · intro x hx
        exact List.Mem.tail a (ih h x hx)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.Mem.head source
        · exact List.Mem.tail a (ih htail x hx)

/-- The power-set generator has its advertised exact cardinality. -/
theorem length_subsets {alpha : Type} : ∀ xs : List alpha,
    (subsets xs).length = 2 ^ xs.length := by
  intro xs
  induction xs with
  | nil => simp [subsets]
  | cons x xs ih =>
      simp only [subsets, List.length_append, List.length_map, ih,
        List.length_cons, Nat.pow_succ]
      omega

/-- Deterministic Cartesian product, preserving the order of both inputs. -/
def cross {alpha beta : Type} (xs : List alpha) (ys : List beta) :
    List (alpha × beta) := match xs with
  | [] => []
  | x :: rest => ys.map (x, ·) ++ cross rest ys

theorem mem_cross_iff {alpha beta : Type} (xs : List alpha) (ys : List beta)
    (x : alpha) (y : beta) :
    (x, y) ∈ cross xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  induction xs with
  | nil => simp [cross]
  | cons head tail ih =>
      simp only [cross, List.mem_append, List.mem_map, List.mem_cons, ih]
      constructor
      · rintro (⟨candidate, hc, hp⟩ | htail)
        · cases hp
          exact ⟨Or.inl rfl, hc⟩
        · exact ⟨Or.inr htail.1, htail.2⟩
      · rintro ⟨rfl | htail, hy⟩
        · exact Or.inl ⟨y, hy, rfl⟩
        · exact Or.inr ⟨htail, hy⟩

theorem length_cross {alpha beta : Type} (xs : List alpha) (ys : List beta) :
    (cross xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [cross]
  | cons x xs ih =>
      simp only [cross, List.length_append, List.length_map, ih,
        List.length_cons, Nat.add_mul]
      omega

/-- Duplicate-free cut candidates; first occurrence order is retained. -/
def canonicalCuts (available : List Era.Cut) : List Era.Cut :=
  available.eraseDups

/-- Duplicate-free delivery candidates from the world's issued event pool. -/
def canonicalEvents (w : EraWorld) : List Era.Event :=
  w.pool.eraseDups

/-- One bounded choice: newly visible cuts and delivered pool events. -/
abbrev Choice := List Era.Cut × List Era.Event

/-- Every canonical cut subset crossed with every canonical delivery subset. -/
def choices (available : List Era.Cut) (w : EraWorld) : List Choice :=
  cross (subsets (canonicalCuts available)) (subsets (canonicalEvents w))

/-- Materialise one choice monotonically over the base world.  Appending may
redeliver an event; ERA's set semantics makes that intentionally harmless. -/
def materialize (w : EraWorld) (choice : Choice) : EraWorld :=
  { cuts := w.cuts ++ choice.1
    log := w.log ++ choice.2
    pool := w.pool }

/-- Every canonical choice materialises a legal bounded announcement at a
wellformed base world. -/
theorem materialize_announcementWithin {available : List Era.Cut}
    {w : EraWorld} (hwf : Wf w) {choice : Choice}
    (hchoice : choice ∈ choices available w) :
    AnnouncementWithin available w (materialize w choice) := by
  have hcandidates : choice.1 ∈ subsets (canonicalCuts available) :=
    (mem_cross_iff _ _ _ _).mp hchoice |>.1
  have hevents : choice.2 ∈ subsets (canonicalEvents w) :=
    (mem_cross_iff _ _ _ _).mp hchoice |>.2
  have hcuts : ∀ c ∈ choice.1, c ∈ available := by
    intro c hc
    have := mem_of_mem_subsets hcandidates c hc
    simpa [canonicalCuts] using this
  have hpool : ∀ e ∈ choice.2, e ∈ w.pool := by
    intro e he
    have := mem_of_mem_subsets hevents e he
    simpa [canonicalEvents] using this
  constructor
  · refine ⟨?_, fun _ => Iff.rfl, ?_, ?_⟩
    · intro c hc
      exact List.mem_append.mpr (Or.inl hc)
    · intro e he
      exact List.mem_append.mpr (Or.inl he)
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hwf e he
      · exact hpool e he
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr (hcuts c hc)

/-- Select exactly the candidate cuts and pool events present in a target. -/
def choiceOf (available : List Era.Cut) (w t : EraWorld) : Choice :=
  (canonicalCuts available |>.filter fun c => decide (c ∈ t.cuts),
   canonicalEvents w |>.filter fun e => decide (e ∈ t.log))

theorem choiceOf_mem_choices (available : List Era.Cut) (w t : EraWorld) :
    choiceOf available w t ∈ choices available w := by
  apply (mem_cross_iff _ _ _ _).mpr
  exact ⟨filter_mem_subsets _ _, filter_mem_subsets _ _⟩

/-- The selected materialisation has exactly the target cut and log sets for
every bounded target. -/
theorem materialize_choiceOf_same_sets {available : List Era.Cut}
    {w t : EraWorld} (h : AnnouncementWithin available w t) :
    (∀ c, c ∈ (materialize w (choiceOf available w t)).cuts ↔ c ∈ t.cuts) ∧
      (∀ e, e ∈ (materialize w (choiceOf available w t)).log ↔ e ∈ t.log) := by
  constructor
  · intro c
    constructor
    · intro hc
      rcases List.mem_append.mp hc with hc | hc
      · exact h.1.1 c hc
      · exact (List.mem_filter.mp hc).2 |> of_decide_eq_true
    · intro hc
      rcases h.2 c hc with hcbase | hcavailable
      · exact List.mem_append.mpr (Or.inl hcbase)
      · apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_filter.mpr
        exact ⟨(by simpa [canonicalCuts] using hcavailable), decide_eq_true hc⟩
  · intro e
    constructor
    · intro he
      rcases List.mem_append.mp he with he | he
      · exact h.1.2.2.1 e he
      · exact (List.mem_filter.mp he).2 |> of_decide_eq_true
    · intro he
      have hepool : e ∈ w.pool := h.1.2.2.2 e he
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_filter.mpr
      exact ⟨(by simpa [canonicalEvents] using hepool), decide_eq_true he⟩

/-! ## 3. Exact trace classification and final-view soundness -/

/-- The canonical finalised execution trace consumed by `Era.resolveFinal`. -/
def finalTrace (w : EraWorld) : List Era.Event :=
  Era.execOrder w.cuts (w.log.filter (Era.finalized w.cuts))

theorem finalView_eq_fold_finalTrace (w : EraWorld) :
    finalView w = (finalTrace w).foldl Era.applyEvent Era.initView := by
  rfl

/-- Trace stability over every materialised choice, as a proposition. -/
def TraceStable (available : List Era.Cut) (w : EraWorld) : Prop :=
  ∀ choice ∈ choices available w,
    finalTrace (materialize w choice) = finalTrace w

/-- Executable exhaustive trace classifier. -/
def traceStableB (available : List Era.Cut) (w : EraWorld) : Bool :=
  (choices available w).all fun choice =>
    finalTrace (materialize w choice) == finalTrace w

/-- **Exactness at trace level.** The classifier returns true iff every
canonical materialised future has exactly the base final trace. -/
theorem traceStableB_eq_true_iff (available : List Era.Cut) (w : EraWorld) :
    traceStableB available w = true ↔ TraceStable available w := by
  simp [traceStableB, TraceStable, beq_iff_eq]

/-- Set-equivalent bounded targets have the same final trace as their selected
canonical materialisation. -/
theorem finalTrace_choiceOf_eq {available : List Era.Cut} {w t : EraWorld}
    (h : AnnouncementWithin available w t) :
    finalTrace (materialize w (choiceOf available w t)) = finalTrace t := by
  obtain ⟨hcuts, hlog⟩ := materialize_choiceOf_same_sets h
  unfold finalTrace
  apply Era.execOrder_same_sets hcuts
  intro e
  simp only [List.mem_filter]
  rw [hlog e, EraCertificate.finalized_congr hcuts e]

/-- **Bounded final-view soundness.** A true trace certificate freezes the full
`finalView` for every `AnnouncementWithin` target.  This does not quantify over
unrestricted `Announcement`. -/
theorem traceStableB_finalView_sound {available : List Era.Cut} {w : EraWorld}
    (haccept : traceStableB available w = true) {t : EraWorld}
    (ht : AnnouncementWithin available w t) :
    finalView t = finalView w := by
  have hstable := (traceStableB_eq_true_iff available w).mp haccept
  have hchoice := hstable (choiceOf available w t)
    (choiceOf_mem_choices available w t)
  have htrace : finalTrace t = finalTrace w := by
    rw [← finalTrace_choiceOf_eq ht, hchoice]
  rw [finalView_eq_fold_finalTrace, finalView_eq_fold_finalTrace, htrace]

/-- Certificate-shaped spelling of `traceStableB_finalView_sound`: acceptance
is free termination of `finalView` for the bounded relation and only that
relation. -/
theorem traceStableB_finalView {available : List Era.Cut} {w : EraWorld}
    (haccept : traceStableB available w = true) :
    Evidence.FreeTermination (AnnouncementWithin available) finalView w :=
  fun _ ht => traceStableB_finalView_sound haccept ht

/-- At a wellformed base, canonical materialisations are themselves bounded
futures, so trace acceptance is iff trace stability over all bounded targets. -/
theorem traceStableB_iff_all_bounded_traces {available : List Era.Cut}
    {w : EraWorld} (hwf : Wf w) :
    traceStableB available w = true ↔
      ∀ t, AnnouncementWithin available w t → finalTrace t = finalTrace w := by
  rw [traceStableB_eq_true_iff]
  constructor
  · intro h t ht
    rw [← finalTrace_choiceOf_eq ht]
    exact h _ (choiceOf_mem_choices available w t)
  · intro h choice hchoice
    exact h _ (materialize_announcementWithin hwf hchoice)

/-- **Exact bounded certificate theorem.** At a wellformed base, Boolean trace
acceptance is iff free termination of the canonical final trace under the
explicitly bounded announcement relation. -/
theorem traceStableB_iff_freeTermination {available : List Era.Cut}
    {w : EraWorld} (hwf : Wf w) :
    traceStableB available w = true ↔
      Evidence.FreeTermination (AnnouncementWithin available) finalTrace w :=
  traceStableB_iff_all_bounded_traces hwf

/-! ## 4. Explicit exponential cost -/

/-- Number of candidate trace comparisons, excluding the one base trace reused
by all comparisons. -/
def traceCount (available : List Era.Cut) (w : EraWorld) : Nat :=
  (choices available w).length

/-- **Exact candidate-space count.** With `c` distinct supplied cuts and `e`
distinct issued events, the classifier has `2^c * 2^e` materialised traces
(plus one reusable base trace).  An accepting run examines them all; a refusing
run may short-circuit.  Thus the worst-case outer enumeration is
`O(2^(c+e))`; this theorem deliberately exposes, rather than hides, that cost. -/
theorem traceCount_eq (available : List Era.Cut) (w : EraWorld) :
    traceCount available w =
      2 ^ (canonicalCuts available).length *
        2 ^ (canonicalEvents w).length := by
  simp [traceCount, choices, length_cross, length_subsets]

/-! ## 5. No finite cut pool covers the unrestricted future -/

/-- Maximum event-id coordinate in a finite cut list. -/
def maxCutEventId : List Era.Cut → Nat
  | [] => 0
  | cut :: cuts => Nat.max cut.2 (maxCutEventId cuts)

theorem second_le_maxCutEventId {cut : Era.Cut} {cuts : List Era.Cut}
    (h : cut ∈ cuts) : cut.2 ≤ maxCutEventId cuts := by
  induction cuts with
  | nil => simp at h
  | cons head cuts ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- A cut whose event-id coordinate is fresh for both the base and supplied
finite pool.  Epoch zero is immaterial; freshness is carried by the second
coordinate. -/
def freshCut (w : EraWorld) (available : List Era.Cut) : Era.Cut :=
  (0, maxCutEventId (w.cuts ++ available) + 1)

theorem freshCut_not_mem_base_or_available (w : EraWorld)
    (available : List Era.Cut) :
    freshCut w available ∉ w.cuts ∧ freshCut w available ∉ available := by
  have hfresh : freshCut w available ∉ w.cuts ++ available := by
    intro hmem
    have hle := second_le_maxCutEventId hmem
    simp [freshCut] at hle
    omega
  simpa [List.mem_append] using hfresh

/-- The unrestricted target obtained by appending the fresh cut and doing no
delivery. -/
def freshAnnouncement (w : EraWorld) (available : List Era.Cut) : EraWorld :=
  { w with cuts := w.cuts ++ [freshCut w available] }

theorem freshAnnouncement_is_announcement {w : EraWorld} (hwf : Wf w)
    (available : List Era.Cut) :
    Announcement w (freshAnnouncement w available) := by
  refine ⟨?_, fun _ => Iff.rfl, fun _ h => h, hwf⟩
  intro c hc
  exact List.mem_append.mpr (Or.inl hc)

/-- A finite pool covers the unrestricted axis only if every unrestricted
announcement also satisfies its finite cut bound. -/
def CoversUnrestricted (available : List Era.Cut) (w : EraWorld) : Prop :=
  ∀ t, Announcement w t → AnnouncementWithin available w t

/-- **Fresh-cut obstruction.** No finite cut pool covers ERA's unrestricted
announcement future.  This is why the bounded certificate above cannot be
promoted to unrestricted future closure without a separately proved external
coverage/sealing premise. -/
theorem no_finite_pool_covers_unrestricted {w : EraWorld} (hwf : Wf w)
    (available : List Era.Cut) :
    ¬ CoversUnrestricted available w := by
  intro hcover
  have hwithin := hcover (freshAnnouncement w available)
    (freshAnnouncement_is_announcement hwf available)
  have hmem : freshCut w available ∈
      (freshAnnouncement w available).cuts := by
    apply List.mem_append.mpr
    exact Or.inr (List.Mem.head [])
  rcases hwithin.2 _ hmem with hbase | havailable
  · exact (freshCut_not_mem_base_or_available w available).1 hbase
  · exact (freshCut_not_mem_base_or_available w available).2 havailable

end Uwueave.BoundedEraAnnouncement
