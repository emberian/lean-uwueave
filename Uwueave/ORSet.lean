/-
# Uwueave.ORSet — removable sets: observed-remove and causal-length.

The G-Set can only grow, and the 2P-Set can never re-add. The two standard
designs that give a *removable, re-addable* set are classified here:

  * the **OR-Set** (observed-remove, add-wins): every add carries a fresh tag;
    a remove tombstones exactly the tags it has *observed*. An add concurrent
    with a remove survives it — the remove could not have observed the new tag.
  * the **causal-length set** (Yu): membership is the *parity* of a per-element
    counter — odd = present. Add bumps even→odd, remove bumps odd→even; merge
    is pointwise max.

Both get their `MergeState` instances entirely from the lifts (a product of
G-Sets; a Pi of max-Nat) — zero new merge proofs, which is the composition
algebra doing its job. The theorems are about their *presence* invariants, and
they land on opposite sides in an instructive way:

  * OR-Set presence is **not** I-confluent (`orset_present_not_iconfluent`):
    two replicas can each hold the element alive through a different tag while
    tombstoning the other's — the merge is dead. Under tag-scoped rem-after-add
    that clash is causally Live (`CausalReach.orset_clash_joint`). The *scoped*
    guarantee that is actually true (and is what "add-wins" means) is
    `orset_present_survives`: presence through a tag the other side has not
    tombstoned survives.
  * CL-Set presence **is** I-confluent (`clset_present_iconfluent`) — because
    per-key max *selects* one replica's count, so per-key invariants are free
    (`selection_iconfluent`'s pointwise cousin). The arbitration got baked
    into the counter: whoever's causal length is longer wins that element.

Neither is "better"; they price the same square edit differently. OR-Set pays
in tag metadata and gives finer concurrent semantics; CL-Set pays in
arbitration (a longer remote history silently wins) and gives O(1) state per
element.

And the OR-Set's verdict is **a verdict about its remove op**, not about the
structure. §3 models the other one — the *element-wide* remove (`removeAll`,
"tombstone every tag of `a` I have observed") — and gets the opposite answer:
`orset_ew_present_iconfluent`. Two removes of that shape cannot disagree about
which tag survived, so the §1 clash never forms. What does still happen, and
should, is `removeAll_then_add_survives`: add-wins carrying a fresh tag
through a completed remove. The causal-reachability twin of the dichotomy is
`CausalReach.orset_reachability_depends_on_remove_shape`.
-/
import Uwueave.Catalog

namespace Uwueave.ORSet

open Uwueave Uwueave.Catalog

/-! ## §1. The OR-Set -/

/-- OR-Set state over elements `α` with tags `τ`: observed adds and observed
removes (tombstones), each a G-Set of (element, tag) pairs. The `MergeState`
is the product-of-GSets instance — inherited, not re-proved. -/
abbrev ORSet (α τ : Type) := GSet (α × τ) × GSet (α × τ)

example (α τ : Type) : MergeState (ORSet α τ) := inferInstance

/-- Presence: some tag witnesses an add that no observed remove has
tombstoned. -/
def Present {α τ : Type} (s : ORSet α τ) (a : α) : Prop :=
  ∃ t : τ, s.1 (a, t) = true ∧ s.2 (a, t) = false

/-- **The add-wins guarantee, correctly scoped.** If `x` holds `a` alive
through tag `t` and `y` has not tombstoned `t`, the merge holds `a` alive
(still through `t`). A remove can only tombstone tags it observed, so an add
concurrent with it survives — this is the theorem "add-wins" refers to. -/
theorem orset_present_survives {α τ : Type} (x y : ORSet α τ) (a : α) (t : τ)
    (hadd : x.1 (a, t) = true) (hx : x.2 (a, t) = false)
    (hy : y.2 (a, t) = false) :
    Present (x ⊔ y) a := by
  refine ⟨t, ?_, ?_⟩
  · show (x.1 (a, t) || y.1 (a, t)) = true
    simp [hadd]
  · show (x.2 (a, t) || y.2 (a, t)) = false
    simp [hx, hy]

/-- ⚠ **Unscoped presence is NOT I-confluent.** The clash: both replicas know
adds `{t₁, t₂}`; replica `x` has tombstoned `t₂` (alive through `t₁`), replica
`y` has tombstoned `t₁` (alive through `t₂`). Each is present; the merge
tombstones both tags and the element is gone.

Reachability (settled): under **tag-scoped rem-after-add** the clash pair *is*
jointly causally reachable — `CausalReach.orset_clash_joint` / `orset_clash_present`.
So this refutation is **Live** for that protocol reading, not LatticeOnly.

Read the scope: this is a theorem about the **tag-scoped** remove. The
element-wide "remove all observed tags" op is `removeAll` (§3), and on its
protocol class the same invariant is I-confluent
(`orset_ew_present_iconfluent`) — the clash needs one replica to tombstone
`t₂` while keeping `t₁`, which that op cannot do. Causally the same dichotomy
is settled in `CausalReach.lean` §6 (`ew_clashL_unreachable`,
`ew_clashR_unreachable`, `orset_reachability_depends_on_remove_shape`). The
judgement is still state-based; op-based add-wins guarantees remain the scoped
form `orset_present_survives`, never bare presence stability. -/
theorem orset_present_not_iconfluent :
    ¬ IConfluent (S := ORSet Nat Nat) (fun s => Present s 0) := by
  intro h
  -- x: adds {(0,1),(0,2)}, tombs {(0,2)} — alive through tag 1.
  -- y: adds {(0,1),(0,2)}, tombs {(0,1)} — alive through tag 2.
  have hbad := h
    (fun p => p == (0, 1) || p == (0, 2), fun p => p == (0, 2))
    (fun p => p == (0, 1) || p == (0, 2), fun p => p == (0, 1))
    ⟨1, by decide, by decide⟩ ⟨2, by decide, by decide⟩
  obtain ⟨t, hadd, htomb⟩ := hbad
  -- The merged adds only contain tags 1 and 2 …
  have ht : t = 1 ∨ t = 2 := by
    simp [prod_merge_fst, gset_mem_merge] at hadd
    omega
  -- … and the merged tombstones contain both.
  cases ht with
  | inl h1 => subst h1; exact absurd htomb (by decide)
  | inr h2 => subst h2; exact absurd htomb (by decide)

/-! ## §2. The causal-length set -/

/-- Causal-length set: per-element causal length, odd = present. Merge is
pointwise max — the Pi-over-max instance, inherited. -/
abbrev CLSet (α : Type) := α → Nat

example (α : Type) : MergeState (CLSet α) := inferInstance

/-- Presence is parity. -/
def CLPresent {α : Type} (s : CLSet α) (a : α) : Prop := s a % 2 = 1

/-- **CL-Set presence IS I-confluent** — per-key max selects one side's count,
so the merged parity is one of the two replicas' parities, and both were odd.
(The pointwise cousin of `selection_iconfluent`.) The flip side is the
arbitration this bakes in: a *longer* remote history wins the element even
when your local history is more recent in wall-clock terms — causal length,
not time, is the tiebreak. -/
theorem clset_present_iconfluent {α : Type} (a : α) :
    IConfluent (S := CLSet α) (fun s => CLPresent s a) := by
  intro x y hx hy
  show Nat.max (x a) (y a) % 2 = 1
  rw [nat_max_def]
  split
  · exact hy
  · exact hx

/-- Absence is I-confluent by the same selection argument — the CL-Set has no
analogue of the OR-Set's both-sides-tombstone anomaly, because there is
nothing element-shaped to lose: the counter *is* the element's whole story. -/
theorem clset_absent_iconfluent {α : Type} (a : α) :
    IConfluent (S := CLSet α) (fun s => s a % 2 = 0) := by
  intro x y hx hy
  show Nat.max (x a) (y a) % 2 = 0
  rw [nat_max_def]
  split
  · exact hy
  · exact hx

/-- ⚠ But *cross-element* invariants fail exactly as they did for LWW pairs:
"if `0` is present then `1` is present" dies when the merge takes `0`'s longer
count from one replica and `1`'s from the other. Same lesson, third structure:
**selection lattices compose into non-selection lattices.** -/
theorem clset_cross_element_not_iconfluent :
    ¬ IConfluent (S := CLSet Nat)
      (fun s => s 0 % 2 = 1 → s 1 % 2 = 1) := by
  intro h
  -- x: {0 ↦ 3, 1 ↦ 1} — both present.  y: {0 ↦ 2, 1 ↦ 2} — both absent-or-even,
  -- invariant vacuously fine. merge: {0 ↦ max(3,2)=3 (odd, PRESENT),
  -- 1 ↦ max(1,2)=2 (even, absent)} — antecedent holds, consequent dies.
  have hbad := h (fun n => if n = 0 then 3 else 1) (fun n => if n = 0 then 2 else 2)
    (by intro _; decide) (by intro hc; simp at hc)
  have h0 : Nat.max 3 2 % 2 = 1 := by decide
  have h1 := hbad (by
    show Nat.max ((if (0:Nat) = 0 then 3 else 1)) ((if (0:Nat) = 0 then 2 else 2)) % 2 = 1
    decide)
  revert h1
  show ¬ (Nat.max ((if (1:Nat) = 0 then 3 else 1)) ((if (1:Nat) = 0 then 2 else 2)) % 2 = 1)
  decide

/-! ## §3. The other remove: element-wide — back to §1's OR-Set.

§1's `orset_present_not_iconfluent` is a theorem about **tag-scoped** removes:
a remove tombstones the one tag it names, so two replicas can tombstone each
other's tag and annihilate the element. The classical observed-remove op is
different — "remove everything I have seen of `a`" — and it is modeled here as
`removeAll`, with the verdict it earns:

  * `orset_ew_present_iconfluent` — on the element-wide protocol class
    (`EWUniform` ∧ `TombsObserved`: a replica's tombstone bit is uniform
    across the tags of an element it has observed, and tombstones only ever
    name observed adds), **presence IS I-confluent**. The §1 anomaly is a
    property of the tag-scoped op, not of the OR-Set.
  * `orset_ew_present_survives` — the operational, asymmetric form: only the
    *removing* side needs the discipline for a concurrent add to survive.
  * `removeAll_uniform` / `removeAll_tombs_observed` — the op lands in that
    class, and `removeAll_absent` / `removeAll_frame` say what it does: the
    element goes, nothing else moves.
  * `removeAll_then_add_survives` — and the discipline is not a straitjacket:
    a replica that removes and *then* observes a new tag leaves the class, on
    purpose. That state has the §1 clash's exact shape and is perfectly
    reachable — it is add-wins working. What is unreachable is two replicas
    holding *asymmetric* tombstones after both saw both adds, which is the
    causal half of the story, settled in `CausalReach.lean` §6
    (`ew_clashL_unreachable`, `ew_clashR_unreachable`, and the dichotomy
    `orset_reachability_depends_on_remove_shape`). This section is the
    state-level twin of that: same two remove shapes, opposite verdicts. -/

/-- The OR-Set `add`: observe one (element, tag) pair. Tags are fresh per add,
which is the whole mechanism — a remove cannot have observed a tag that did
not exist when it ran. -/
def addTag {α τ : Type} [DecidableEq α] [DecidableEq τ] (s : ORSet α τ)
    (a : α) (t : τ) : ORSet α τ :=
  (fun p => s.1 p || decide (p = (a, t)), s.2)

/-- **Element-wide remove**: tombstone every tag of `a` this replica has
observed as added — "remove what I have seen", the classical observed-remove
op. Tags of other elements are untouched. -/
def removeAll {α τ : Type} [DecidableEq α] (s : ORSet α τ) (a : α) : ORSet α τ :=
  (s.1, fun p => s.2 p || (decide (p.1 = a) && s.1 p))

/-- The removing replica only adds tombstones, so it moves *up* the lattice:
`removeAll` is a legal CRDT operation, not a state rollback. -/
theorem le_removeAll {α τ : Type} [DecidableEq α] (s : ORSet α τ) (a : α) :
    s ⊑ removeAll s a := by
  show (s.1 ⊔ s.1, s.2 ⊔ (fun p => s.2 p || (decide (p.1 = a) && s.1 p)))
      = removeAll s a
  have h1 : s.1 ⊔ s.1 = s.1 := merge_idem s.1
  have h2 : s.2 ⊔ (fun p => s.2 p || (decide (p.1 = a) && s.1 p))
      = (fun p => s.2 p || (decide (p.1 = a) && s.1 p)) := by
    funext p
    show (s.2 p || (s.2 p || (decide (p.1 = a) && s.1 p)))
      = (s.2 p || (decide (p.1 = a) && s.1 p))
    cases s.2 p <;> cases (decide (p.1 = a) && s.1 p) <;> rfl
  rw [h1, h2]
  rfl

/-- After the remove the element is gone locally: every tag that could witness
it has just been tombstoned. -/
theorem removeAll_absent {α τ : Type} [DecidableEq α] (s : ORSet α τ) (a : α) :
    ¬ Present (removeAll s a) a := by
  intro ⟨t, hadd, htomb⟩
  have hadd' : s.1 (a, t) = true := hadd
  have : (s.2 (a, t) || (decide ((a, t).1 = a) && s.1 (a, t))) = false := htomb
  rw [hadd'] at this
  simp at this

/-- And nothing else moves: an element-wide remove of `a` leaves the presence
of every other element exactly as it was. -/
theorem removeAll_frame {α τ : Type} [DecidableEq α] (s : ORSet α τ) {a b : α}
    (h : b ≠ a) : Present (removeAll s b) a ↔ Present s a := by
  constructor
  · intro ⟨t, hadd, htomb⟩
    refine ⟨t, hadd, ?_⟩
    have : (s.2 (a, t) || (decide ((a, t).1 = b) && s.1 (a, t))) = false := htomb
    revert this
    simp [Ne.symm h]
  · intro ⟨t, hadd, htomb⟩
    refine ⟨t, hadd, ?_⟩
    show (s.2 (a, t) || (decide ((a, t).1 = b) && s.1 (a, t))) = false
    simp [Ne.symm h, htomb]

/-- Tombstones name only observed adds — the well-formedness every remove op
respects, since you cannot tombstone a tag you have never seen. -/
def TombsObserved {α τ : Type} (s : ORSet α τ) (a : α) : Prop :=
  ∀ t : τ, s.2 (a, t) = true → s.1 (a, t) = true

/-- **Element-wide uniformity**: across the tags of `a` this replica has
observed, its tombstone bit is the same for all of them. That is the signature
of a remove which tombstones *every* observed tag at once — and, dually, the
property a tag-scoped remove destroys. -/
def EWUniform {α τ : Type} (s : ORSet α τ) (a : α) : Prop :=
  ∀ t t' : τ, s.1 (a, t) = true → s.1 (a, t') = true → s.2 (a, t) = s.2 (a, t')

/-- The state right after an element-wide remove is uniform on that element:
every observed tag carries a tombstone. -/
theorem removeAll_uniform {α τ : Type} [DecidableEq α] (s : ORSet α τ) (a : α) :
    EWUniform (removeAll s a) a := by
  intro t t' ht ht'
  have h1 : s.1 (a, t) = true := ht
  have h2 : s.1 (a, t') = true := ht'
  show (s.2 (a, t) || (decide ((a, t).1 = a) && s.1 (a, t)))
    = (s.2 (a, t') || (decide ((a, t').1 = a) && s.1 (a, t')))
  simp [h1, h2]

/-- The op preserves tombstone well-formedness: it only tombstones what it has
observed. -/
theorem removeAll_tombs_observed {α τ : Type} [DecidableEq α] (s : ORSet α τ)
    (a : α) (h : TombsObserved s a) : TombsObserved (removeAll s a) a := by
  intro t ht
  have ht' : (s.2 (a, t) || (decide ((a, t).1 = a) && s.1 (a, t))) = true := ht
  show s.1 (a, t) = true
  by_cases hs : s.1 (a, t) = true
  · exact hs
  · have hsf : s.1 (a, t) = false := by simpa using hs
    rw [hsf] at ht'
    simp at ht'
    exact absurd (h t ht') hs

/-- A present element whose observed tags are uniformly tombstoned-or-not must
be uniformly *not*: one live tag forces every observed tag live, and
well-formedness forces the unobserved ones clear too. This is the shape lemma
the confluence result runs on. -/
theorem ew_tombs_clear {α τ : Type} {s : ORSet α τ} {a : α}
    (hp : Present s a) (hu : EWUniform s a) (ho : TombsObserved s a) :
    ∀ t : τ, s.2 (a, t) = false := by
  intro t
  obtain ⟨t₀, hadd₀, htomb₀⟩ := hp
  cases ht : s.2 (a, t) with
  | false => rfl
  | true =>
    have hobs : s.1 (a, t) = true := ho t ht
    have := hu t t₀ hobs hadd₀
    rw [ht, htomb₀] at this
    exact absurd this (by simp)

/-- **On the element-wide protocol class, presence IS I-confluent.** Two
replicas that each hold `a`, each tombstone uniformly across the tags of `a`
they have observed, and each tombstone only observed adds, merge to a state
that still holds `a` — and is still in the class. The §1 anomaly does not
arise: it needed one replica to tombstone tag `t₂` while keeping `t₁`, which
is precisely what "remove everything I have seen" cannot do.

Same lattice, same invariant, opposite verdict from
`orset_present_not_iconfluent` — the difference is entirely the shape of the
remove op, which is why that theorem must be read as a statement about
tag-scoped removes. The causal-reachability twin of this dichotomy is
`CausalReach.orset_reachability_depends_on_remove_shape`. -/
theorem orset_ew_present_iconfluent {α τ : Type} (a : α) :
    IConfluent (S := ORSet α τ)
      (fun s => Present s a ∧ EWUniform s a ∧ TombsObserved s a) := by
  intro x y hx hy
  have hxc := ew_tombs_clear hx.1 hx.2.1 hx.2.2
  have hyc := ew_tombs_clear hy.1 hy.2.1 hy.2.2
  have hmc : ∀ t : τ, (x ⊔ y).2 (a, t) = false := by
    intro t
    show (x.2 (a, t) || y.2 (a, t)) = false
    rw [hxc t, hyc t]
    rfl
  obtain ⟨t₀, hadd₀, _⟩ := hx.1
  refine ⟨⟨t₀, ?_, hmc t₀⟩, ?_, ?_⟩
  · show (x.1 (a, t₀) || y.1 (a, t₀)) = true
    simp [hadd₀]
  · intro t t' _ _
    rw [hmc t, hmc t']
  · intro t ht
    rw [hmc t] at ht
    exact absurd ht (by simp)

/-- **The operational form: only the remover needs the discipline.** If `y`
runs element-wide removes (uniform, well-formed tombstones) and still holds
`a`, then whatever `x` holds — however its own removes were shaped — `a`
survives the merge through `x`'s witnessing tag. `y` either tombstoned every
tag of `a` it saw (and would not hold `a`) or none of them; there is no
in-between for it to disagree with `x` about. -/
theorem orset_ew_present_survives {α τ : Type} (x y : ORSet α τ) (a : α)
    (hy : EWUniform y a) (hyo : TombsObserved y a)
    (hpx : Present x a) (hpy : Present y a) : Present (x ⊔ y) a := by
  obtain ⟨t, hadd, htomb⟩ := hpx
  refine ⟨t, ?_, ?_⟩
  · show (x.1 (a, t) || y.1 (a, t)) = true
    simp [hadd]
  · show (x.2 (a, t) || y.2 (a, t)) = false
    rw [htomb, ew_tombs_clear hpy hy hyo t]
    rfl

/-- A replica that has observed one add of element `0`, under tag `1`. -/
def sPreRemove : ORSet Nat Nat := (fun p => p == (0, 1), fun _ => false)

/-- ⚠ **Add-wins, through an element-wide remove.** The replica removes
everything it has seen of `0` and *then* observes a fresh add under tag `2`:
the element is present again, and the state is no longer `EWUniform` — tag `1`
tombstoned, tag `2` not. That is not a violation of anything; it is add-wins,
and it is why the class is a property of a *moment*, not an invariant a
replica keeps forever.

Note the shape: adds `{(0,1), (0,2)}`, tombstones `{(0,1)}` — exactly the
clash state `CausalReach.ewClashR`, which that file proves **no cut of the
element-wide history interprets to**. No contradiction: the unreachability is
relative to a history where both adds precede both removes. Here the remove
precedes the second add, which is a different history and an ordinary one. The
clash needs *two* such replicas disagreeing about which tag survived, and that
is what element-wide removes cannot produce. -/
theorem removeAll_then_add_survives :
    Present (addTag (removeAll sPreRemove 0) 0 2) 0 ∧
    ¬ EWUniform (addTag (removeAll sPreRemove 0) 0 2) 0 ∧
    ¬ Present (removeAll sPreRemove 0) 0 := by
  refine ⟨⟨2, by decide, by decide⟩, ?_, removeAll_absent sPreRemove 0⟩
  intro h
  exact absurd (h 1 2 (by decide) (by decide)) (by decide)

end Uwueave.ORSet
