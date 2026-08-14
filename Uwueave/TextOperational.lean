/-
# Uwueave.TextOperational -- content identity, canonical Fugue state, and scoped GC

This downstream module adds the operational data deliberately absent from
`TextSummary`. Content-bearing insertions carry their bytes-at-miniature-scale,
with a deterministic address derived from `(anchor, content)`. Fugue operations
remain a grow-only set and are materialised through `TextSummary`'s canonical
enumeration before the reference `Fugue.docOrder` is called.

Garbage collection is explicitly scoped. A `StabilityCertificate` contains a
finite list of admitted future contexts and a checked proof that collected ids
are already tombstoned, are not nameable by any listed future, and preserve the
visible view in every listed future. It is not a claim about unlisted or
unbounded futures; `TextSummary.no_gc_summary_sufficient` remains the negative
boundary for unrestricted contexts.
-/
import Uwueave.TextSummary

namespace Uwueave.TextOperational

open Uwueave Uwueave.Catalog
open Uwueave.TextSummary

/-! ## 1. Content-bearing, content-addressed insertions -/

/- A deterministic miniature content address compatible with
`TextSummary.glyph`. That reference labelling reserves `2` for `b`, `4` for
`c`, and every other id for `a`; `a` addresses retain the anchor explicitly.
The collision-free batch premise below is therefore load-bearing for repeated
`b` or `c` insertions in this deliberately three-glyph model. -/
def contentId (anchor : Nat) : Glyph → Nat
  | .a => anchor + 5
  | .b => 2
  | .c => 4

/-- The global content labelling induced by `contentId`. -/
def glyphAtId (id : Nat) : Glyph :=
  TextSummary.glyph id

theorem glyphAtId_contentId (anchor : Nat) (content : Glyph) :
    glyphAtId (contentId anchor content) = content := by
  cases content <;> simp [contentId, glyphAtId, TextSummary.glyph]

/-- Wire form: content is a field, while `id` is independently inspectable so
malformed/colliding input can be rejected rather than made unrepresentable. -/
structure ContentInsert where
  id : Nat
  anchor : Nat
  content : Glyph
  deriving DecidableEq, Repr

def ContentInsert.canonical (op : ContentInsert) : Prop :=
  op.id = contentId op.anchor op.content

def canonicalInsert (anchor : Nat) (content : Glyph) : ContentInsert :=
  ⟨contentId anchor content, anchor, content⟩

@[simp] theorem canonicalInsert_is_canonical (anchor : Nat) (content : Glyph) :
    (canonicalInsert anchor content).canonical := rfl

/-- No two operations in the finite batch use one id for different payloads. -/
def CollisionFree (ops : List ContentInsert) : Prop :=
  ∀ left ∈ ops, ∀ right ∈ ops, left.id = right.id → left = right

def CanonicalBatch (ops : List ContentInsert) : Prop :=
  ∀ op ∈ ops, op.canonical

/-- For a collision-free canonical batch, every operation's content is
recovered by the exact global `Nat -> Glyph` labelling used by
`TextSummary.text`. -/
theorem collision_free_batch_projects_to_global_glyph
    (ops : List ContentInsert) (canonical : CanonicalBatch ops)
    (collisionFree : CollisionFree ops) :
    CollisionFree ops ∧ ∀ op ∈ ops, glyphAtId op.id = op.content := by
  refine ⟨collisionFree, ?_⟩
  intro op hop
  rw [canonical op hop]
  exact glyphAtId_contentId op.anchor op.content

/-- Forget content to the positional carrier used by `TextSummary`. -/
def projectSeq (ops : List ContentInsert) : Sequence.SeqState :=
  fun pair => ops.any fun op => op.id == pair.1 && op.anchor == pair.2

def project (ops : List ContentInsert) : TState :=
  (projectSeq ops, fun _ => false)

/-- Collision-free canonical batches project to actual sequence edges, and
the fixed labelling that `TextSummary.text` applies to every projected id
recovers the retained payload. -/
theorem collision_free_projection_agrees (ops : List ContentInsert)
    (canonical : CanonicalBatch ops) (collisionFree : CollisionFree ops) :
    CollisionFree ops ∧ ∀ operation ∈ ops,
      (project ops).1 (operation.id, operation.anchor) = true ∧
      TextSummary.glyph operation.id = operation.content := by
  refine ⟨collisionFree, ?_⟩
  intro operation member
  constructor
  · change (ops.any fun candidate =>
        candidate.id == operation.id &&
          candidate.anchor == operation.anchor) = true
    rw [List.any_eq_true]
    exact ⟨operation, member, by simp⟩
  · change glyphAtId operation.id = operation.content
    exact (collision_free_batch_projects_to_global_glyph ops canonical
      collisionFree).2 operation member

/-- Operational content state: insertion payloads are retained in the carrier,
while deletion remains the grow-only tombstone information of `TextSummary`. -/
structure ContentState where
  insertions : List ContentInsert
  tombstones : GSet Nat

def emptyContent : ContentState := ⟨[], fun _ => false⟩

inductive ContentOp where
  | insert (operation : ContentInsert)
  | delete (id : Nat)

def applyContent (state : ContentState) : ContentOp → ContentState
  | .insert operation => ⟨operation :: state.insertions, state.tombstones⟩
  | .delete id =>
      ⟨state.insertions, fun candidate => state.tombstones candidate || candidate == id⟩

/-- Erasing content produces exactly the insertion/tombstone carrier consumed
by `TextSummary.visible`. -/
def projectContent (state : ContentState) : TState :=
  (projectSeq state.insertions, state.tombstones)

@[simp] theorem projectContent_insert (state : ContentState)
    (operation : ContentInsert) :
    projectContent (applyContent state (.insert operation)) =
      (projectSeq (operation :: state.insertions), state.tombstones) := rfl

@[simp] theorem projectContent_delete (state : ContentState) (id : Nat) :
    (projectContent (applyContent state (.delete id))).2 =
      fun candidate => state.tombstones candidate || candidate == id := rfl

def collisionLeft : ContentInsert := ⟨1, 0, .a⟩
def collisionRight : ContentInsert := ⟨1, 0, .b⟩

/-- If collision-freedom is dropped, positional projection cannot distinguish
two different contents for the same id. -/
theorem collision_counterexample :
    project [collisionLeft] = project [collisionRight]
      ∧ collisionLeft.content ≠ collisionRight.content
      ∧ ¬ CollisionFree [collisionLeft, collisionRight] := by
  constructor
  · apply Prod.ext
    · funext pair
      simp [project, projectSeq, collisionLeft, collisionRight]
    · rfl
  constructor
  · decide
  · intro collisionFree
    have equal := collisionFree collisionLeft (by simp) collisionRight (by simp) rfl
    exact absurd (congrArg ContentInsert.content equal) (by decide)

/-! ## 2. The canonical commutative-idempotent Fugue operation set -/

/-- The production Fugue carrier is the operation set already used by
`TextSummary`, not `Fugue.OpSet`'s list wrapper. -/
abbrev FugueState := TextSummary.FState

example : MergeState FugueState := inferInstance

def materializeFugue (bound : Nat) (state : FugueState) : Fugue.OpSet :=
  TextSummary.toOpSet bound state

def fugueDocOrder (bound : Nat) (state : FugueState) : List Nat :=
  Fugue.docOrder bound (materializeFugue bound state)

theorem fugue_state_merge_comm (left right : FugueState) :
    left ⊔ right = right ⊔ left := merge_comm left right

theorem fugue_state_merge_idem (state : FugueState) :
    state ⊔ state = state := merge_idem state

theorem materialized_docOrder_agrees_reference (bound : Nat)
    (state : FugueState) :
    fugueDocOrder bound state =
      Fugue.docOrder bound (TextSummary.toOpSet bound state) := rfl

def canonicalFugueText (bound : Nat) (state : FugueState) : List Glyph :=
  ((fugueDocOrder bound state).filter (TextSummary.minted bound state)).map
    TextSummary.glyph

theorem canonical_fugue_witness_agrees :
    canonicalFugueText 4 (TextSummary.fugueALow ⊔ TextSummary.fugueBMid) =
        TextSummary.fugueText 4
          (TextSummary.fugueALow ⊔ TextSummary.fugueBMid)
      ∧ canonicalFugueText 4
          (TextSummary.fugueALow ⊔ TextSummary.fugueBMid) = [.a, .b] :=
  ⟨rfl, TextSummary.fugue_low_merge⟩

/-! ## 3. Tombstone collection under an explicit causal-stability scope -/

def namesId (bound : Nat) (future : TState) (id : Nat) : Bool :=
  future.2 id || (TextSummary.window bound).any fun pair =>
    future.1 pair && (pair.1 == id || pair.2 == id)

/-- Physically remove the insertion records and tombstones for the certified
ids. This is deliberately not a lattice mutation; it is a scoped compaction. -/
def collect (state : TState) (ids : List Nat) : TState :=
  (fun pair => state.1 pair && !(ids.contains pair.1),
   fun id => state.2 id && !(ids.contains id))

/-- Executable certificate check. Besides future unnameability it checks the
semantic preservation equation itself, so accepting a certificate never asks
the kernel to trust that the caller's finite inventory is adequate. -/
def stabilityB (bound : Nat) (state : TState) (ids : List Nat)
    (futures : List TState) : Bool :=
  ids.all state.2 && futures.all fun future =>
    ids.all (fun id => !(namesId bound future id)) &&
      decide (TextSummary.visible bound (collect state ids ⊔ future) =
        TextSummary.visible bound (state ⊔ future))

structure StabilityCertificate (bound : Nat) (state : TState)
    (ids : List Nat) where
  futures : List TState
  checked : stabilityB bound state ids futures = true

def StabilityCertificate.Admitted {bound : Nat} {state : TState}
    {ids : List Nat} (certificate : StabilityCertificate bound state ids)
    (future : TState) : Prop :=
  future ∈ certificate.futures

theorem StabilityCertificate.collected_ids_tombstoned {bound : Nat}
    {state : TState} {ids : List Nat}
    (certificate : StabilityCertificate bound state ids) :
    ∀ id ∈ ids, state.2 id = true := by
  have checked := ((Bool.and_eq_true _ _).mp certificate.checked).1
  exact List.all_eq_true.mp checked

theorem StabilityCertificate.future_cannot_name_collected {bound : Nat}
    {state : TState} {ids : List Nat}
    (certificate : StabilityCertificate bound state ids) {future : TState}
    (admitted : certificate.Admitted future) :
    ∀ id ∈ ids, namesId bound future id = false := by
  have futuresChecked := ((Bool.and_eq_true _ _).mp certificate.checked).2
  have futureChecked := (List.all_eq_true.mp futuresChecked) future admitted
  have namesChecked := ((Bool.and_eq_true _ _).mp futureChecked).1
  intro id hid
  have hnot := (List.all_eq_true.mp namesChecked) id hid
  simpa using hnot

/-- Every admitted future sees exactly the same visible document after scoped
collection. No conclusion is available for a context absent from the
certificate's finite inventory. -/
theorem StabilityCertificate.visible_preserved {bound : Nat}
    {state : TState} {ids : List Nat}
    (certificate : StabilityCertificate bound state ids) {future : TState}
    (admitted : certificate.Admitted future) :
    TextSummary.visible bound (collect state ids ⊔ future) =
      TextSummary.visible bound (state ⊔ future) := by
  have futuresChecked := ((Bool.and_eq_true _ _).mp certificate.checked).2
  have futureChecked := (List.all_eq_true.mp futuresChecked) future admitted
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp futureChecked).2

def deletedOneStable : StabilityCertificate 5 TextSummary.deletedOne [1] where
  futures := [TextSummary.noOps, TextSummary.typedBMid]
  checked := by decide

theorem scoped_gc_fixture :
    namesId 5 TextSummary.noOps 1 = false
      ∧ TextSummary.visible 5
          (collect TextSummary.deletedOne [1] ⊔ TextSummary.noOps) =
        TextSummary.visible 5
          (TextSummary.deletedOne ⊔ TextSummary.noOps)
      ∧ TextSummary.visible 5
          (collect TextSummary.deletedOne [1] ⊔ TextSummary.typedBMid) =
        TextSummary.visible 5
          (TextSummary.deletedOne ⊔ TextSummary.typedBMid) := by
  refine ⟨deletedOneStable.future_cannot_name_collected
      (future := TextSummary.noOps)
        (by simp [StabilityCertificate.Admitted, deletedOneStable]) 1
        (by simp), ?_, ?_⟩
  · exact deletedOneStable.visible_preserved
      (future := TextSummary.noOps)
        (by simp [StabilityCertificate.Admitted, deletedOneStable])
  · exact deletedOneStable.visible_preserved
      (future := TextSummary.typedBMid)
        (by simp [StabilityCertificate.Admitted, deletedOneStable])

/-- The unrestricted negative boundary is retained verbatim. -/
theorem unrestricted_gc_remains_unsound {T : Type} (summary : TState → T)
    (factors : ∃ post : List (Nat × Nat) → T,
      ∀ state, summary state = post (TextSummary.garbageCollected 5 state)) :
    ¬ Sufficient summary (TextSummary.text 5) :=
  TextSummary.no_gc_summary_sufficient summary factors

end Uwueave.TextOperational
