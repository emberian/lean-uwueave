/-
# Uwueave.WovenOperational -- delivered edits and hole-aware terms

This module supplies two operational layers downstream of `Wellformed` and
`WovenEdit` without changing either document representation.

The delivery layer is a CmRDT set of stable edit identifiers. A finite catalog
maps those identifiers to proof-carrying, well-formed document deltas. Replay
materialises catalog entries in canonical catalog order, so duplicate delivery
is idempotent and every fair interleaving has the same declared view. This is a
finite-catalog theorem: it does not assert transport fairness or an unbounded
operation inventory.

The term layer is a typed sidecar over a woven document. It contains ordinary
nodes, cross-tree references, relocations, branches, and explicit holes whose
provenance is a nonempty list of stable edit ids. Synthesis handles terms with
enough information to determine their kind; checking additionally accepts a
hole at its declared expected kind. Accepted relocation/reference operations,
rendering, and resolution do not rewrite the underlying document, so the
existing six-field `WellFormed` theorem remains the structural floor.
-/
import Uwueave.WovenEdit

namespace Uwueave.WovenOperational

open Uwueave Uwueave.Catalog
open Uwueave.Wellformed

/-! ## 1. A duplicate-tolerant CmRDT delivery log -/

/-- Stable operation identity at the protocol boundary. -/
abbrev EditId := Nat

/-- A catalog operation is well typed by construction: its materialised delta
already satisfies the exact woven-document structural predicate. -/
structure LoggedEdit (n root : Nat) where
  id : EditId
  delta : WovenDoc
  wellFormed : WellFormed n root delta

/-- A finite operation inventory with collision-free stable identities. -/
structure EditCatalog (n root : Nat) where
  ops : List (LoggedEdit n root)
  uniqueIds : (ops.map LoggedEdit.id).Nodup

/-- Received operation identities form a grow-only set, hence inherit the
proved commutative, associative, idempotent merge. -/
abbrev DeliveryLog := GSet EditId

/-- A finite concurrent-delivery history; order and duplicates are retained in
the history even though the delivered CmRDT state forgets both. -/
abbrev EditHistory := List EditId

example : MergeState DeliveryLog := inferInstance

def emptyDelivery : DeliveryLog := fun _ => false

def deliver (log : DeliveryLog) (id : EditId) : DeliveryLog :=
  WovenEdit.insertG log id

def runDeliveries : DeliveryLog → EditHistory → DeliveryLog
  | log, [] => log
  | log, id :: ids => runDeliveries (deliver log id) ids

theorem deliver_duplicate (log : DeliveryLog) (id : EditId) :
    deliver (deliver log id) id = deliver log id := by
  funext candidate
  simp [deliver, WovenEdit.insertG]

theorem delivery_merge_comm (left right : DeliveryLog) :
    left ⊔ right = right ⊔ left := merge_comm left right

theorem runDeliveries_preserves (log : DeliveryLog) (schedule : EditHistory)
    (id : EditId) (present : log id = true) :
    runDeliveries log schedule id = true := by
  induction schedule generalizing log with
  | nil => exact present
  | cons head tail ih =>
      apply ih (deliver log head)
      exact (WovenEdit.insertG_apply log head id).2 (Or.inl present)

theorem runDeliveries_contains (log : DeliveryLog) (schedule : EditHistory)
    (id : EditId) (present : id ∈ schedule) :
    runDeliveries log schedule id = true := by
  induction schedule generalizing log with
  | nil => simp at present
  | cons head tail ih =>
      simp only [List.mem_cons] at present
      cases present with
      | inl equal =>
          subst equal
          simp only [runDeliveries]
          apply runDeliveries_preserves (deliver log id) tail id
          simp [deliver, WovenEdit.insertG]
      | inr later =>
          simp only [runDeliveries]
          exact ih (deliver log head) later

/-- The declared observable is the canonical fold of precisely the catalog
deltas whose stable identities have been delivered. -/
def deliveryView {n root : Nat} (catalog : EditCatalog n root)
    (base : WovenDoc) (log : DeliveryLog) : WovenDoc :=
  Wellformed.mergeAll base
    ((catalog.ops.filter fun operation => log operation.id).map
      LoggedEdit.delta)

/-- Any delivery state has a well-formed view. Redelivery and partial delivery
cannot expose a malformed intermediate document. -/
theorem deliveryView_wellFormed {n root : Nat}
    (catalog : EditCatalog n root) (base : WovenDoc)
    (baseWellFormed : WellFormed n root base) (log : DeliveryLog) :
    WellFormed n root (deliveryView catalog base log) := by
  apply Wellformed.mergeAll_wellformed n root _ base baseWellFormed
  intro delta member
  simp only [List.mem_map] at member
  obtain ⟨operation, _, rfl⟩ := member
  exact operation.wellFormed

/-- A finite history is fair for a catalog when it delivers every catalogued
stable identity at least once; duplicates and order are unrestricted. -/
def Fair {n root : Nat} (catalog : EditCatalog n root)
    (schedule : EditHistory) : Prop :=
  ∀ operation ∈ catalog.ops, operation.id ∈ schedule

theorem fair_filter_is_catalog {n root : Nat}
    (catalog : EditCatalog n root) (schedule : EditHistory)
    (fair : Fair catalog schedule) :
    catalog.ops.filter
        (fun operation => runDeliveries emptyDelivery schedule operation.id) =
      catalog.ops := by
  apply List.filter_eq_self.2
  intro operation member
  exact runDeliveries_contains emptyDelivery schedule operation.id
    (fair operation member)

/-- Every pair of fair delivery interleavings of the well-typed catalog
preserves `WellFormed` and converges exactly in the declared view. -/
theorem fair_interleavings_preserve_and_converge {n root : Nat}
    (catalog : EditCatalog n root) (base : WovenDoc)
    (baseWellFormed : WellFormed n root base)
    (left right : EditHistory) (leftFair : Fair catalog left)
    (rightFair : Fair catalog right) :
    WellFormed n root
        (deliveryView catalog base (runDeliveries emptyDelivery left)) ∧
      WellFormed n root
        (deliveryView catalog base (runDeliveries emptyDelivery right)) ∧
      deliveryView catalog base (runDeliveries emptyDelivery left) =
        deliveryView catalog base (runDeliveries emptyDelivery right) := by
  refine ⟨deliveryView_wellFormed catalog base baseWellFormed _,
    deliveryView_wellFormed catalog base baseWellFormed _, ?_⟩
  simp only [deliveryView, fair_filter_is_catalog catalog left leftFair,
    fair_filter_is_catalog catalog right rightFair]

def editX : LoggedEdit 5 9 := ⟨1, docX, docX_wellFormed⟩
def editY : LoggedEdit 5 9 := ⟨2, docY, docY_wellFormed⟩

def concurrentXY : EditCatalog 5 9 where
  ops := [editX, editY]
  uniqueIds := by decide

def deliveryLeft : EditHistory := [1, 2, 1]
def deliveryRight : EditHistory := [2, 1, 2]

theorem deliveryLeft_fair : Fair concurrentXY deliveryLeft := by
  simp [Fair, concurrentXY, deliveryLeft, editX, editY]
theorem deliveryRight_fair : Fair concurrentXY deliveryRight := by
  simp [Fair, concurrentXY, deliveryRight, editX, editY]

theorem concurrent_delivery_fixture :
    WellFormed 5 9
        (deliveryView concurrentXY docX
          (runDeliveries emptyDelivery deliveryLeft)) ∧
      WellFormed 5 9
        (deliveryView concurrentXY docX
          (runDeliveries emptyDelivery deliveryRight)) ∧
      deliveryView concurrentXY docX
          (runDeliveries emptyDelivery deliveryLeft) =
        deliveryView concurrentXY docX
          (runDeliveries emptyDelivery deliveryRight) :=
  fair_interleavings_preserve_and_converge concurrentXY docX docX_wellFormed
    deliveryLeft deliveryRight deliveryLeft_fair deliveryRight_fair

/-! ## 2. Hole-aware bidirectional terms -/

inductive Kind where
  | node
  | forest
  deriving DecidableEq, Repr

/-- Provenance is intentionally explicit in relocations, cross-tree
references, and holes. -/
inductive Term where
  | node (node : NodeId)
  | branch (left right : Term)
  | crossTree (tree node : Nat) (origin : EditId)
  | relocated (node destination : NodeId) (origin : EditId)
  | hole (expected : Kind) (origins : List EditId)
  deriving DecidableEq, Repr

/-- Synthesis refuses holes: their expected type is checked, never inferred. -/
def synth? (document : WovenDoc) : Term → Option Kind
  | .node node => if nodes document node then some .node else none
  | .branch left right =>
      if synth? document left = some .node ∧
          synth? document right = some .node then
        some .forest
      else none
  | .crossTree _ node _ => if nodes document node then some .node else none
  | .relocated node destination _ =>
      if nodes document node ∧ nodes document destination then some .node
      else none
  | .hole _ _ => none

/-- Checking extends synthesis with nonempty, provenance-carrying holes. -/
def check? (document : WovenDoc) (term : Term) (expected : Kind) : Bool :=
  match term with
  | .hole declared origins => declared == expected && !origins.isEmpty
  | other => synth? document other == some expected

/-- The synthesis judgement is the proposition exposed by the executable
synthesizer. -/
def Synth (document : WovenDoc) (term : Term) (kind : Kind) : Prop :=
  synth? document term = some kind

/-- The checking judgement is the proposition exposed by the executable
checker. -/
def Checks (document : WovenDoc) (term : Term) (kind : Kind) : Prop :=
  check? document term kind = true

theorem synth_implies_check {document : WovenDoc} {term : Term} {kind : Kind}
    (synthesizes : Synth document term kind) : Checks document term kind := by
  cases term <;> simp_all [Synth, Checks, check?, synth?]

theorem hole_checks_iff (document : WovenDoc) (declared expected : Kind)
    (origins : List EditId) :
    Checks document (.hole declared origins) expected ↔
      declared = expected ∧ origins ≠ [] := by
  simp [Checks, check?]

/-- A typed term state couples the bidirectional judgement to the structural
document floor. -/
structure TypedTermState (n root : Nat) (kind : Kind) where
  document : WovenDoc
  term : Term
  wellFormed : WellFormed n root document
  checks : Checks document term kind

inductive Rendered where
  | node (node : NodeId)
  | branch (left right : Rendered)
  | reference (tree node : Nat) (origin : EditId)
  | moved (node destination : NodeId) (origin : EditId)
  | unresolved (expected : Kind) (origins : List EditId)
  deriving DecidableEq, Repr

def render : Term → Rendered
  | .node node => .node node
  | .branch left right => .branch (render left) (render right)
  | .crossTree tree node origin => .reference tree node origin
  | .relocated node destination origin => .moved node destination origin
  | .hole expected origins => .unresolved expected origins

/-- Typed evaluation is total and preserves the underlying structural floor. -/
def evaluate {n root : Nat} {kind : Kind}
    (state : TypedTermState n root kind) : Rendered :=
  render state.term

/-- Rendering is a total sidecar transformation and cannot invalidate the
underlying woven document. -/
theorem rendering_preserves_wellFormed {n root : Nat}
    (document : WovenDoc) (documentWellFormed : WellFormed n root document)
    (term : Term) :
    ∃ output : Rendered, render term = output ∧ WellFormed n root document :=
  ⟨render term, rfl, documentWellFormed⟩

theorem typed_evaluation_preserves_wellFormed {n root : Nat} {kind : Kind}
    (state : TypedTermState n root kind) :
    WellFormed n root state.document :=
  state.wellFormed

/-! ## 3. Accepted operations, relocation conflicts, and resolution -/

inductive TermCommand where
  | relocate (id : EditId) (node destination : NodeId)
  | crossTree (id : EditId) (tree : Nat) (node : NodeId)
  deriving DecidableEq, Repr

/-- Operation checking establishes referential integrity before constructing
the typed sidecar term. -/
def checkCommand (document : WovenDoc) : TermCommand → Option Term
  | .relocate id node destination =>
      if nodes document node ∧ nodes document destination then
        some (.relocated node destination id)
      else none
  | .crossTree id tree node =>
      if nodes document node then some (.crossTree tree node id) else none

theorem accepted_command_checks {document : WovenDoc} {command : TermCommand}
    {term : Term} (accepted : checkCommand document command = some term) :
    Checks document term .node := by
  cases command with
  | relocate id node destination =>
      simp only [checkCommand] at accepted
      split at accepted
      · next condition =>
          cases accepted
          simp [Checks, check?, synth?, condition]
      · simp at accepted
  | crossTree id tree node =>
      simp only [checkCommand] at accepted
      split at accepted
      · next condition =>
          cases accepted
          simp [Checks, check?, synth?, condition]
      · simp at accepted

/-- Every accepted term edit preserves `WellFormed`; commands change only the
typed sidecar and cannot invalidate the underlying woven document. -/
theorem every_accepted_edit_preserves_wellFormed {n root : Nat}
    {document : WovenDoc} (documentWellFormed : WellFormed n root document)
    {command : TermCommand} {term : Term}
    (accepted : checkCommand document command = some term) :
    ∃ state : TypedTermState n root .node,
      state.document = document ∧ state.term = term :=
  ⟨⟨document, term, documentWellFormed,
      accepted_command_checks accepted⟩, rfl, rfl⟩

theorem positive_relocation_fixture :
    checkCommand docX (.relocate 101 0 1) =
      some (.relocated 0 1 101) := by decide

theorem rejected_relocation_fixture :
    checkCommand docX (.relocate 101 0 12) = none := by decide

theorem cross_tree_reference_fixture :
    checkCommand docX (.crossTree 103 7 1) =
      some (.crossTree 7 1 103) := by decide

structure Relocation where
  id : EditId
  node : NodeId
  destination : NodeId
  deriving DecidableEq, Repr

/-- Two outcomes for the same node and different destinations become a hole,
retaining both stable edit identities in deterministic left/right order. -/
def mergeRelocations (left right : Relocation) : Term :=
  if left.node = right.node ∧ left.destination ≠ right.destination then
    .hole .node [left.id, right.id]
  else
    .branch (.relocated left.node left.destination left.id)
      (.relocated right.node right.destination right.id)

def relocationLeft : Relocation := ⟨101, 0, 0⟩
def relocationRight : Relocation := ⟨102, 0, 1⟩

theorem conflicting_relocations_are_accepted :
    checkCommand docX (.relocate 101 0 0) =
        some (.relocated 0 0 101) ∧
      checkCommand docX (.relocate 102 0 1) =
        some (.relocated 0 1 102) := by decide

theorem relocation_conflict_retains_provenance :
    mergeRelocations relocationLeft relocationRight =
      .hole .node [101, 102] := by decide

theorem conflict_hole_checks :
    Checks docX (mergeRelocations relocationLeft relocationRight) .node := by
  rw [relocation_conflict_retains_provenance]
  rfl

theorem conflict_render_retains_provenance :
    render (mergeRelocations relocationLeft relocationRight) =
      .unresolved .node [101, 102] := by decide

/-- Resolve a node hole only to an existing node. Other terms are already
resolved and pass through unchanged. -/
def resolve (document : WovenDoc) (term : Term) (chosen : NodeId) : Option Term :=
  match term with
  | .hole .node origins =>
      if !origins.isEmpty ∧ nodes document chosen then some (.node chosen)
      else none
  | .hole .forest _ => none
  | other => some other

theorem successful_resolution_checks {document : WovenDoc} {term resolved : Term}
    {chosen : NodeId} (success : resolve document term chosen = some resolved)
    (hole : ∃ origins, term = .hole .node origins) :
    Checks document resolved .node := by
  obtain ⟨origins, rfl⟩ := hole
  simp only [resolve] at success
  split at success
  · next condition =>
      cases success
      simp [Checks, check?, synth?, condition.2]
  · simp at success

/-- Resolution also preserves the underlying `WellFormed` document floor. -/
theorem resolution_preserves_wellFormed {n root : Nat}
    {document : WovenDoc} (documentWellFormed : WellFormed n root document)
    {term resolved : Term} {chosen : NodeId}
    (success : resolve document term chosen = some resolved) :
    WellFormed n root document := by
  have _resolved : ∃ candidate,
      resolve document term chosen = some candidate := ⟨resolved, success⟩
  exact documentWellFormed

theorem conflict_resolution_fixture :
    resolve docX (mergeRelocations relocationLeft relocationRight) 1 =
      some (.node 1) ∧
    Checks docX (.node 1) .node ∧
    WellFormed 5 9 docX := by
  refine ⟨by decide, ?_, docX_wellFormed⟩
  rfl

end Uwueave.WovenOperational
