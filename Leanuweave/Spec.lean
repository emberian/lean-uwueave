/-
# Leanuweave.Spec — a fluid, proof-carrying composition DSL.

The point of the catalog is to be *composed*: a real document schema is a
record of fields — a node set here, a per-node register there, a quota, a
bookmark set. This file is the algebra that lets you build the schema
fluently and get, at the top, not a heuristic but a **verdict that carries its
own evidence**:

  * `Verdict.free h`            — an actual `IConfluent` proof, or
  * `Verdict.clash x y …`       — an actual two-replica counterexample,
                                  transported up through every combinator, so
                                  the top-level answer to "can my whole
                                  document replicate coordination-free?" is
                                  either a theorem or a runnable repro.

The design is a *shallow* embedding: a "spec" is just a Lean type with a
`MergeState` instance, built with ordinary `×` and `→`, and classified
invariants compose with ordinary function application. You get binders, `let`,
recursion and notation from Lean itself instead of from a bespoke AST — that
is what makes it fluid. (A deep embedding with a reflective `Spec` inductive
would buy serialization of specs, at the price of universe bookkeeping; if a
tool needs that later, it can quote *into* this layer.)

The two examples at the bottom are the intended user experience: a loom
document schema assembled in six lines, classified field-by-field, with one
deliberately-poisoned variant showing a single field's counterexample
propagating to the whole document.
-/
import Leanuweave.Move

namespace Leanuweave.Spec

open Leanuweave Leanuweave.Catalog

universe u v

/-! ## §1. Verdicts -/

/-- A classified invariant: either provably coordination-free, or refuted by a
concrete clashing pair. `escalation_witness` guarantees every non-confluent
invariant *has* a clash, so this type loses no generality — it just insists the
evidence be produced rather than promised. -/
inductive Verdict {S : Type u} [MergeState S] (I : Invariant S) : Type u where
  /-- Coordination-free, with the proof. -/
  | free (h : IConfluent I)
  /-- Requires coordination; `x`, `y` are legal replica states whose merge is
  illegal — the repro a test suite should replay. -/
  | clash (x y : S) (hx : I x) (hy : I y) (hbad : ¬ I (x ⊔ y))

namespace Verdict

variable {A : Type u} {B : Type v} [MergeState A] [MergeState B]

/-- Conjunction of two free invariants **on the same state** is free. (No
independence needed — both watch the same merge.) -/
def andFree {I J : Invariant A} :
    Verdict I → Verdict J → Option (Verdict (fun s => I s ∧ J s))
  | .free hI, .free hJ => some (.free (and_iconfluent hI hJ))
  | _, _ => none
  -- `none` is honest: a conjunction with a non-confluent conjunct is not
  -- automatically non-confluent (the other conjunct may exclude the clash
  -- states), so no verdict is claimed. Classify the conjunction directly if
  -- you need one.

/-- Two free field invariants give a free record invariant — `product_iconfluent`
as a combinator. -/
def prodFree {IA : Invariant A} {IB : Invariant B} :
    IConfluent IA → IConfluent IB → Verdict (S := A × B) (fun p => IA p.1 ∧ IB p.2) :=
  fun hA hB => .free (product_iconfluent hA hB)

/-- **Counterexample transport, left field.** A clash on field A becomes a clash
on the whole record, holding any legal field-B value fixed (idempotence keeps
it fixed through the merge). This is what makes the DSL's failures *actionable*:
the top-level repro names the exact field and states. -/
def prodClashLeft {IA : Invariant A} {IB : Invariant B}
    (x y : A) (hx : IA x) (hy : IA y) (hbad : ¬ IA (x ⊔ y))
    (b : B) (hb : IB b) : Verdict (S := A × B) (fun p => IA p.1 ∧ IB p.2) :=
  .clash (x, b) (y, b) ⟨hx, hb⟩ ⟨hy, hb⟩
    (fun hmerge => hbad hmerge.1)

/-- Counterexample transport, right field. -/
def prodClashRight {IA : Invariant A} {IB : Invariant B}
    (x y : B) (hx : IB x) (hy : IB y) (hbad : ¬ IB (x ⊔ y))
    (a : A) (ha : IA a) : Verdict (S := A × B) (fun p => IA p.1 ∧ IB p.2) :=
  .clash (a, x) (a, y) ⟨ha, hx⟩ ⟨ha, hy⟩
    (fun hmerge => hbad hmerge.2)

/-- A per-key-free invariant is free over the keyed map — `pi_iconfluent` as a
combinator. -/
def keyedFree {K : Type u} {V : Type v} [MergeState V] {J : K → Invariant V}
    (h : ∀ k, IConfluent (J k)) :
    Verdict (S := K → V) (fun f => ∀ k, J k (f k)) :=
  .free (pi_iconfluent h)

/-- Erase the evidence, keep the answer — for reporting. -/
def isFree {S : Type u} [MergeState S] {I : Invariant S} : Verdict I → Bool
  | .free _ => true
  | .clash .. => false

end Verdict

/-! ## §2. Worked example — a loom document schema, assembled and classified.

The schema (deliberately shaped like a universal-weave instance):

  * `nodes`     : a grow-only node-id set              (`GSet Nat`)
  * `meta`      : a per-node LWW register              (`Nat → LWW`)
  * `bookmarks` : per-device bookmark counts against
                  a per-device quota (escrowed)        (`Escrow Bool`)

State and merge come from `×` and `→` — no new instances, no new proofs. -/

/-- The document state. This *is* the DSL: ordinary type formers, instances
resolved by composition. -/
abbrev LoomDoc := GSet Nat × ((Nat → LWW) × Escrow Bool)

example : MergeState LoomDoc := inferInstance

/-- The document invariant: genesis node present; every metadata register's
timestamp at least 1 (i.e. genuinely written); no device over its bookmark
quota. -/
def loomInv (quota : Bool → Nat) : Invariant LoomDoc := fun d =>
  (d.1 0 = true)
  ∧ ((∀ k, 1 ≤ (d.2.1 k).ts) ∧ (∀ i, d.2.2 i ≤ quota i))

/-- **The whole document replicates coordination-free** — built entirely from
catalog verdicts and the two lifts, one combinator per schema node. Read the
term: it *is* the schema's classification report. -/
def loomVerdict (quota : Bool → Nat) : Verdict (loomInv quota) :=
  .free (product_iconfluent
    (gset_mem_iconfluent 0)
    (product_iconfluent
      (pi_iconfluent fun _ => lww_every_invariant_iconfluent (fun r => 1 ≤ r.ts))
      (escrow_local_bound_iconfluent quota)))

/-! ### The poisoned variant

Add one innocent-looking feature — "a document has at most one pinned node",
a uniqueness ceiling on a grow-only set — and the *document* stops being
coordination-free, with the pin-set's `{0}`/`{1}` clash transported to a
whole-document repro. -/

/-- The poisoned schema: the same document plus a pinned-node set that is
supposed to stay a singleton. -/
abbrev PinnedDoc := GSet Nat × GSet Nat  -- (nodes, pins)

def pinnedInv : Invariant PinnedDoc := fun d =>
  (d.1 0 = true) ∧ (∀ m n, d.2 m = true → d.2 n = true → m = n)

/-- ⚠ The uniqueness ceiling's clash, transported: two replicas that each pin a
different node. Both are legal whole documents; their merge pins two nodes.
The evidence is a pair of complete document states — paste them into a test. -/
def pinnedVerdict : Verdict pinnedInv :=
  Verdict.prodClashRight (IA := fun s => s 0 = true)
    (IB := fun s => ∀ m n, s m = true → s n = true → m = n)
    (fun n => n == 0) (fun n => n == 1)
    (fun m n hm hn => by simp at hm hn; omega)
    (fun m n hm hn => by simp at hm hn; omega)
    (fun hmerge => by
      have := hmerge 0 1 (by decide) (by decide)
      omega)
    (fun n => n == 0) (by decide)

/-- The report, evaluated: the clean schema is free, the poisoned one is not —
and both answers are backed by the terms above, not by this `Bool`. -/
example : (loomVerdict (fun _ => 64)).isFree = true := rfl
example : pinnedVerdict.isFree = false := rfl

end Leanuweave.Spec
