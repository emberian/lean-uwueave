/-
# Uwueave.EvidenceGraph — structured evidence documents

`DerivedDocument.EvidenceDoc` faithfully stores result evidence, but it is a
flat set of three node constructors.  This module adds the missing structural
rung: candidates, sources, obligations, and certificates are distinct typed
vertices, while attribution, owing, and discharge are typed edges.

The graph remains a state-based CRDT.  Both vertex and edge sets are grow-only,
the encoder preserves joins, and endpoint wellformedness is I-confluent.  The
old flat document is recovered by a forgetful join homomorphism, so this module
refines rather than replaces `DerivedDocument`.

The edge orientation is rank-decreasing:

    candidate ─attributed→ source ─owes→ obligation
    certificate ─discharges──────────→ obligation

Thus the structural layer is DAG-like by construction.  No cryptographic or
content-addressing claim is made: node identities remain the structured data
shown in their constructors.
-/
import Uwueave.DerivedDocument

namespace Uwueave.EvidenceGraph

open Uwueave Uwueave.Catalog

/-! ## 1. Typed vertices, typed edges, and merge -/

/-- The four sorts of vertex in an evidence graph.  A candidate retains its
source in its identity, as it did in `Evidence.ResultEvidence`; the source also
has its own vertex so attribution is now an edge rather than packed metadata. -/
inductive Node (α : Type) : Type where
  | candidate (value : α) (source : Evidence.Source)
  | source (source : Evidence.Source)
  | obligation (source : Evidence.Source)
  | certificate (source : Evidence.Source)
  deriving DecidableEq

/-- The only well-typed edge shapes.  `owes` records that an obligation is
active; the obligation vertex may remain after a certificate discharges it. -/
inductive Edge (α : Type) : Type where
  | attributed (value : α) (source : Evidence.Source)
  | owes (source : Evidence.Source)
  | discharges (source : Evidence.Source)
  deriving DecidableEq

/-- The source endpoint of a typed evidence edge. -/
def edgeFrom {α : Type} : Edge α → Node α
  | .attributed a o => .candidate a o
  | .owes o => .source o
  | .discharges o => .certificate o

/-- The target endpoint of a typed evidence edge. -/
def edgeTo {α : Type} : Edge α → Node α
  | .attributed _ o => .source o
  | .owes o => .obligation o
  | .discharges o => .obligation o

/-- A rank witnessing the graph's acyclic orientation. -/
def nodeRank {α : Type} : Node α → Nat
  | .candidate .. => 2
  | .source .. => 1
  | .certificate .. => 1
  | .obligation .. => 0

/-- Every permitted edge strictly descends the vertex rank. -/
theorem edge_rank_descends {α : Type} (e : Edge α) :
    nodeRank (edgeTo e) < nodeRank (edgeFrom e) := by
  cases e <;> simp [edgeFrom, edgeTo, nodeRank]

/-- A typed evidence graph is a grow-only vertex set paired with a grow-only
edge set. -/
abbrev Graph (α : Type) : Type := GSet (Node α) × GSet (Edge α)

/-- Vertex membership. -/
abbrev nodes {α : Type} (g : Graph α) : GSet (Node α) := g.1

/-- Edge membership. -/
abbrev edges {α : Type} (g : Graph α) : GSet (Edge α) := g.2

/-- Graph merge is inherited componentwise from the two G-Sets. -/
example {α : Type} : MergeState (Graph α) := inferInstance

theorem nodes_merge {α : Type} (g h : Graph α) :
    nodes (g ⊔ h) = nodes g ⊔ nodes h := rfl

theorem edges_merge {α : Type} (g h : Graph α) :
    edges (g ⊔ h) = edges g ⊔ edges h := rfl

/-! ## 2. Structural wellformedness -/

/-- Every present edge has both of its typed endpoints. -/
def WellFormed {α : Type} (g : Graph α) : Prop :=
  ∀ e, edges g e = true →
    nodes g (edgeFrom e) = true ∧ nodes g (edgeTo e) = true

/-- Endpoint integrity is preserved by graph union.  An edge in the union came
from one legal replica, and both of its endpoints grow with that replica. -/
theorem wellFormed_iconfluent {α : Type} :
    IConfluent (S := Graph α) WellFormed := by
  intro x y hx hy e he
  rcases (Holes.gset_mem_or (edges x) (edges y) e).mp he with hxe | hye
  · obtain ⟨hfrom, hto⟩ := hx e hxe
    constructor
    · show (nodes x (edgeFrom e) || nodes y (edgeFrom e)) = true
      simp [hfrom]
    · show (nodes x (edgeTo e) || nodes y (edgeTo e)) = true
      simp [hto]
  · obtain ⟨hfrom, hto⟩ := hy e hye
    constructor
    · show (nodes x (edgeFrom e) || nodes y (edgeFrom e)) = true
      simp [hfrom]
    · show (nodes x (edgeTo e) || nodes y (edgeTo e)) = true
      simp [hto]

/-! ## 3. Encoding result evidence -/

/-- Sources mentioned by candidates.  This is noncomputable for the same
reason as `Evidence.values`: the existential ranges over an arbitrary carrier. -/
noncomputable def candidateSources {α : Type}
    (e : Evidence.ResultEvidence α) : GSet Evidence.Source :=
  fun o => Holes.truth (∃ a, Evidence.candidates e (a, o) = true)

theorem candidateSources_mem {α : Type} (e : Evidence.ResultEvidence α)
    (o : Evidence.Source) :
    candidateSources e o = true ↔ ∃ a, Evidence.candidates e (a, o) = true :=
  Holes.truth_eq_true

/-- Candidate-source projection preserves union. -/
theorem candidateSources_merge {α : Type}
    (e₁ e₂ : Evidence.ResultEvidence α) :
    candidateSources (e₁ ⊔ e₂) = candidateSources e₁ ⊔ candidateSources e₂ := by
  apply Holes.gset_ext
  intro o
  rw [Holes.gset_mem_or]
  simp only [candidateSources_mem]
  constructor
  · rintro ⟨a, ha⟩
    have ha' :
        (Evidence.candidates e₁ (a, o) || Evidence.candidates e₂ (a, o)) = true := ha
    rcases (Bool.or_eq_true _ _).mp ha' with h | h
    · exact Or.inl ⟨a, h⟩
    · exact Or.inr ⟨a, h⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · refine ⟨a, ?_⟩
      show (Evidence.candidates e₁ (a, o) || Evidence.candidates e₂ (a, o)) = true
      simp [ha]
    · refine ⟨a, ?_⟩
      show (Evidence.candidates e₁ (a, o) || Evidence.candidates e₂ (a, o)) = true
      simp [ha]

/-- **The structured encoding.** Each fact contributes its vertex, the
vertices needed to type its edge, and that edge.  An obligation vertex is kept
when either an active obligation or its closing certificate exists; the
`owes` edge is what distinguishes an active obligation from a discharged one. -/
noncomputable def encodeEvidenceGraph {α : Type}
    (e : Evidence.ResultEvidence α) : Graph α :=
  (fun n => match n with
    | .candidate a o => Evidence.candidates e (a, o)
    | .source o =>
        candidateSources e o || Evidence.obligations e o || Evidence.certificates e o
    | .obligation o => Evidence.obligations e o || Evidence.certificates e o
    | .certificate o => Evidence.certificates e o,
   fun edge => match edge with
    | .attributed a o => Evidence.candidates e (a, o)
    | .owes o => Evidence.obligations e o
    | .discharges o => Evidence.certificates e o)

/-- Every encoded evidence value is structurally wellformed. -/
theorem encodeEvidenceGraph_wellFormed {α : Type}
    (e : Evidence.ResultEvidence α) : WellFormed (encodeEvidenceGraph e) := by
  intro edge hedge
  cases edge with
  | attributed a o =>
      change Evidence.candidates e (a, o) = true at hedge
      have hs : candidateSources e o = true :=
        (candidateSources_mem e o).2 ⟨a, hedge⟩
      constructor
      · change Evidence.candidates e (a, o) = true
        exact hedge
      · change (candidateSources e o || Evidence.obligations e o ||
            Evidence.certificates e o) = true
        simp [hs]
  | owes o =>
      change Evidence.obligations e o = true at hedge
      constructor
      · change (candidateSources e o || Evidence.obligations e o ||
            Evidence.certificates e o) = true
        simp [hedge]
      · change (Evidence.obligations e o || Evidence.certificates e o) = true
        simp [hedge]
  | discharges o =>
      change Evidence.certificates e o = true at hedge
      constructor
      · change Evidence.certificates e o = true
        exact hedge
      · change (Evidence.obligations e o || Evidence.certificates e o) = true
        simp [hedge]

/-- **Encoding commutes with merge.** Nodes and edges may be encoded before or
after replica union with exactly the same graph. -/
theorem encodeEvidenceGraph_merge {α : Type}
    (e₁ e₂ : Evidence.ResultEvidence α) :
    encodeEvidenceGraph (e₁ ⊔ e₂) =
      encodeEvidenceGraph e₁ ⊔ encodeEvidenceGraph e₂ := by
  apply Prod.ext
  · funext n
    cases n with
    | candidate a o => rfl
    | source o =>
        change (candidateSources (e₁ ⊔ e₂) o ||
                (Evidence.obligations e₁ o || Evidence.obligations e₂ o) ||
                (Evidence.certificates e₁ o || Evidence.certificates e₂ o)) =
              ((candidateSources e₁ o || Evidence.obligations e₁ o ||
                Evidence.certificates e₁ o) ||
               (candidateSources e₂ o || Evidence.obligations e₂ o ||
                Evidence.certificates e₂ o))
        rw [candidateSources_merge]
        show (((candidateSources e₁ o || candidateSources e₂ o) ||
              (Evidence.obligations e₁ o || Evidence.obligations e₂ o)) ||
              (Evidence.certificates e₁ o || Evidence.certificates e₂ o)) =
            ((candidateSources e₁ o || Evidence.obligations e₁ o ||
              Evidence.certificates e₁ o) ||
             (candidateSources e₂ o || Evidence.obligations e₂ o ||
              Evidence.certificates e₂ o))
        ac_rfl
    | obligation o =>
        show ((Evidence.obligations e₁ o || Evidence.obligations e₂ o) ||
              (Evidence.certificates e₁ o || Evidence.certificates e₂ o)) =
            ((Evidence.obligations e₁ o || Evidence.certificates e₁ o) ||
             (Evidence.obligations e₂ o || Evidence.certificates e₂ o))
        ac_rfl
    | certificate o => rfl
  · funext edge
    cases edge <;> rfl

theorem encodeEvidenceGraph_joinHom {α : Type} :
    JoinHom (encodeEvidenceGraph (α := α)) :=
  encodeEvidenceGraph_merge

/-! ## 4. The old flat document is the forgetful projection -/

/-- Forget graph-only structure.  Candidate and certificate facts are read
from their vertices; an outstanding obligation is read from its `owes` edge,
which avoids confusing it with the retained target of a discharge edge. -/
def forgetEvidenceGraph {α : Type} (g : Graph α) :
    DerivedDocument.EvidenceDoc α
  | .cand a o => nodes g (.candidate a o)
  | .owed o => edges g (.owes o)
  | .sealedBy o => nodes g (.certificate o)

theorem forgetEvidenceGraph_merge {α : Type} (g h : Graph α) :
    forgetEvidenceGraph (g ⊔ h) =
      forgetEvidenceGraph g ⊔ forgetEvidenceGraph h := by
  funext n
  cases n <;> rfl

theorem forgetEvidenceGraph_joinHom {α : Type} :
    JoinHom (forgetEvidenceGraph (α := α)) :=
  forgetEvidenceGraph_merge

/-- Forgetting the structured encoding recovers the existing flat encoding on
the nose. -/
theorem forget_encodeEvidenceGraph {α : Type}
    (e : Evidence.ResultEvidence α) :
    forgetEvidenceGraph (encodeEvidenceGraph e) =
      DerivedDocument.encodeEvidence e := by
  funext n
  cases n <;> rfl

/-- The old encoder factors through the graph encoder by a forgetful join
homomorphism. -/
theorem flat_encodeEvidence_is_projection {α : Type} :
    DerivedDocument.encodeEvidence (α := α) =
      forgetEvidenceGraph ∘ encodeEvidenceGraph := by
  funext e
  exact (forget_encodeEvidenceGraph e).symm

/-! ## 5. A real fork and a malformed graph -/

/-- The graph encoding of the library's closed two-candidate fork. -/
noncomputable def forkedEvidenceGraph : Graph Holes.Val :=
  encodeEvidenceGraph Evidence.forkedClosedW

/-- The fork is a pair of distinct candidate branches with explicit
attribution edges to two present source vertices. -/
theorem forked_evidence_has_two_sourced_branches :
    nodes forkedEvidenceGraph (.candidate 47 Evidence.alice) = true
      ∧ nodes forkedEvidenceGraph (.candidate 49 Evidence.bob) = true
      ∧ (Node.candidate 47 Evidence.alice : Node Holes.Val) ≠
          Node.candidate 49 Evidence.bob
      ∧ edges forkedEvidenceGraph (.attributed 47 Evidence.alice) = true
      ∧ edges forkedEvidenceGraph (.attributed 49 Evidence.bob) = true
      ∧ nodes forkedEvidenceGraph (.source Evidence.alice) = true
      ∧ nodes forkedEvidenceGraph (.source Evidence.bob) = true := by
  have hw := encodeEvidenceGraph_wellFormed Evidence.forkedClosedW
  have ha : edges forkedEvidenceGraph (.attributed 47 Evidence.alice) = true := by
    decide
  have hb : edges forkedEvidenceGraph (.attributed 49 Evidence.bob) = true := by
    decide
  have hwa := hw (.attributed 47 Evidence.alice) ha
  have hwb := hw (.attributed 49 Evidence.bob) hb
  exact ⟨by decide, by decide, by decide, ha, hb, hwa.2, hwb.2⟩

/-- The closed fork also contains explicit certificate-to-obligation discharge
edges for both sources; closure is represented structurally rather than by a
flat certificate bit alone. -/
theorem forked_evidence_has_explicit_discharges :
    nodes forkedEvidenceGraph (.certificate Evidence.alice) = true
      ∧ nodes forkedEvidenceGraph (.obligation Evidence.alice) = true
      ∧ edges forkedEvidenceGraph (.discharges Evidence.alice) = true
      ∧ nodes forkedEvidenceGraph (.certificate Evidence.bob) = true
      ∧ nodes forkedEvidenceGraph (.obligation Evidence.bob) = true
      ∧ edges forkedEvidenceGraph (.discharges Evidence.bob) = true
      ∧ edgeFrom (Edge.discharges Evidence.alice : Edge Holes.Val) =
          .certificate Evidence.alice
      ∧ edgeTo (Edge.discharges Evidence.alice : Edge Holes.Val) =
          .obligation Evidence.alice := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl, rfl⟩

/-- One dangling attribution edge and no vertices. -/
def danglingAttribution : Graph Holes.Val :=
  (fun _ => false,
   fun e => decide (e = Edge.attributed 47 Evidence.alice))

/-- **Wellformedness is load-bearing.** The edge type prevents a category
mistake, but does not by itself install endpoints: this concrete graph carries
an attribution edge whose candidate vertex is absent, and is therefore
rejected by `WellFormed`. -/
theorem danglingAttribution_is_malformed :
    edges danglingAttribution (.attributed 47 Evidence.alice) = true
      ∧ nodes danglingAttribution (.candidate 47 Evidence.alice) = false
      ∧ ¬ WellFormed danglingAttribution := by
  refine ⟨by decide, rfl, ?_⟩
  intro hw
  have h := hw (.attributed 47 Evidence.alice) (by decide)
  exact Bool.noConfusion h.1

end Uwueave.EvidenceGraph
