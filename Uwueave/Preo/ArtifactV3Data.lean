/-
# Uwueave.Preo.ArtifactV3Data — neutral typed-query artifact rows

V3 extends, rather than mutates, the V2 artifact projection.  The `base` field
is the exact V2 `ArtifactEncoding`; query, result, and certificate rows are
append-only first-order data.  This leaf imports no proof-bearing source,
diagnostic renderer, example, or host projection.

All cross-row identities have distinct wrapper types in memory.  The durable
wire projects those wrappers to naturals, but the Lean API cannot accidentally
interchange a schema, query, result, program, certificate, or world identity.
-/
import Uwueave.Preo.ArtifactData

namespace Uwueave.Preo.ArtifactV3

open Uwueave.Preo.Artifact

set_option autoImplicit false

/-! ## Stable identities -/

structure SchemaId where
  value : Nat
  deriving DecidableEq

structure QueryId where
  value : Nat
  deriving DecidableEq

structure ResultId where
  value : Nat
  deriving DecidableEq

structure ProgramId where
  value : Nat
  deriving DecidableEq

structure CertificateId where
  value : Nat
  deriving DecidableEq

structure WorldId where
  value : Nat
  deriving DecidableEq

structure ResolutionId where
  value : Nat
  deriving DecidableEq

structure SurfaceId where
  value : Nat
  deriving DecidableEq

structure ReasonId where
  value : Nat
  deriving DecidableEq

/-! ## Query rows -/

inductive HoleKind where
  | field
  | opaque
  deriving DecidableEq

/-- Exact syntax-tree location and referenced field of a typed query hole. -/
structure HoleRow where
  path : List Nat
  field : FieldId
  kind : HoleKind
  deriving DecidableEq

/-- Positive analysis evidence exported by a checked state program.  Absence
means only that the corresponding proof was not supplied; it is not a negative
semantic claim. -/
inductive AnalysisTag where
  | mergeSafe
  | monotoneSafe
  deriving DecidableEq

/-- A checked typed query, projected to stable identities and exact structural
dependencies.  `result` is the result row which implements this query. -/
structure QueryRow where
  id : QueryId
  schema : SchemaId
  result : ResultId
  program : ProgramId
  reads : List FieldId
  holes : List HoleRow
  analyses : List AnalysisTag
  deriving DecidableEq

/-! ## Result rows -/

/-- First-order identity of the checked resolution syntax. -/
inductive ResolutionRow where
  | preserveFork
  | named (id : ResolutionId)
  deriving DecidableEq

/-- Value-erased six-status result metadata. -/
inductive StatusShape where
  | exact
  | provisional
  | forkedClosed
  | forkedOpen
  | absent
  | pending
  deriving DecidableEq

/-- Independent first-order visibility metadata.  Opaque reasons are stable
identities, not host diagnostic strings. -/
inductive VisibilityRow where
  | inspectable
  | opaque (reason : ReasonId)
  deriving DecidableEq

/-- Independent first-order disclosure metadata for the exact result branch. -/
inductive DisclosureRow where
  | shown
  | hidden (reason : ReasonId)
  deriving DecidableEq

/-- One checked result at its exact query/future/policy boundary.  `effect` is
the canonical list representation of the declaration's certified six-status
downset; `status` is the exact value-erased status of this result. -/
structure ResultRow where
  id : ResultId
  query : QueryId
  future : FutureId
  resolution : ResolutionRow
  surface : SurfaceId
  status : StatusShape
  effect : List StatusShape
  visibility : VisibilityRow
  /-- `none` means no selected result value exists at this status.  A present
  value is emitted only from an explicit selected-value witness. -/
  disclosure : Option DisclosureRow
  deriving DecidableEq

/-! ## Certificate rows -/

/-- Stable identity of a checked certificate at one exact world for one exact
future.  No accepted predicate or proof is reconstructed from this row. -/
structure CertificateRow where
  id : CertificateId
  future : FutureId
  world : WorldId
  deriving DecidableEq

/-! ## Append-only V3 aggregate -/

structure ArtifactV3Encoding where
  base : ArtifactEncoding
  /-- Stable identity of the one typed schema used by the query rows. -/
  schema : SchemaId
  /-- Identity registry only.  Membership never reconstitutes a world model or
  a `WorldIndex`. -/
  worlds : List WorldId
  queries : List QueryRow
  results : List ResultRow
  certificates : List CertificateRow
  deriving DecidableEq

/-! ## Honest V3 limits

`ProjectionV3.validate` requires the world registry and query/result/
certificate rows to be strictly increasing by their stable IDs, making the
extension representation canonical under row permutation.  Checked appenders
require this ordering as a proof premise.

Certificate rows intentionally identify only a certificate, future, and
world.  They cannot express which result/query consumed that certificate; a
future wire version must add that reference before decoded validation can
check it.  Likewise resolution, surface, and reason IDs retain stable manifest
identity but this version carries no name registries from which to detect two
authored names assigned the same number. -/

end Uwueave.Preo.ArtifactV3
