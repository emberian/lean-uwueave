/-
# Uwueave.Preo.ArtifactDiagnostics — optional first-order pretty printers

The durable validator needs structural data and decidable equality, but it does
not print artifacts. Keeping all derived Repr instances here preserves the
existing public instance names for callers of Uwueave.Preo.Artifact without
placing their generated code in the runtime validation closure.
-/
import Uwueave.Preo.ArtifactData

namespace Uwueave.Preo.Artifact

deriving instance Repr for DeclarationId
deriving instance Repr for FieldId
deriving instance Repr for InvariantId
deriving instance Repr for FutureId
deriving instance Repr for SessionId
deriving instance Repr for PlanId
deriving instance Repr for BudgetId
deriving instance Repr for VerdictEvidence
deriving instance Repr for Currency
deriving instance Repr for EvidenceKey
deriving instance Repr for DemandArtifact
deriving instance Repr for OriginArtifact
deriving instance Repr for ObligationArtifact
deriving instance Repr for DeclarationArtifact
deriving instance Repr for FieldArtifact
deriving instance Repr for InvariantArtifact
deriving instance Repr for FutureArtifact
deriving instance Repr for SessionArtifact
deriving instance Repr for PlanArtifact
deriving instance Repr for BudgetArtifact
deriving instance Repr for Artifact
deriving instance Repr for DeclarationArtifactEncoding
deriving instance Repr for FieldArtifactEncoding
deriving instance Repr for InvariantArtifactEncoding
deriving instance Repr for FutureArtifactEncoding
deriving instance Repr for SessionArtifactEncoding
deriving instance Repr for PlanArtifactEncoding
deriving instance Repr for BudgetArtifactEncoding
deriving instance Repr for ArtifactEncoding

end Uwueave.Preo.Artifact
