import Uwueave.Repair

open Uwueave
open Uwueave.Repair

/-- U-0123 exposes the exact admitted-feed rewrite, proves preservation is
compositional, and includes both a preserved production transport and a
concrete changed-type refutation. -/
theorem debtClosure_U_0123 :
    (∀ {P Q : Promise} (repair : Repair P Q)
        (kept : repair.relation.demandEquivalenceKept = true)
        (state : P.State) (demand : P.Demand),
      Q.admits (repair.transform state)
          ((repair.observation kept).toDemand demand) ↔
        P.admits state demand)
    ∧ (∀ {P Q R : Promise} (first : Repair P Q) (second : Repair Q R),
      first.PreservesDemandEquiv → second.PreservesDemandEquiv →
        (first.comp second).PreservesDemandEquiv)
    ∧ fork.PreservesDemandEquiv
    ∧ changeDemandType.RefutesDemandEquiv
    ∧ emptyDemandPromise.Singular
    ∧ unitDemandPromise.Singular
    ∧ changeDemandType.relation.singularObservation = true
    ∧ changeDemandType.relation.demandEquivalenceKept = false
    ∧ changeDemandType.RefutesDemandEquiv := by
  exact
    ⟨Repair.observation_transport,
      Repair.comp_preserves_demand_equiv,
      fork_preserves_demand_equiv,
      changeDemandType_refutes_demand_equiv,
      changed_demand_type_but_both_singular.1,
      changed_demand_type_but_both_singular.2.1,
      changed_demand_type_but_both_singular.2.2.1,
      changed_demand_type_but_both_singular.2.2.2.1,
      changed_demand_type_but_both_singular.2.2.2.2⟩

#print axioms debtClosure_U_0123
