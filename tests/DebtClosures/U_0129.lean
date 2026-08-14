import Uwueave.Repair

open Uwueave
open Uwueave.Repair

/-- U-0129 makes demand equivalence load-bearing rather than inferring it from
singularity. Fork preserves the demand/feed transport while losing singularity;
the changed-type repair keeps singularity while refuting that transport. -/
theorem debtClosure_U_0129 :
    fork.PreservesDemandEquiv
    ∧ fork.relation.demandEquivalenceKept = true
    ∧ fork.relation.singularObservation = false
    ∧ ¬ forkedRegisterPromise.Singular
    ∧ emptyDemandPromise.Singular
    ∧ unitDemandPromise.Singular
    ∧ changeDemandType.relation.demandEquivalenceKept = false
    ∧ changeDemandType.relation.singularObservation = true
    ∧ changeDemandType.RefutesDemandEquiv := by
  exact
    ⟨fork_observation_axes_are_independent.1,
      fork_observation_axes_are_independent.2.1,
      fork_observation_axes_are_independent.2.2.1,
      fork_observation_axes_are_independent.2.2.2,
      changed_demand_type_but_both_singular.1,
      changed_demand_type_but_both_singular.2.1,
      changed_demand_type_but_both_singular.2.2.2.1,
      changed_demand_type_but_both_singular.2.2.1,
      changed_demand_type_but_both_singular.2.2.2.2⟩

#print axioms debtClosure_U_0129
