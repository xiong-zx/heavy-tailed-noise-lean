import HeavyTailedNoise
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Print the complete lower, gated and Fradin theorem signatures and reject dependencies outside
the three standard logical axioms permitted by this package's public API.
-/

#check HeavyTailedNoise.gatedHaar_fixed_prior_average_risk_lower_bound
#check HeavyTailedNoise.gatedHaar_bad_legal_instance
#check HeavyTailedNoise.gatedHaar_refutes_dimension_uniform_guarantee
#check HeavyTailedNoise.gatedHaar_minimax_complexity_gt_response_budget
#check HeavyTailedNoise.gatedHaar_minimax_complexity_lower_bound
#check HeavyTailedNoise.gatedHaar_minimax_complexity_absolute_constants
#check HeavyTailedNoise.Fradin.original_theorem31_lower_bound
#check HeavyTailedNoise.Fradin.original_theorem31_constants
#check HeavyTailedNoise.Fradin.observedSourceRoundComplexity_eq
#check HeavyTailedNoise.Fradin.source_coefficient_realization
#check HeavyTailedNoise.RandomizedLift.actualStoppedPosterior_residual_reflections
#check HeavyTailedNoise.RandomizedLift.unscaledHaar_averageRisk_ge
#check HeavyTailedNoise.RandomizedLift.baseline_public_dimension_bad_instance
#check HeavyTailedNoise.RandomizedLift.baseline_minimax_complexity_lower_bound
#check HeavyTailedNoise.RandomizedLift.full_minimax_lower_bound_of_absolute_accuracy
#check HeavyTailedNoise.RandomizedLift.full_lower_bound_refutes_response_budget
#check HeavyTailedNoise.RandomizedLift.full_lower_bound_absolute_accuracy_and_fixed_parameter_constants
#check HeavyTailedNoise.RandomizedLift.noisePair_minimax_complexity_lower_bound

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let publicTheorems : Array Name := #[
    ``HeavyTailedNoise.gatedHaar_fixed_prior_average_risk_lower_bound,
    ``HeavyTailedNoise.gatedHaar_bad_legal_instance,
    ``HeavyTailedNoise.gatedHaar_refutes_dimension_uniform_guarantee,
    ``HeavyTailedNoise.gatedHaar_minimax_complexity_gt_response_budget,
    ``HeavyTailedNoise.gatedHaar_minimax_complexity_lower_bound,
    ``HeavyTailedNoise.gatedHaar_minimax_complexity_absolute_constants,
    ``HeavyTailedNoise.Fradin.original_theorem31_lower_bound,
    ``HeavyTailedNoise.Fradin.original_theorem31_constants,
    ``HeavyTailedNoise.Fradin.observedSourceRoundComplexity_eq,
    ``HeavyTailedNoise.Fradin.source_coefficient_realization,
    ``HeavyTailedNoise.RandomizedLift.actualStoppedPosterior_residual_reflections,
    ``HeavyTailedNoise.RandomizedLift.unscaledHaar_averageRisk_ge,
    ``HeavyTailedNoise.RandomizedLift.baseline_public_dimension_bad_instance,
    ``HeavyTailedNoise.RandomizedLift.baseline_minimax_complexity_lower_bound,
    ``HeavyTailedNoise.RandomizedLift.full_minimax_lower_bound_of_absolute_accuracy,
    ``HeavyTailedNoise.RandomizedLift.full_lower_bound_refutes_response_budget,
    ``HeavyTailedNoise.RandomizedLift.full_lower_bound_absolute_accuracy_and_fixed_parameter_constants,
    ``HeavyTailedNoise.RandomizedLift.noisePair_minimax_complexity_lower_bound]
  for theoremName in publicTheorems do
    let used ← Lean.collectAxioms theoremName
    let forbidden := used.filter (fun axiomName => !allowed.contains axiomName)
    unless forbidden.isEmpty do
      throwError m!"{theoremName} uses forbidden axioms: {forbidden}"
    logInfo m!"{theoremName}: {used}"
