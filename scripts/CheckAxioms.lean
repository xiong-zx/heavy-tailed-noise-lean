import HeavyTailedNoise
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Print the complete lower, upper, tight-rate, gated and Fradin theorem signatures and reject dependencies outside
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
#check HeavyTailedNoise.UpperK1.Admissible.paperSchedule_average_actual_estimator_error_le
#check HeavyTailedNoise.UpperK1.Admissible.strict_k1_shared_batch_ema_upper
#check HeavyTailedNoise.UpperK1.upperRateConstant_pos
#check HeavyTailedNoise.UpperK1.paper_upper_shape_le_two_full_lower_shape
#check HeavyTailedNoise.UpperK1.full_lower_shape_le_two_paper_upper_shape
#check HeavyTailedNoise.strictK1_same_model_tight_rate
#check HeavyTailedNoise.strictK1_same_model_refutes_response_budget
#check HeavyTailedNoise.UpperK1.risk_privateLiftAlgorithm_eq
#check HeavyTailedNoise.UpperK1.strict_k1_shared_batch_ema_uniform_guarantee
#check HeavyTailedNoise.UpperK1.strict_k1_shared_batch_ema_minimax_le_responseCount
#check HeavyTailedNoise.UpperK1.strict_k1_shared_batch_ema_minimax_le_rate
#check HeavyTailedNoise.strictK1_same_model_minimax_tight_rate

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
    ``HeavyTailedNoise.RandomizedLift.noisePair_minimax_complexity_lower_bound,
    ``HeavyTailedNoise.UpperK1.Admissible.paperSchedule_average_actual_estimator_error_le,
    ``HeavyTailedNoise.UpperK1.Admissible.strict_k1_shared_batch_ema_upper,
    ``HeavyTailedNoise.UpperK1.upperRateConstant_pos,
    ``HeavyTailedNoise.UpperK1.paper_upper_shape_le_two_full_lower_shape,
    ``HeavyTailedNoise.UpperK1.full_lower_shape_le_two_paper_upper_shape,
    ``HeavyTailedNoise.strictK1_same_model_tight_rate,
    ``HeavyTailedNoise.strictK1_same_model_refutes_response_budget,
    ``HeavyTailedNoise.UpperK1.risk_privateLiftAlgorithm_eq,
    ``HeavyTailedNoise.UpperK1.strict_k1_shared_batch_ema_uniform_guarantee,
    ``HeavyTailedNoise.UpperK1.strict_k1_shared_batch_ema_minimax_le_responseCount,
    ``HeavyTailedNoise.UpperK1.strict_k1_shared_batch_ema_minimax_le_rate,
    ``HeavyTailedNoise.strictK1_same_model_minimax_tight_rate]
  for theoremName in publicTheorems do
    let used ← Lean.collectAxioms theoremName
    let forbidden := used.filter (fun axiomName => !allowed.contains axiomName)
    unless forbidden.isEmpty do
      throwError m!"{theoremName} uses forbidden axioms: {forbidden}"
    logInfo m!"{theoremName}: {used}"
