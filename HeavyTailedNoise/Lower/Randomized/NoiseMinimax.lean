import HeavyTailedNoise.Lower.Randomized.NoiseRisk
import HeavyTailedNoise.Lower.Gated.GatedHaarMinimaxComplexity

/-!
Numeric minimax corollary of NoiseRisk. The existing canonical complexity
definition is imported unchanged; separating this import layer does not
change the mathematical statement or its proof.
-/

namespace HeavyTailedNoise.RandomizedLift

open HeavyTailedNoise.Fradin
open scoped ENNReal
noncomputable section
set_option autoImplicit false
universe u

/-- A pure-noise term in the single dimension-uniform minimax model.
For zero or small noise the natural exclusion concerns only N=0. -/
theorem noisePair_minimax_complexity_lower_bound {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hgap : 8 * ε ^ 2 ≤ L * Δ) :
    ENNReal.ofReal (noiseRateConstant p * (σ / ε) ^ tailExponent p) <
      (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal) := by
  apply dimensionUniformMinimaxComplexity_gt_of_excluded_real_budget
  · exact mul_nonneg (noiseRateConstant_pos p).le (Real.rpow_nonneg (div_nonneg hσ hε.le) _)
  · intro N hN
    exact noisePair_refutes_dimension_uniform_guarantee hp hq hL hΔ hε hσ hgap
      (noiseRate_budget_implies_reveal_budget hp.1 hσ hε hN)

end
end HeavyTailedNoise.RandomizedLift
