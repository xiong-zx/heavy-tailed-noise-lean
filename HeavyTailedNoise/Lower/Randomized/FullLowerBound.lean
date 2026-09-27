import HeavyTailedNoise.Lower.Randomized.FinalBaseline
import HeavyTailedNoise.Lower.Randomized.RateAssembly
import HeavyTailedNoise.Lower.Gated.GatedHaarPublicRegime

/-!
Literal existing minimax baseline and the complete finite-q max lower rate.
The baseline and gated premises of the arithmetic composition are both
discharged by actual unrestricted entries. No alternative complexity,
stochastic assumption, or expected stopping budget is introduced.
These remain candidate sources until their complete native dependency check.
-/

namespace HeavyTailedNoise.RandomizedLift

open HeavyTailedNoise.Fradin
open scoped ENNReal
noncomputable section
set_option autoImplicit false
universe u

theorem baseline_minimax_complexity_lower_bound {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hA : 2 * physicalChainConstant ≤ L * Δ / ε ^ 2) :
    ENNReal.ofReal (physicalBaselineCoefficient p q *
      baselineRate (L * Δ / ε ^ 2) ((σ / ε) ^ tailExponent p) q) <
      (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal) := by
  apply dimensionUniformMinimaxComplexity_gt_of_excluded_real_budget
  · apply mul_nonneg (physicalBaselineCoefficient_pos p q).le
    apply baselineRate_nonneg
    · positivity
    · exact Real.rpow_nonneg (div_nonneg hσ hε.le) _
  · intro N hN
    exact baseline_refutes_dimension_uniform_guarantee N hp hq hL hΔ hε hσ hA hN

def fullPublicRateCoefficient (p q : ℝ) : ℝ :=
  combinedRateConstant (physicalBaselineCoefficient p q)

theorem fullPublicRateCoefficient_pos (p q : ℝ) : 0 < fullPublicRateCoefficient p q :=
  combinedRateConstant_pos (physicalBaselineCoefficient_pos p q)

/-- Complete lower rate with actual unrestricted baseline and gated inputs.
No hbaseline, hgeometry or chain-risk parameter occurs in this statement. -/
theorem full_minimax_complexity_lower_bound {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hA : 2 * physicalChainConstant ≤ L * Δ / ε ^ 2) :
    ENNReal.ofReal (fullPublicRateCoefficient p q *
      max (baselineRate (L * Δ / ε ^ 2) ((σ / ε) ^ tailExponent p) q)
        ((L * Δ / ε ^ 2) * (max 1 (σ / ε)) ^ 2)) <
      (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal) :=
  combined_minimax_lower_bound_of_baseline hp hq hL hΔ hε hσ
    (physicalBaselineCoefficient_pos p q)
    (baseline_minimax_complexity_lower_bound hp hq hL hΔ hε hσ hA)

theorem full_minimax_lower_bound_of_absolute_accuracy {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (haccuracy : ε ≤ physicalAccuracyConstant * Real.sqrt (L * Δ)) :
    ENNReal.ofReal (fullPublicRateCoefficient p q *
      max (baselineRate (L * Δ / ε ^ 2) ((σ / ε) ^ tailExponent p) q)
        ((L * Δ / ε ^ 2) * (max 1 (σ / ε)) ^ 2)) <
      (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal) :=
  full_minimax_complexity_lower_bound hp hq hL hΔ hε hσ
    (physical_accuracy_of_absolute_epsilon_bound hL hΔ hε haccuracy)

/-- The natural fixed-cap statement follows from the same literal infimum.
In particular, N=0 is excluded whenever it satisfies the displayed bound. -/
theorem full_lower_bound_refutes_response_budget {p q L Δ σ ε : ℝ} (N : ℕ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (haccuracy : ε ≤ physicalAccuracyConstant * Real.sqrt (L * Δ))
    (hN : (N : ℝ) ≤ fullPublicRateCoefficient p q *
      max (baselineRate (L * Δ / ε ^ 2) ((σ / ε) ^ tailExponent p) q)
        ((L * Δ / ε ^ 2) * (max 1 (σ / ε)) ^ 2)) :
    ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ L ε := by
  intro hguarantee
  have hlower := full_minimax_lower_bound_of_absolute_accuracy.{u}
    hp hq hL hΔ hε hσ haccuracy
  have hcomplex : dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε ≤ (N : ℕ∞) := by
    unfold dimensionUniformMinimaxComplexity
    exact iInf_le_of_le N (iInf_le _ hguarantee)
  have hcomplexReal : (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal) ≤
      (N : ENNReal) := by
    simpa only [ENat.toENNReal_coe] using ENat.toENNReal_le.mpr hcomplex
  have hbudgetReal : (N : ENNReal) ≤ ENNReal.ofReal
      (fullPublicRateCoefficient p q *
        max (baselineRate (L * Δ / ε ^ 2) ((σ / ε) ^ tailExponent p) q)
          ((L * Δ / ε ^ 2) * (max 1 (σ / ε)) ^ 2)) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hN
  exact not_lt_of_ge (hcomplexReal.trans hbudgetReal) hlower

/-- One absolute accuracy constant precedes p,q; their positive response
coefficient precedes every physical parameter and every algorithm. -/
theorem full_lower_bound_absolute_accuracy_and_fixed_parameter_constants :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ p q : ℝ, (1 < p ∧ p ≤ 2) → 1 ≤ q →
        ∃ c : ℝ, 0 < c ∧
          ∀ L Δ ε σ : ℝ, 0 < L → 0 < Δ → 0 < ε → 0 ≤ σ →
            ε ≤ c₀ * Real.sqrt (L * Δ) →
            ENNReal.ofReal (c *
              max (baselineRate (L * Δ / ε ^ 2) ((σ / ε) ^ tailExponent p) q)
                ((L * Δ / ε ^ 2) * (max 1 (σ / ε)) ^ 2)) <
              (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal) := by
  refine ⟨physicalAccuracyConstant, physicalAccuracyConstant_pos, ?_⟩
  intro p q hp hq
  refine ⟨fullPublicRateCoefficient p q, fullPublicRateCoefficient_pos p q, ?_⟩
  intro L Δ ε σ hL hΔ hε hσ haccuracy
  exact full_minimax_lower_bound_of_absolute_accuracy hp hq hL hΔ hε hσ haccuracy

end
end HeavyTailedNoise.RandomizedLift
