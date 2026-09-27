import HeavyTailedNoise.Lower.Randomized.ActualRisk
import HeavyTailedNoise.Lower.Randomized.BaselineBudget

/-!
Unrestricted physical baseline entry. The actual preselected-frame risk
theorem discharges the geometric input. Public parameters and the natural
response budget select the hard dimension before all private spaces and
algorithms. There is no stochastic or chain-risk premise in these entries.
These are candidate sources until the complete native dependency check.
-/

namespace HeavyTailedNoise.RandomizedLift

open HeavyTailedNoise.Fradin MeasureTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false
universe u

/-- One public dimension works for every arbitrary measurable-private
algorithm. Its output may be unqueried, and N counts responses only. -/
theorem baseline_public_dimension_bad_instance {p q L Δ σ ε : ℝ} (N : ℕ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hA : 2 * physicalChainConstant ≤ L * Δ / ε ^ 2)
    (hN : (N : ℝ) ≤ physicalBaselineCoefficient p q *
      ((L * Δ / ε ^ 2) + (σ / ε) ^ tailExponent p +
        (L * Δ / ε ^ 2) * ((σ / ε) ^ tailExponent p) ^ (1 / q))) :
    ∃ d : ℕ, 0 < d ∧
      ∀ (Private : Type u) (privateSpace : MeasurableSpace Private)
        (A : @RandomAlgorithm d N Private privateSpace),
        ∃ I : Admissible d Bool p q Δ σ L,
          ENNReal.ofReal ε <
            @risk d N Bool inferInstance Private privateSpace p q Δ σ L I A := by
  rcases physical_baseline_budget_dichotomy N hA (div_nonneg hσ hε.le) hp.1 hq hN with
    hlarge | hnoise
  · let θ := physicalTheta σ ε p hp.1
    let T := physicalChainLength L Δ ε θ q
    let d := geometricDimension (liftRadius T) T N
    have hT : 0 < T := hlarge.2.1
    have hbudget : 8 * (N : ℝ) * (θ : ℝ) ≤ (T : ℝ) := hlarge.2.2
    have hdgt : T + N < d := geometricDimension_gt (liftRadius T) T N
    have hd : 0 < d := by omega
    have hTd : T ≤ d := by omega
    let μ := preselectedOrthonormalFrameLaw d T hTd
    refine ⟨d, hd, ?_⟩
    intro Private privateSpace A
    letI : MeasurableSpace Private := privateSpace
    let instanceAt := fun V : {U : Fin T → Point d // Orthonormal ℝ U} =>
      physicalAdmissible hd hp hq hL hΔ hε hσ V.1 V.2 hT
    have haverage : ENNReal.ofReal ε < ∫⁻ V, risk (instanceAt V) A ∂μ := by
      apply physical_averageRisk_gt_of_unscaled_average hd hp hq hL hΔ hε hσ hT μ
        (fun V => V.1) (fun V => V.2) ?_ A
      intro B
      exact unscaledHaar_averageRisk_gt_eighth hT hTd θ B le_rfl hbudget
    obtain ⟨V, hV⟩ := bad_orientation_of_average μ instanceAt A haverage
    exact ⟨instanceAt V, hV⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro Private privateSpace A
    letI : MeasurableSpace Private := privateSpace
    exact noisePair_bad_instance hp hq hL hΔ hε hσ
      (physical_accuracy_implies_noise_gap hε hA)
      (noiseRate_budget_implies_reveal_budget hp.1 hσ hε hnoise) A

/-- Arbitrary randomized strict-K=1 exclusion, including N=0 and sigma=0.
The only regime restriction is the public absolute accuracy condition. -/
theorem baseline_refutes_dimension_uniform_guarantee {p q L Δ σ ε : ℝ} (N : ℕ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hA : 2 * physicalChainConstant ≤ L * Δ / ε ^ 2)
    (hN : (N : ℝ) ≤ physicalBaselineCoefficient p q *
      ((L * Δ / ε ^ 2) + (σ / ε) ^ tailExponent p +
        (L * Δ / ε ^ 2) * ((σ / ε) ^ tailExponent p) ^ (1 / q))) :
    ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ L ε := by
  obtain ⟨d, hd, hbad⟩ := baseline_public_dimension_bad_instance.{u}
    N hp hq hL hΔ hε hσ hA hN
  intro hguarantee
  obtain ⟨Private, privateSpace, A, hAall⟩ := hguarantee d hd
  obtain ⟨I, hI⟩ := hbad Private privateSpace A
  exact not_lt_of_ge (hAall Bool inferInstance I) hI

theorem baseline_refutes_of_absolute_accuracy {p q L Δ σ ε : ℝ} (N : ℕ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (haccuracy : ε ≤ physicalAccuracyConstant * Real.sqrt (L * Δ))
    (hN : (N : ℝ) ≤ physicalBaselineCoefficient p q *
      ((L * Δ / ε ^ 2) + (σ / ε) ^ tailExponent p +
        (L * Δ / ε ^ 2) * ((σ / ε) ^ tailExponent p) ^ (1 / q))) :
    ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ L ε :=
  baseline_refutes_dimension_uniform_guarantee N hp hq hL hΔ hε hσ
    (physical_accuracy_of_absolute_epsilon_bound hL hΔ hε haccuracy) hN

end
end HeavyTailedNoise.RandomizedLift
