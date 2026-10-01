import Mathlib.Probability.Moments.SubGaussian

/-! Hoeffding exponential contraction for a bounded variable with negative mean. -/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- A bounded variable with negative mean has a contracting exponential
moment.  The explicit coefficient is Hoeffding's half-range squared. -/
theorem bounded_negativeDrift_mgf_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (χ : Ω → ℝ) (hχ : Measurable χ)
    (C δ lam : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hlam : 0 ≤ lam)
    (hbound : ∀ ω, |χ ω| ≤ C)
    (hdrift : (∫ ω, χ ω ∂μ) ≤ -δ) :
    mgf χ μ lam ≤
      Real.exp (((((‖C - -C‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * lam ^ 2 / 2) -
        lam * δ) := by
  have hmem : ∀ᵐ ω ∂μ, χ ω ∈ Set.Icc (-C) C :=
    Filter.Eventually.of_forall fun ω =>
      (abs_le.mp (hbound ω))
  let c : ℝ≥0 := (‖C - -C‖₊ / 2) ^ 2
  have hsub : HasSubgaussianMGF
      (fun ω => χ ω - (∫ z, χ z ∂μ)) c μ :=
    hasSubgaussianMGF_of_mem_Icc hχ.aemeasurable hmem
  have hshift : mgf χ μ lam =
      mgf (fun ω => χ ω - (∫ z, χ z ∂μ)) μ lam *
        Real.exp (lam * (∫ z, χ z ∂μ)) := by
    have h := mgf_add_const (X := fun ω => χ ω - (∫ z, χ z ∂μ))
      (μ := μ) (t := lam) (∫ z, χ z ∂μ)
    simpa only [sub_add_cancel] using h
  have hmean : lam * (∫ z, χ z ∂μ) ≤ -lam * δ := by
    nlinarith [mul_le_mul_of_nonneg_left hdrift hlam]
  calc
    mgf χ μ lam =
        mgf (fun ω => χ ω - (∫ z, χ z ∂μ)) μ lam *
          Real.exp (lam * (∫ z, χ z ∂μ)) := hshift
    _ ≤ Real.exp ((c : ℝ) * lam ^ 2 / 2) *
          Real.exp (lam * (∫ z, χ z ∂μ)) := by
            exact mul_le_mul_of_nonneg_right (hsub.mgf_le lam)
              (Real.exp_nonneg _)
    _ ≤ Real.exp ((c : ℝ) * lam ^ 2 / 2) *
          Real.exp (-lam * δ) := by
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmean)
              (Real.exp_nonneg _)
    _ = Real.exp (((c : ℝ) * lam ^ 2 / 2) - lam * δ) := by
          rw [← Real.exp_add]
          ring

end

end HeavyTailedNoise.UpperK1
