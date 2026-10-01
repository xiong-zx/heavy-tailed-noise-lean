import Mathlib.Probability.Moments.SubGaussian

/-!
Integrating a fixed-history mgf bound against a nonnegative predictable
weight.  This is a product-measure lemma; it contains no oracle or algorithm.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory ProbabilityTheory

noncomputable section

theorem predictable_weighted_mgf_integral_le
    {History Batch : Type*}
    [MeasurableSpace History] [MeasurableSpace Batch]
    (μpast : Measure History) [SFinite μpast]
    (μbatch : Measure Batch) [IsProbabilityMeasure μbatch]
    (f : History → ℝ) (χ : History → Batch → ℝ)
    (lam r : ℝ)
    (hf_nonneg : ∀ H, 0 ≤ f H)
    (hf_int : Integrable f μpast)
    (hweighted_int : Integrable
      (fun z : History × Batch => f z.1 * Real.exp (lam * χ z.1 z.2))
      (μpast.prod μbatch))
    (hmgf : ∀ H, f H ≠ 0 → mgf (χ H) μbatch lam ≤ r) :
    (∫ z : History × Batch,
      f z.1 * Real.exp (lam * χ z.1 z.2) ∂μpast.prod μbatch) ≤
      r * ∫ H, f H ∂μpast := by
  have hinner (H : History) :
      (∫ batch : Batch, f H * Real.exp (lam * χ H batch) ∂μbatch) ≤
        f H * r := by
    by_cases hf : f H = 0
    · simp [hf]
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hmgf H hf) (hf_nonneg H)
  rw [integral_prod _ hweighted_int]
  calc
    (∫ H : History,
      ∫ batch : Batch, f H * Real.exp (lam * χ H batch) ∂μbatch ∂μpast) ≤
        ∫ H, f H * r ∂μpast := by
          exact integral_mono hweighted_int.integral_prod_left
            (hf_int.mul_const r) hinner
    _ = r * ∫ H, f H ∂μpast := by
          rw [integral_mul_const]
          ring

end

end HeavyTailedNoise.UpperK1
