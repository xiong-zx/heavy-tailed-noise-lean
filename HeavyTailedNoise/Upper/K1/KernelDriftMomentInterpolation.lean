import Mathlib

/-!
On a probability space, a nonnegative `p`-integrable random scale has an
`s` moment for every `0 < s ≤ p`, with the sharp root bound.  This is the
outer-history step needed after the actual q-WAS displacement factor has
been made deterministic by the clipped center update.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem integral_rpow_le_lpNorm_rpow_of_probability
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Measurable f)
    (hf_nonneg : ∀ a, 0 ≤ f a)
    {s p : ℝ} (hs : 0 < s) (hsp : s ≤ p)
    (hfp : MemLp f (ENNReal.ofReal p) μ) :
    (∫ a, f a ^ s ∂μ) ≤
      (lpNorm f (ENNReal.ofReal p) μ) ^ s := by
  have hENN : eLpNorm f (ENNReal.ofReal s) μ ≤
      eLpNorm f (ENNReal.ofReal p) μ := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (f := f) (μ := μ) (ENNReal.ofReal_le_ofReal hsp)
      hf.aestronglyMeasurable
    simpa using h
  have hLp : lpNorm f (ENNReal.ofReal s) μ ≤
      lpNorm f (ENNReal.ofReal p) μ := by
    simpa only [toReal_eLpNorm] using
      (ENNReal.toReal_mono hfp.eLpNorm_ne_top hENN)
  have hInt0 : 0 ≤ ∫ a, f a ^ s ∂μ :=
    integral_nonneg (fun a => Real.rpow_nonneg (hf_nonneg a) _)
  have hLpEq : lpNorm f (ENNReal.ofReal s) μ =
      (∫ a, f a ^ s ∂μ) ^ s⁻¹ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hs)
      ENNReal.ofReal_ne_top hf.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hs.le]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (hf_nonneg a)]
  have hrecover :
      (lpNorm f (ENNReal.ofReal s) μ) ^ s =
        ∫ a, f a ^ s ∂μ := by
    rw [hLpEq, ← Real.rpow_mul hInt0,
      inv_mul_cancel₀ hs.ne', Real.rpow_one]
  calc
    (∫ a, f a ^ s ∂μ) =
        (lpNorm f (ENNReal.ofReal s) μ) ^ s := hrecover.symm
    _ ≤ (lpNorm f (ENNReal.ofReal p) μ) ^ s :=
      Real.rpow_le_rpow lpNorm_nonneg hLp hs.le

end

end HeavyTailedNoise.UpperK1
