import HeavyTailedNoise.Model.Basic

/-!
The final conversion from a high-probability gradient barrier to a strict
lower bound on extended expected risk. It remains valid if the risk is infinite.
-/

open MeasureTheory

namespace HeavyTailedNoise

/-- More than half the probability mass above `a` forces the extended
expectation strictly above `a / 2`. -/
theorem lintegral_gt_half_threshold {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ENNReal) (hf : AEMeasurable f μ)
    {a : ENNReal} (ha0 : a ≠ 0) (hatop : a ≠ ⊤)
    (hgood : (1 / 2 : ENNReal) < μ {ω | a ≤ f ω}) :
    a * (1 / 2 : ENNReal) < ∫⁻ ω, f ω ∂μ := by
  calc
    a * (1 / 2 : ENNReal) < a * μ {ω | a ≤ f ω} :=
      ENNReal.mul_lt_mul_right ha0 hatop hgood
    _ ≤ ∫⁻ ω, f ω ∂μ := mul_meas_ge_le_lintegral₀ hf a

end HeavyTailedNoise
