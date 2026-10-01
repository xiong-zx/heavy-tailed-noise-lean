import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Addition of four error budgets under one common law. -/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

theorem extended_average_four_errors
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (c : ENNReal)
    (e f g h b : Ω → ENNReal)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hh : AEMeasurable h μ)
    (hpoint : ∀ ω, e ω ≤ f ω + g ω + h ω + b ω)
    {A B C D : ENNReal}
    (hA : c * (∫⁻ ω, f ω ∂μ) ≤ A)
    (hB : c * (∫⁻ ω, g ω ∂μ) ≤ B)
    (hC : c * (∫⁻ ω, h ω ∂μ) ≤ C)
    (hD : c * (∫⁻ ω, b ω ∂μ) ≤ D) :
    c * (∫⁻ ω, e ω ∂μ) ≤ A + B + C + D := by
  have hsum :
      (∫⁻ ω, f ω + g ω + h ω + b ω ∂μ) =
        (∫⁻ ω, f ω ∂μ) + (∫⁻ ω, g ω ∂μ) +
          (∫⁻ ω, h ω ∂μ) + (∫⁻ ω, b ω ∂μ) := by
    have hfg : AEMeasurable (fun ω => f ω + g ω) μ := hf.add hg
    have hfgh : AEMeasurable (fun ω => f ω + g ω + h ω) μ := hfg.add hh
    rw [lintegral_add_left' hfgh b,
      lintegral_add_left' hfg h, lintegral_add_left' hf g]
  calc
    _ ≤ c * (∫⁻ ω, f ω + g ω + h ω + b ω ∂μ) :=
      mul_le_mul_right (lintegral_mono hpoint) c
    _ = c * (∫⁻ ω, f ω ∂μ) + c * (∫⁻ ω, g ω ∂μ) +
        c * (∫⁻ ω, h ω ∂μ) + c * (∫⁻ ω, b ω ∂μ) := by
      rw [hsum, mul_add, mul_add, mul_add]
    _ ≤ A + B + C + D := add_le_add (add_le_add (add_le_add hA hB) hC) hD

end HeavyTailedNoise.UpperK1
