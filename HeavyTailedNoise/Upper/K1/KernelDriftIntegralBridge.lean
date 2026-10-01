import Mathlib

/-!
A short nonnegative-integral transport lemma.  It requires integrability
only of the explicit majorant, so it applies to the actual source-drift
readout without silently assuming that readout itself is integrable.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem lintegral_ofReal_le_of_integrable_majorant
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (C : ℝ)
    (hgInt : Integrable g μ)
    (hgNonneg : 0 ≤ᵐ[μ] g)
    (hfg : ∀ a, f a ≤ g a)
    (hgBound : (∫ a, g a ∂μ) ≤ C) :
    (∫⁻ a, ENNReal.ofReal (f a) ∂μ) ≤ ENNReal.ofReal C := by
  calc
    (∫⁻ a, ENNReal.ofReal (f a) ∂μ) ≤
        ∫⁻ a, ENNReal.ofReal (g a) ∂μ :=
      lintegral_mono (fun a => ENNReal.ofReal_le_ofReal (hfg a))
    _ = ENNReal.ofReal (∫ a, g a ∂μ) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        hgInt hgNonneg).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hgBound

end

end HeavyTailedNoise.UpperK1
