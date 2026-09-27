import HeavyTailedNoise.Model.Distributional

/-!
The three independent random sources in the final average risk—preselected
frame, algorithm private tape, and fresh Gaussian seeds—can be represented by
one joint product law. The only premise here is measurability of the actual
nonnegative loss as a function of all three sources.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

theorem lintegral_frame_private_seed_eq_joint
    {Frame Private Seed : Type*}
    [MeasurableSpace Frame] [MeasurableSpace Private] [MeasurableSpace Seed]
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (loss : Frame → Private → Seed → ENNReal)
    (hloss : Measurable
      (fun z : Frame × (Private × Seed) => loss z.1 z.2.1 z.2.2)) :
    (∫⁻ U, ∫⁻ r, ∫⁻ s, loss U r s ∂ν ∂ρ ∂μ) =
      ∫⁻ z, loss z.1 z.2.1 z.2.2 ∂μ.prod (ρ.prod ν) := by
  have hinner (U : Frame) :
      (∫⁻ r, ∫⁻ s, loss U r s ∂ν ∂ρ) =
        ∫⁻ p, loss U p.1 p.2 ∂ρ.prod ν := by
    have hsection : Measurable
        (fun p : Private × Seed => loss U p.1 p.2) :=
      hloss.comp (measurable_const.prodMk measurable_id)
    exact lintegral_lintegral hsection.aemeasurable
  simp_rw [hinner]
  exact lintegral_lintegral hloss.aemeasurable

end

end HeavyTailedNoise
