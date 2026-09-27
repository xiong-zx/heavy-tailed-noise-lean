import HeavyTailedNoise.Probability.RiskProtocolJointLaw

/-!
A uniform event bound for each fixed private tape passes to an arbitrary
independent private law. No regular conditional distribution on Private and
no StandardBorelSpace Private are needed.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

theorem private_mixture_event_le
    {Frame Private Tape : Type*}
    [MeasurableSpace Frame] [MeasurableSpace Private] [MeasurableSpace Tape]
    (μ : Measure Frame) (ρ : Measure Private) (ν : Measure Tape)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (E : Set (Frame × (Private × Tape))) (hE : MeasurableSet E)
    (b : ENNReal)
    (hfixed : ∀ r : Private,
      (μ.prod ν) {z : Frame × Tape | (z.1, (r, z.2)) ∈ E} ≤ b) :
    (μ.prod (ρ.prod ν)) E ≤ b := by
  have hsec : MeasurableSet
      {z : (Frame × Private) × Tape | (z.1.1, (z.1.2, z.2)) ∈ E} :=
    hE.preimage (by fun_prop)
  have hG : Measurable
      (fun p : Frame × Private => ν {ξ | (p.1, (p.2, ξ)) ∈ E}) := by
    exact measurable_measure_prodMk_left hsec
  calc
    (μ.prod (ρ.prod ν)) E =
        ∫⁻ U, ∫⁻ r, ν {ξ | (U, (r, ξ)) ∈ E} ∂ρ ∂μ := by
      rw [Measure.prod_apply hE]
      apply lintegral_congr
      intro U
      rw [Measure.prod_apply (hE.preimage measurable_prodMk_left)]
      rfl
    _ = ∫⁻ r, ∫⁻ U, ν {ξ | (U, (r, ξ)) ∈ E} ∂μ ∂ρ :=
      lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ r, (μ.prod ν) {z : Frame × Tape | (z.1, (r, z.2)) ∈ E} ∂ρ := by
      apply lintegral_congr
      intro r
      have hEr : MeasurableSet
          {z : Frame × Tape | (z.1, (r, z.2)) ∈ E} :=
        hE.preimage (measurable_fst.prodMk
          (measurable_const.prodMk measurable_snd))
      rw [Measure.prod_apply hEr]
      rfl
    _ ≤ ∫⁻ _r, b ∂ρ := lintegral_mono hfixed
    _ = b := by simp

end

end HeavyTailedNoise
