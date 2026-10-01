import HeavyTailedNoise.Upper.Foundations.ClippedBatch
import HeavyTailedNoise.Upper.Foundations.ClipMoment

/-!
The dimension-free fresh-batch variance bound for a clipped residual at an
arbitrary fixed pre-batch center.  The batch lemma conditions on the whole
pre-batch history; the moment input is the oracle's original centered
`p`-BCM, not a conditional moment of `response - center`.
-/

open MeasureTheory

noncomputable section

namespace HeavyTailedNoise

theorem Admissible.upperClippedBatchMean_secondMoment_le
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar τ : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hτ : 0 < τ) (x w : Point d) (hb : 0 < b) :
    (∫ seeds : Fin b → Seed,
      ‖upperResidualBatchMean I.oracle (upperClip τ) x w seeds -
        upperResidualSourceMean I.oracle (upperClip τ) x w‖ ^ 2
      ∂freshSeedLaw I.oracle b) ≤
      (b : ℝ)⁻¹ * ((2 * τ) ^ (2 - p) * σ ^ p) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  let f : Seed → ℝ := fun ξ =>
    ‖upperClip τ (I.oracle.response x ξ - w) -
      upperClip τ (I.objective.grad x - w)‖ ^ 2
  have hresponse : Measurable (I.oracle.response x) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hdiff : Measurable (fun ξ : Seed =>
      upperClip τ (I.oracle.response x ξ - w) -
        upperClip τ (I.objective.grad x - w)) :=
    ((measurable_upperClip hτ).comp
      (hresponse.sub (measurable_const : Measurable (fun _ : Seed => w)))).sub
      measurable_const
  have hf : Measurable f := by
    dsimp [f]
    exact hdiff.norm.pow_const 2
  have hnonneg (ξ : Seed) : 0 ≤ f ξ := sq_nonneg _
  have hscale : 0 ≤ (2 * τ) ^ (2 - p) * σ ^ p :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg I.sigma_nonneg _)
  have hreal : (∫ ξ, f ξ ∂I.oracle.law) ≤
      (2 * τ) ^ (2 - p) * σ ^ p := by
    calc
      (∫ ξ, f ξ ∂I.oracle.law) =
          ENNReal.toReal (∫⁻ ξ, ENNReal.ofReal (f ξ) ∂I.oracle.law) :=
            integral_eq_lintegral_of_nonneg_ae
              (Filter.Eventually.of_forall hnonneg) hf.aestronglyMeasurable
      _ ≤ ENNReal.toReal
          (ENNReal.ofReal ((2 * τ) ^ (2 - p) * σ ^ p)) :=
            ENNReal.toReal_mono (by finiteness)
              (I.upperClip_centered_difference_secondMoment hτ x w)
      _ = (2 * τ) ^ (2 - p) * σ ^ p := ENNReal.toReal_ofReal hscale
  have href := upperResidualBatchMean_secondMoment_le_reference
    I.oracle (upperClip τ) (measurable_upperClip hτ) τ
    (upperClip_norm_le hτ) x w (I.objective.grad x) hb
  calc
    (∫ seeds : Fin b → Seed,
      ‖upperResidualBatchMean I.oracle (upperClip τ) x w seeds -
        upperResidualSourceMean I.oracle (upperClip τ) x w‖ ^ 2
      ∂freshSeedLaw I.oracle b) ≤
        (b : ℝ)⁻¹ * ∫ ξ, f ξ ∂I.oracle.law := href
    _ ≤ (b : ℝ)⁻¹ * ((2 * τ) ^ (2 - p) * σ ^ p) :=
      mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr (Nat.cast_nonneg b))

end HeavyTailedNoise
