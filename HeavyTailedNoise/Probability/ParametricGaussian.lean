import HeavyTailedNoise.Model.ParametricProtocol
import HeavyTailedNoise.Probability.GaussianOracle

/-!
The final additive Gaussian oracle keeps its seed law fixed as the hidden
frame varies. Joint response measurability reduces exactly to joint
measurability of the deterministic gradient field.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

theorem measurable_parametric_gaussianResponse
    {Frame : Type*} [MeasurableSpace Frame]
    (d : ℕ) (grad : Frame → Point d → Point d) (a : ℝ)
    (hgrad : Measurable
      (fun z : Frame × Point d => grad z.1 z.2)) :
    Measurable (fun z : Frame × (Point d × Point d) =>
      gaussianResponse d (grad z.1) a z.2.1 z.2.2) := by
  unfold gaussianResponse
  have hnoise : Measurable
      (fun z : Frame × (Point d × Point d) => a • z.2.2) := by fun_prop
  exact (hgrad.comp (measurable_fst.prodMk
    (measurable_fst.comp measurable_snd))).add hnoise

theorem gaussianOracle_common_freshSeedLaw
    {Frame : Type*} [MeasurableSpace Frame]
    (d N : ℕ) (grad : Frame → Point d → Point d)
    (hgrad : ∀ U, Continuous (grad U)) (a : ℝ) (U : Frame) :
    freshSeedLaw (gaussianOracle d (grad U) (hgrad U) a) N =
      Measure.pi (fun _ : Fin N => standardGaussianLaw d) := rfl

end

end HeavyTailedNoise
