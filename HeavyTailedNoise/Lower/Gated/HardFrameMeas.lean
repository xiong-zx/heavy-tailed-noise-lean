import HeavyTailedNoise.Lower.Gated.JointScaledGradientMeas
import HeavyTailedNoise.Probability.ParametricGaussian
import HeavyTailedNoise.Probability.HaarConditionalFrame

/-!
Lightweight restriction of the checked joint gradient/response maps to the
subtype of genuine orthonormal frames. Keep the large admissible-instance
constructor out of the measurability goal.
-/

namespace HeavyTailedNoise

noncomputable section

theorem measurable_scaledGradient_on_orthonormalFrames
    {d T : ℕ} (hT : 0 < T) {L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) :
    Measurable
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × Point d =>
        gradient (scaledHardPotential L ε z.1.1) z.2) := by
  let f : ((Fin T → Point d) × Point d) → Point d :=
    fun z => gradient (scaledHardPotential L ε z.1) z.2
  let g : ({U : Fin T → Point d // Orthonormal ℝ U} × Point d) →
      ((Fin T → Point d) × Point d) := fun z => (z.1.1, z.2)
  have hf : Measurable f := measurable_joint_scaledHardGradient hT hL hε
  have hg : Measurable g :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hfg : Measurable (f ∘ g) := hf.comp hg
  change Measurable (f ∘ g)
  exact hfg

theorem measurable_gaussianResponse_on_orthonormalFrames
    {d T : ℕ} (hT : 0 < T) {L ε σ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) :
    Measurable
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} ×
        (Point d × Point d) =>
        gaussianResponse d (gradient (scaledHardPotential L ε z.1.1))
          (σ / Real.sqrt d) z.2.1 z.2.2) := by
  exact measurable_parametric_gaussianResponse d
    (fun U : {U : Fin T → Point d // Orthonormal ℝ U} =>
      gradient (scaledHardPotential L ε U.1))
    (σ / Real.sqrt d)
    (measurable_scaledGradient_on_orthonormalFrames hT hL hε)

end

end HeavyTailedNoise
