import HeavyTailedNoise.Probability.GaussianMeanKernel
import HeavyTailedNoise.Lower.Gated.JointPrefixGradientMeas
import HeavyTailedNoise.Lower.Gated.PrefixContrast
import HeavyTailedNoise.Probability.GaussianKLAdaptive

/-!
Gaussian information for one frozen truncated-prefix stage. The response
kernel below maps the existing standard Gaussian seed through the existing
truncated gradient; it does not define a second oracle. The stopped-stage
initial-history identification is a separate boundary.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
set_option maxHeartbeats 1000000

noncomputable section

namespace HeavyTailedNoise

private lemma idealPrefixIndex_val (hT : 0 < T) (j : Fin T) :
    idealPrefixIndex hT j.val = j := by
  apply Fin.ext
  simp [idealPrefixIndex]
  omega

/-- The exact frozen response mean is measurable jointly in the frame and
query. -/
theorem measurable_joint_frozenStageMean {d T : ℕ} (hT : 0 < T)
    (j : Fin T) :
    Measurable (fun z : (Fin T → Point d) × Point d =>
      idealResponseMean hT z.1 j.val z.2) := by
  simpa [idealResponseMean, idealPrefixIndex_val hT j] using
    (measurable_joint_prefixGradient hT j)

/-- Contrast of the exact frozen response means for two orthonormal frames
sharing every previously revealed column. -/
theorem norm_frozenStageMean_sub_le_300 {d T : ℕ} (hT : 0 < T)
    {U V : Fin T → Point d} (hU : Orthonormal ℝ U)
    (hV : Orthonormal ℝ V) (j : Fin T)
    (hpre : ∀ i, i < j → U i = V i) (x : Point d) :
    ‖idealResponseMean hT U j.val x -
      idealResponseMean hT V j.val x‖ ≤ 300 := by
  simpa [idealResponseMean, idealPrefixIndex_val hT j] using
    (norm_gradient_prefixHardPotential_sub_le_300 hU hV j hpre x)

end HeavyTailedNoise
