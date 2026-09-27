import HeavyTailedNoise.Lower.Gated.JointHardGeometry
import HeavyTailedNoise.Lower.Gated.HardPreprojectionBounds
import HeavyTailedNoise.Lower.Gated.ScaledObjectiveGap

/-!
Joint `C²` regularity of the actual preprojection objective in the hidden
frame and query. The soft-projection composition and final gradient
measurability remain separate obligations, not additional observations.
-/

namespace HeavyTailedNoise

noncomputable section

theorem contDiff_joint_hardPreprojectionPotential_two {d T : ℕ} :
    ContDiff ℝ 2
      (fun z : (Fin T → Point d) × Point d =>
        hardPreprojectionPotential z.1 z.2) := by
  change ContDiff ℝ 2
    (fun z : (Fin T → Point d) × Point d =>
      carmonChain (frameCoordinates z.1 z.2) + gatedCorrection z.1 z.2)
  exact ((contDiff_carmonChain_two T).comp
    (contDiff_joint_frameCoordinates_two (d := d) (T := T))).add
      (contDiff_joint_gatedCorrection_two (d := d) (T := T))

end

end HeavyTailedNoise
