import HeavyTailedNoise.Lower.Gated.HardObjective

/-!
Joint regularity in a hidden frame and an ambient query point. Fixed-frame
smoothness alone does not justify Tonelli over the preselected frame law.
-/

namespace HeavyTailedNoise

noncomputable section

theorem contDiff_joint_frameCoordinates_two {d T : ℕ} :
    ContDiff ℝ 2
      (fun z : (Fin T → Point d) × Point d => frameCoordinates z.1 z.2) := by
  unfold frameCoordinates
  apply contDiff_pi.mpr
  intro i
  have hU : ContDiff ℝ 2
      (fun z : (Fin T → Point d) × Point d => z.1 i) := by fun_prop
  have hy : ContDiff ℝ 2
      (fun z : (Fin T → Point d) × Point d => z.2) := by fun_prop
  exact hU.inner ℝ hy

theorem contDiff_joint_frameOrthogonalResidual_two {d T : ℕ}
    (s : Finset (Fin T)) :
    ContDiff ℝ 2
      (fun z : (Fin T → Point d) × Point d =>
        frameOrthogonalResidual z.1 s z.2) := by
  unfold frameOrthogonalResidual
  have hy : ContDiff ℝ 2
      (fun z : (Fin T → Point d) × Point d => z.2) := by fun_prop
  apply hy.sub
  apply ContDiff.sum
  intro i hi
  have hz := (contDiff_pi.mp (contDiff_joint_frameCoordinates_two (d := d) (T := T))) i
  have hU : ContDiff ℝ 2
      (fun z : (Fin T → Point d) × Point d => z.1 i) := by fun_prop
  exact hz.smul hU

theorem contDiff_joint_gatedResidual_two {d T : ℕ} (k : Fin T) :
    ContDiff ℝ 2
      (fun z : (Fin T → Point d) × Point d => gatedResidual z.1 k z.2) := by
  unfold gatedResidual
  apply ((contDiff_joint_frameOrthogonalResidual_two
    (d := d) (T := T) (Finset.univ.filter (· ≤ k))).norm_sq ℝ).sub
  apply ContDiff.sum
  intro i hi
  have hz := (contDiff_pi.mp (contDiff_joint_frameCoordinates_two (d := d) (T := T))) i
  exact (contDiff_carmonOmegaSix_two.comp hz).mul (hz.pow 2)

theorem contDiff_joint_gatedCorrection_two {d T : ℕ} :
    ContDiff ℝ 2
      (fun z : (Fin T → Point d) × Point d => gatedCorrection z.1 z.2) := by
  apply ContDiff.sum
  intro k hk
  have hσ := contDiff_joint_gatedResidual_two (d := d) (T := T) k
  have hz := contDiff_joint_frameCoordinates_two (d := d) (T := T)
  exact (contDiff_const.sub (contDiff_carmonChi_two.comp hσ)).mul
    ((contDiff_actual_chainGateTerm_two k).comp hz)

end

end HeavyTailedNoise
