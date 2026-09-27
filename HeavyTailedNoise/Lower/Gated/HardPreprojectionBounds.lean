import HeavyTailedNoise.Analysis.CarmonChainQuantitative
import HeavyTailedNoise.Lower.Gated.SupportResidualHessian
import HeavyTailedNoise.Lower.Gated.HardObjective

/-!
Quantitative bounds for the exact potential before radial soft projection.
Every derivative is taken on the ambient Euclidean space `Point d`.
-/

namespace HeavyTailedNoise

noncomputable section

/-- The exact `F_U(y) = f_T(Uᵀy) + Q_U(y)` appearing inside `hardPotential`. -/
def hardPreprojectionPotential {d T : ℕ} (U : Fin T → Point d) (y : Point d) : ℝ :=
  carmonChain (frameCoordinates U y) + gatedCorrection U y

theorem hardPotential_eq_preprojection {d T : ℕ} (U : Fin T → Point d) (x : Point d) :
    hardPotential U x =
      hardPreprojectionPotential U (softProjection (hardRadius T) x) +
        (1 / 10 : ℝ) * ‖x‖ ^ 2 := rfl

theorem contDiff_hardPreprojectionPotential_two {d T : ℕ} (U : Fin T → Point d) :
    ContDiff ℝ 2 (hardPreprojectionPotential U) :=
  ((contDiff_carmonChain_two T).comp (contDiff_frameCoordinates_two U)).add
    (contDiff_gatedCorrection_two U)

theorem fderiv_hardPreprojectionPotential {d T : ℕ} (U : Fin T → Point d) (y : Point d) :
    fderiv ℝ (hardPreprojectionPotential U) y =
      fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x)) y +
        fderiv ℝ (gatedCorrection U) y := by
  exact fderiv_fun_add
    ((((contDiff_carmonChain_two T).comp (contDiff_frameCoordinates_two U)).differentiable
      (by norm_num) y))
    (((contDiff_gatedCorrection_two U).differentiable (by norm_num) y))

theorem second_fderiv_hardPreprojectionPotential {d T : ℕ}
    (U : Fin T → Point d) (y : Point d) :
    fderiv ℝ (fderiv ℝ (hardPreprojectionPotential U)) y =
      fderiv ℝ (fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x))) y +
        fderiv ℝ (fderiv ℝ (gatedCorrection U)) y := by
  have heq := funext (fderiv_hardPreprojectionPotential U)
  rw [heq]
  have hf := ((contDiff_carmonChain_two T).comp (contDiff_frameCoordinates_two U)).fderiv_right
    (m := 1) (by norm_num)
  have hq := (contDiff_gatedCorrection_two U).fderiv_right (m := 1) (by norm_num)
  exact fderiv_fun_add (hf.differentiable (by norm_num) y)
    (hq.differentiable (by norm_num) y)

/-- Global ambient first-derivative bound, with no condition on the query point. -/
theorem norm_fderiv_hardPreprojectionPotential_le {d T : ℕ}
    {U : Fin T → Point d} (hU : Orthonormal ℝ U) (y : Point d) :
    ‖fderiv ℝ (hardPreprojectionPotential U) y‖ ≤ 23 * Real.sqrt T + 100 := by
  have hq : ‖fderiv ℝ (gatedCorrection U) y‖ ≤ 100 := by
    simpa [gradient] using norm_gradient_gatedCorrection_le_100_of_orthonormal hU y
  rw [fderiv_hardPreprojectionPotential]
  exact (ContinuousLinearMap.opNorm_add_le _ _).trans
    (add_le_add (norm_fderiv_carmonChain_pullback_le_23_sqrt hU y)
      hq)

theorem norm_gradient_hardPreprojectionPotential_le {d T : ℕ}
    {U : Fin T → Point d} (hU : Orthonormal ℝ U) (y : Point d) :
    ‖gradient (hardPreprojectionPotential U) y‖ ≤ 23 * Real.sqrt T + 100 := by
  simpa [gradient] using norm_fderiv_hardPreprojectionPotential_le hU y

/-- Exact sum of the checked chain bound `152` and correction bound `4100`. -/
theorem norm_second_fderiv_hardPreprojectionPotential_le_4252 {d T : ℕ}
    {U : Fin T → Point d} (hU : Orthonormal ℝ U) (y : Point d) :
    ‖fderiv ℝ (fderiv ℝ (hardPreprojectionPotential U)) y‖ ≤ 4252 := by
  rw [second_fderiv_hardPreprojectionPotential]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x))) y‖ +
        ‖fderiv ℝ (fderiv ℝ (gatedCorrection U)) y‖ := ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ (152 : ℝ) + 4100 := add_le_add (norm_second_fderiv_carmonChain_pullback_le_152 hU y)
      (norm_second_fderiv_gatedCorrection_le_4100_of_orthonormal hU y)
    _ = 4252 := by norm_num

end

end HeavyTailedNoise
