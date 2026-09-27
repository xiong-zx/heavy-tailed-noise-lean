import HeavyTailedNoise.Analysis.CarmonChainGap
import HeavyTailedNoise.Lower.Gated.HardObjective

/-!
The exact unscaled hard objective inherits the scalar chain's `12T` gap.
This proof uses the actual nonnegative correction and radial projection, without
assuming frame orthogonality or any unproved smoothness constant.
-/

namespace HeavyTailedNoise

noncomputable section

theorem gatedResidual_zero {d T : ℕ} (U : Fin T → Point d) (k : Fin T) :
    gatedResidual U k 0 = 0 := by
  simp [gatedResidual, frameOrthogonalResidual, frameCoordinates]

theorem carmonChi_zero : carmonChi 0 = 1 := by
  unfold carmonChi
  rw [smoothstep_zero_of_nonpos (by norm_num)]
  ring

theorem gatedCorrection_zero {d T : ℕ} (U : Fin T → Point d) :
    gatedCorrection U 0 = 0 := by
  unfold gatedCorrection
  apply Finset.sum_eq_zero
  intro k hk
  rw [gatedResidual_zero, carmonChi_zero]
  ring

theorem softProjection_zero {d : ℕ} (R : ℝ) :
    softProjection (d := d) R 0 = 0 := by
  simp [softProjection]

theorem frameCoordinates_zero {d T : ℕ} (U : Fin T → Point d) :
    frameCoordinates U 0 = fun _ : Fin T => 0 := by
  funext k
  simp [frameCoordinates]

theorem hardPotential_zero_eq_chain_zero {d T : ℕ} (U : Fin T → Point d) :
    hardPotential U 0 = carmonChain (fun _ : Fin T => 0) := by
  simp [hardPotential, softProjection_zero, gatedCorrection_zero,
    frameCoordinates_zero]

theorem hardPotential_chainInf_le {d T : ℕ} (U : Fin T → Point d)
    (x : Point d) :
    sInf (Set.range (carmonChain (T := T))) ≤ hardPotential U x := by
  have hbdd : BddBelow (Set.range (carmonChain (T := T))) := by
    refine ⟨-(12 : ℝ) * T, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact carmonChain_lower_bound z
  have hf : sInf (Set.range (carmonChain (T := T))) ≤
      carmonChain (frameCoordinates U (softProjection (hardRadius T) x)) :=
    csInf_le hbdd (Set.mem_range_self _)
  have hq := gatedCorrection_nonneg U (softProjection (hardRadius T) x)
  have hr : 0 ≤ (1 / 10 : ℝ) * ‖x‖ ^ 2 := by positivity
  change sInf (Set.range (carmonChain (T := T))) ≤
    carmonChain (frameCoordinates U (softProjection (hardRadius T) x)) +
      gatedCorrection U (softProjection (hardRadius T) x) +
        (1 / 10 : ℝ) * ‖x‖ ^ 2
  linarith

/-- The frozen `12T` gap for the actual unscaled `H_U`. -/
theorem hardPotential_gap_le_12T {d T : ℕ} (U : Fin T → Point d) :
    hardPotential U 0 - sInf (Set.range (hardPotential U)) ≤ 12 * T := by
  have hHne : (Set.range (hardPotential U)).Nonempty :=
    ⟨hardPotential U 0, ⟨0, rfl⟩⟩
  have hInf : sInf (Set.range (carmonChain (T := T))) ≤
      sInf (Set.range (hardPotential U)) :=
    le_csInf hHne (by rintro _ ⟨x, rfl⟩; exact hardPotential_chainInf_le U x)
  rw [hardPotential_zero_eq_chain_zero]
  linarith [carmonChain_gap_le_12T (T := T)]

end

end HeavyTailedNoise
