import HeavyTailedNoise.Lower.Gated.ScaledObjectiveSmoothness
import HeavyTailedNoise.Lower.Gated.HardStationarity

/-!
Exact gradient rescaling and final stationarity decoding. The arbitrary
algorithm's output may be any ambient point, including an unqueried point.
-/

namespace HeavyTailedNoise

noncomputable section

theorem gradient_scaledHardPotential_eq
    {d T : ℕ} (hT : 0 < T) (U : Fin T → Point d)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (x : Point d) :
    gradient (scaledHardPotential L ε U) x =
      (80 * ε) • gradient (hardPotential U)
        ((hardScaleLambda L ε)⁻¹ • x) := by
  let lam : ℝ := hardScaleLambda L ε
  let c : ℝ := L * lam ^ 2 / 4300
  let g : Point d →L[ℝ] Point d := lam⁻¹ • ContinuousLinearMap.id ℝ (Point d)
  have hlam : 0 < lam := by dsimp [lam, hardScaleLambda]; positivity
  let y : Point d := g x
  have hH : HasGradientAt (hardPotential U)
      (gradient (hardPotential U) y) y :=
    ((contDiff_hardPotential_two hT U).differentiable
      (by norm_num) y).hasGradientAt
  have hg : HasFDerivAt g g x := g.hasFDerivAt
  have hcomp := hH.hasFDerivAt.comp x hg
  have hfun : scaledHardPotential L ε U =
      (fun z : Point d => c • hardPotential U (g z)) := by
    funext z
    rfl
  have hscaled : HasFDerivAt (scaledHardPotential L ε U)
      (c • ((innerSL ℝ (gradient (hardPotential U) y)).comp g)) x := by
    rw [hfun]
    exact hcomp.const_smul c
  have hdual :
      c • ((innerSL ℝ (gradient (hardPotential U) y)).comp g) =
        innerSL ℝ ((c * lam⁻¹) • gradient (hardPotential U) y) := by
    ext v
    simp [g, innerSL_apply_apply, real_inner_smul_left, smul_smul]
  rw [hdual] at hscaled
  have hgrad : HasGradientAt (scaledHardPotential L ε U)
      ((c * lam⁻¹) • gradient (hardPotential U) y) x :=
    (hasGradientAt_iff_hasFDerivAt).2 hscaled
  have hactual : HasGradientAt (scaledHardPotential L ε U)
      (gradient (scaledHardPotential L ε U) x) x :=
    ((contDiff_scaledHardPotential_two hT U L ε).differentiable
      (by norm_num) x).hasGradientAt
  have hcoeff : c * lam⁻¹ = 80 * ε := by
    dsimp [c, lam, hardScaleLambda]
    field_simp [hL.ne']
    ring
  have heq := (hgrad.unique hactual).symm
  simpa [y, g, lam, hcoeff] using heq

/-- The frozen `2ε` gradient threshold decodes through the proved unscaled
`1/40` barrier at every possible algorithm output. -/
theorem scaledHardPotential_stationarity_decoding
    {d T : ℕ} (hT : 0 < T) (U : Fin T → Point d)
    (hU : Orthonormal ℝ U)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (x : Point d)
    (hg : ‖gradient (scaledHardPotential L ε U) x‖ < 2 * ε) :
    (∀ i : Fin T,
      1 ≤ |frameCoordinates U
        (softProjection (hardRadius T) ((hardScaleLambda L ε)⁻¹ • x)) i|) ∧
    ‖frameOrthogonalResidual U Finset.univ
      (softProjection (hardRadius T) ((hardScaleLambda L ε)⁻¹ • x))‖ <
        (1 / 6 : ℝ) := by
  have hformula := gradient_scaledHardPotential_eq hT U hL hε x
  rw [hformula, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 80 * ε)] at hg
  have hsmall : ‖gradient (hardPotential U)
      ((hardScaleLambda L ε)⁻¹ • x)‖ < (1 / 40 : ℝ) := by
    nlinarith [norm_nonneg (gradient (hardPotential U)
      ((hardScaleLambda L ε)⁻¹ • x))]
  exact hardPotential_stationarity_decoding hU hT _ hsmall

end

end HeavyTailedNoise
