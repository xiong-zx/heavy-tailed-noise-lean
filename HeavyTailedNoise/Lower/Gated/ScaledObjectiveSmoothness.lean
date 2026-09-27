import HeavyTailedNoise.Lower.Gated.HardObjectiveSmoothness
import HeavyTailedNoise.Lower.Gated.ScaledObjectiveGap

/-!
Smoothness of the exact final parameter rescaling. This is an objective-side
legality lemma; the additive Gaussian oracle is supplied separately by
`GaussianOracle.gaussianAdmissible`.
-/

namespace HeavyTailedNoise

open scoped NNReal

noncomputable section

theorem contDiff_scaledHardPotential_two {d T : ℕ}
    (hT : 0 < T) (U : Fin T → Point d) (L ε : ℝ) :
    ContDiff ℝ 2 (scaledHardPotential L ε U) := by
  let lam : ℝ := hardScaleLambda L ε
  let g : Point d →L[ℝ] Point d := lam⁻¹ • ContinuousLinearMap.id ℝ (Point d)
  have hg : ContDiff ℝ 2 g := g.contDiff
  have hf : ContDiff ℝ 2 (fun x : Point d => hardPotential U (g x)) :=
    (contDiff_hardPotential_two hT U).comp hg
  change ContDiff ℝ 2 (fun x : Point d =>
    (L * lam ^ 2 / 4300) * hardPotential U (g x))
  exact contDiff_const.mul hf

/-- The final rescaling cancels the two powers of `λ` in its Hessian. -/
theorem norm_second_fderiv_scaledHardPotential_le_L
    {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (x : Point d) :
    ‖fderiv ℝ (fderiv ℝ (scaledHardPotential L ε U)) x‖ ≤ L := by
  let lam : ℝ := hardScaleLambda L ε
  let c : ℝ := L * lam ^ 2 / 4300
  let g : Point d →L[ℝ] Point d := lam⁻¹ • ContinuousLinearMap.id ℝ (Point d)
  have hlam : 0 < lam := by dsimp [lam, hardScaleLambda]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hgNorm : ‖g‖ ≤ lam⁻¹ := by
    calc
      ‖g‖ ≤ ‖(lam⁻¹ : ℝ)‖ * ‖ContinuousLinearMap.id ℝ (Point d)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ lam⁻¹ * 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
        gcongr
        exact ContinuousLinearMap.norm_id_le
      _ = lam⁻¹ := by ring
  have hg2 (y : Point d) : ‖fderiv ℝ (fderiv ℝ g) y‖ = 0 := by
    have hfg : fderiv ℝ g = fun _ => g := funext fun z => g.fderiv
    rw [hfg]
    have hzero : fderiv ℝ (fun _ : Point d => g) y =
        (0 : Point d →L[ℝ] (Point d →L[ℝ] Point d)) :=
      fderiv_const_apply g
    rw [hzero]
    exact ContinuousLinearMap.opNorm_zero
  have hcomp := norm_second_fderiv_comp_le
    (contDiff_hardPotential_two hT U) g.contDiff x
  have hcomp' :
      ‖fderiv ℝ (fderiv ℝ (fun y : Point d => hardPotential U (g y))) x‖ ≤
        4300 * (lam⁻¹) ^ 2 := by
    rw [g.fderiv, hg2, mul_zero, add_zero] at hcomp
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ (hardPotential U)) (g x)‖ * ‖g‖ ^ 2 := hcomp
      _ ≤ 4300 * (lam⁻¹) ^ 2 := by
        gcongr
        · exact norm_second_fderiv_hardPotential_le_4300 hU hT (g x)
  have hsecond :
      fderiv ℝ (fderiv ℝ (scaledHardPotential L ε U)) x =
        c • fderiv ℝ (fderiv ℝ
          (fun y : Point d => hardPotential U (g y))) x := by
    have heq : scaledHardPotential L ε U =
        (fun y : Point d => c • hardPotential U (g y)) := by
      funext y
      rfl
    have hfun : (fun y : Point d => c • hardPotential U (g y)) =
        c • (fun y : Point d => hardPotential U (g y)) := by
      funext y
      rfl
    have hfirst : fderiv ℝ (scaledHardPotential L ε U) =
        c • fderiv ℝ (fun y : Point d => hardPotential U (g y)) := by
      rw [heq, hfun]
      exact fderiv_const_smul_field c
    rw [hfirst]
    exact congrFun
      (fderiv_const_smul_field
        (f := fderiv ℝ (fun y : Point d => hardPotential U (g y))) c) x
  have hcoef : c * (4300 * (lam⁻¹) ^ 2) = L := by
    dsimp [c]
    field_simp [hlam.ne']
  calc
    ‖fderiv ℝ (fderiv ℝ (scaledHardPotential L ε U)) x‖ =
        ‖c • fderiv ℝ (fderiv ℝ
          (fun y : Point d => hardPotential U (g y))) x‖ := by rw [hsecond]
    _ ≤ ‖(c : ℝ)‖ *
        ‖fderiv ℝ (fderiv ℝ (fun y : Point d => hardPotential U (g y))) x‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
    _ = c * ‖fderiv ℝ (fderiv ℝ
        (fun y : Point d => hardPotential U (g y))) x‖ := by
          rw [Real.norm_eq_abs, abs_of_pos hc]
    _ ≤ c * (4300 * (lam⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_left hcomp' hc.le
    _ = L := hcoef

/-- Native Euclidean gradient Lipschitz continuity of the final rescaled
population objective. -/
theorem lipschitzWith_gradient_scaledHardPotential
    {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    LipschitzWith (⟨L, hL.le⟩ : ℝ≥0)
      (gradient (scaledHardPotential L ε U)) := by
  let C : ℝ≥0 := ⟨L, hL.le⟩
  have hf : Differentiable ℝ
      (fderiv ℝ (scaledHardPotential L ε U)) :=
    ((contDiff_scaledHardPotential_two hT U L ε).fderiv_right
      (m := 1) (by norm_num)).differentiable (by norm_num)
  have hLips : LipschitzWith C
      (fderiv ℝ (scaledHardPotential L ε U)) :=
    lipschitzWith_of_nnnorm_fderiv_le hf (fun x => by
      exact_mod_cast norm_second_fderiv_scaledHardPotential_le_L hU hT hL hε x)
  have hcomp := (InnerProductSpace.toDual ℝ (Point d)).symm.lipschitz.comp hLips
  have hcoef : (1 : ℝ≥0) * C = C := one_mul C
  rw [hcoef] at hcomp
  change LipschitzWith C (gradient (scaledHardPotential L ε U)) at hcomp
  simpa [C] using hcomp

theorem norm_gradient_scaledHardPotential_sub_le_L
    {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (x y : Point d) :
    ‖gradient (scaledHardPotential L ε U) x -
      gradient (scaledHardPotential L ε U) y‖ ≤
        L * ‖x - y‖ := by
  have h := (lipschitzWith_gradient_scaledHardPotential hU hT hL hε).norm_sub_le x y
  change ‖gradient (scaledHardPotential L ε U) x -
    gradient (scaledHardPotential L ε U) y‖ ≤ L * ‖x - y‖ at h
  exact h

end

end HeavyTailedNoise
