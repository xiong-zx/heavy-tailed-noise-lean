import HeavyTailedNoise.Lower.Gated.HardProjectionSecondBound
import HeavyTailedNoise.Lower.Gated.HardPreprojectionBounds

/-!
Global `4300` smoothness of the exact unscaled hard objective. The checked
budget is `4252 + 6/20 + 1/5 = 4252.5`, with arbitrary ambient query points.
-/

namespace HeavyTailedNoise

noncomputable section

theorem second_fderiv_comp_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} {g : E → F} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (g y))) x v w =
      fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) +
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hfdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hgdd := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun y => f (g y)) =
      (fun y => (fderiv ℝ f (g y)).comp (fderiv ℝ g y)) :=
    funext fun y => fderiv_fun_comp y (hfd (g y)) (hgd y)
  rw [heq]
  have hc := (hfdd (g x)).hasFDerivAt.comp x (hgd x).hasFDerivAt
  have h := hc.clm_comp (hgdd x).hasFDerivAt
  have h' := h
  simp only [Function.comp_apply] at h'
  rw [h'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]

theorem norm_second_fderiv_comp_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} {g : E → F} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun y => f (g y))) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (g x)‖ * ‖fderiv ℝ g x‖ ^ 2 +
        ‖fderiv ℝ f (g x)‖ * ‖fderiv ℝ (fderiv ℝ g) x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [second_fderiv_comp_apply hf hg]
  calc
    _ ≤ ‖fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w)‖ +
        ‖fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ f (g x)‖ * (‖fderiv ℝ (fderiv ℝ g) x‖ * ‖v‖ * ‖w‖) +
        ‖fderiv ℝ (fderiv ℝ f) (g x)‖ * (‖fderiv ℝ g x‖ * ‖v‖) * (‖fderiv ℝ g x‖ * ‖w‖) := by
      apply add_le_add
      · exact ((fderiv ℝ f (g x)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((fderiv ℝ (fderiv ℝ g) x).le_opNorm₂ v w) (norm_nonneg _))
      · apply ((fderiv ℝ (fderiv ℝ f) (g x)).le_opNorm₂ _ _).trans
        gcongr
        · exact (fderiv ℝ g x).le_opNorm v
        · exact (fderiv ℝ g x).le_opNorm w
    _ = _ := by ring

theorem hardPreprojection_gradient_over_radius_le {T : ℕ} (hT : 0 < T) :
    (23 * Real.sqrt T + 100) / hardRadius T ≤ (1 / 20 : ℝ) := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast (Nat.succ_le_of_lt hT)
  have hs : 1 ≤ Real.sqrt T := by
    have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ T)
    nlinarith [Real.sqrt_nonneg (T : ℝ)]
  have hR : 0 < hardRadius T := by unfold hardRadius; positivity
  apply (div_le_iff₀ hR).mpr
  unfold hardRadius
  nlinarith

theorem norm_second_fderiv_projected_prepotential_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d) :
    ‖fderiv ℝ (fderiv ℝ (fun y => hardPreprojectionPotential U (softProjection (hardRadius T) y))) x‖ ≤
      (42523 / 10 : ℝ) := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < hardRadius T := by unfold hardRadius; positivity
  have hcomp := norm_second_fderiv_comp_le (contDiff_hardPreprojectionPotential_two U)
    (contDiff_softProjection_two hR) x
  have hf2 := norm_second_fderiv_hardPreprojectionPotential_le_4252 hU (softProjection (hardRadius T) x)
  have hf1 := norm_fderiv_hardPreprojectionPotential_le hU (softProjection (hardRadius T) x)
  have hg1 := norm_fderiv_softProjection_le_one hR x
  have hg2 := norm_second_fderiv_softProjection_le_six_div_radius hR x
  have hg1sq : ‖fderiv ℝ (softProjection (hardRadius T)) x‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [norm_nonneg (fderiv ℝ (softProjection (hardRadius T)) x)]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (hardPreprojectionPotential U)) (softProjection (hardRadius T) x)‖ *
        ‖fderiv ℝ (softProjection (hardRadius T)) x‖ ^ 2 +
        ‖fderiv ℝ (hardPreprojectionPotential U) (softProjection (hardRadius T) x)‖ *
        ‖fderiv ℝ (fderiv ℝ (softProjection (hardRadius T))) x‖ := hcomp
    _ ≤ 4252 * 1 + (23 * Real.sqrt T + 100) * (6 / hardRadius T) := by
      exact add_le_add (mul_le_mul hf2 hg1sq (sq_nonneg _) (by norm_num))
        (mul_le_mul hf1 hg2 (ContinuousLinearMap.opNorm_nonneg _) (by positivity))
    _ = 4252 + 6 * ((23 * Real.sqrt T + 100) / hardRadius T) := by ring
    _ ≤ 42523 / 10 := by linarith [hardPreprojection_gradient_over_radius_le hT]

theorem hasFDerivAt_hardQuadratic {d : ℕ} (x : Point d) :
    HasFDerivAt (fun y : Point d => (1 / 10 : ℝ) * ‖y‖ ^ 2) ((1 / 5 : ℝ) • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (1 / 10 : ℝ)
  convert! h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  ring

theorem norm_second_fderiv_hardQuadratic_le {d : ℕ} (x : Point d) :
    ‖fderiv ℝ (fderiv ℝ (fun y : Point d => (1 / 10 : ℝ) * ‖y‖ ^ 2)) x‖ ≤ (1 / 5 : ℝ) := by
  have heq : fderiv ℝ (fun y : Point d => (1 / 10 : ℝ) * ‖y‖ ^ 2) =
      (fun y => (1 / 5 : ℝ) • innerSL ℝ y) := funext fun y => (hasFDerivAt_hardQuadratic y).fderiv
  rw [heq]
  have hd : HasFDerivAt (fun y : Point d => (1 / 5 : ℝ) • innerSL ℝ y)
      ((1 / 5 : ℝ) • realInnerLinearMap d) x := (realInnerLinearMap d).hasFDerivAt.const_smul (1 / 5 : ℝ)
  rw [hd.fderiv]
  have hi : ‖realInnerLinearMap d‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    simp [innerSL_apply_norm]
  calc
    _ ≤ |(1 / 5 : ℝ)| * ‖realInnerLinearMap d‖ := by
      simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le (1 / 5 : ℝ) (realInnerLinearMap d)
    _ ≤ 1 / 5 := by norm_num; linarith

/-- Global Hessian bound for the exact unscaled hard objective; `0<T` is `T≥1`. -/
theorem norm_second_fderiv_hardPotential_le_4300 {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d) :
    ‖fderiv ℝ (fderiv ℝ (hardPotential U)) x‖ ≤ 4300 := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < hardRadius T := by unfold hardRadius; positivity
  have hf : ContDiff ℝ 2 (fun y : Point d => hardPreprojectionPotential U (softProjection (hardRadius T) y)) :=
    (contDiff_hardPreprojectionPotential_two U).comp (contDiff_softProjection_two hR)
  have hq : ContDiff ℝ 2 (fun y : Point d => (1 / 10 : ℝ) * ‖y‖ ^ 2) :=
    contDiff_const.mul (contDiff_id.norm_sq ℝ)
  have heq : fderiv ℝ (hardPotential U) = (fun y =>
      fderiv ℝ (fun z => hardPreprojectionPotential U (softProjection (hardRadius T) z)) y +
        fderiv ℝ (fun z : Point d => (1 / 10 : ℝ) * ‖z‖ ^ 2) y) := by
    funext y
    exact fderiv_fun_add (hf.differentiable (by norm_num) y) (hq.differentiable (by norm_num) y)
  rw [heq, fderiv_fun_add
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
    ((hq.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (fun y => hardPreprojectionPotential U (softProjection (hardRadius T) y))) x‖ +
        ‖fderiv ℝ (fderiv ℝ (fun y : Point d => (1 / 10 : ℝ) * ‖y‖ ^ 2)) x‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ (42523 / 10 : ℝ) + 1 / 5 := add_le_add
      (norm_second_fderiv_projected_prepotential_le hU hT x) (norm_second_fderiv_hardQuadratic_le x)
    _ ≤ 4300 := by norm_num

/-- Global gradient difference bound in the actual Euclidean norm. -/
theorem norm_gradient_hardPotential_sub_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x y : Point d) :
    ‖gradient (hardPotential U) x - gradient (hardPotential U) y‖ ≤ 4300 * ‖x - y‖ := by
  have hf : Differentiable ℝ (fderiv ℝ (hardPotential U)) :=
    ((contDiff_hardPotential_two hT U).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hL : LipschitzWith (4300 : NNReal) (fderiv ℝ (hardPotential U)) :=
    lipschitzWith_of_nnnorm_fderiv_le hf (fun z => by exact_mod_cast norm_second_fderiv_hardPotential_le_4300 hU hT z)
  have hn : ‖gradient (hardPotential U) x - gradient (hardPotential U) y‖ =
      ‖fderiv ℝ (hardPotential U) x - fderiv ℝ (hardPotential U) y‖ := by
    simp [gradient, ← map_sub]
  rw [hn]
  simpa using hL.norm_sub_le x y

/-- Global gradient Lipschitz regularity, using the native Euclidean metric. -/
theorem lipschitzWith_gradient_hardPotential {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) :
    LipschitzWith (4300 : NNReal) (gradient (hardPotential U)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [dist_eq_norm] using norm_gradient_hardPotential_sub_le hU hT x y

end

end HeavyTailedNoise
