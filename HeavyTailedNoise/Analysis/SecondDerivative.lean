import HeavyTailedNoise.Model.Basic

namespace HeavyTailedNoise

open Set Filter
open scoped BigOperators Topology Classical
noncomputable section

theorem hasFDerivAt_fderiv_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    HasFDerivAt (fderiv ℝ (fun y => f y * g y))
      ((f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x)) +
       (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))) x := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hfdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hgdd := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun y => f y * g y) =
      (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) :=
    funext fun y => fderiv_fun_mul (hfd y) (hgd y)
  rw [heq]
  exact ((hfd x).hasFDerivAt.fun_smul (hgdd x).hasFDerivAt).fun_add
    ((hgd x).hasFDerivAt.fun_smul (hfdd x).hasFDerivAt)

theorem norm_second_fderiv_mul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ (fderiv ℝ g) x‖ +
      ‖g x‖ * ‖fderiv ℝ (fderiv ℝ f) x‖ +
      2 * ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖ := by
  rw [(hasFDerivAt_fderiv_mul hf hg x).fderiv]
  calc
    _ ≤ ‖f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x)‖ +
        ‖g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ (‖f x • fderiv ℝ (fderiv ℝ g) x‖ + ‖(fderiv ℝ f x).smulRight (fderiv ℝ g x)‖) +
        (‖g x • fderiv ℝ (fderiv ℝ f) x‖ + ‖(fderiv ℝ g x).smulRight (fderiv ℝ f x)‖) :=
      add_le_add (ContinuousLinearMap.opNorm_add_le _ _) (ContinuousLinearMap.opNorm_add_le _ _)
    _ ≤ (‖f x‖ * ‖fderiv ℝ (fderiv ℝ g) x‖ + ‖fderiv ℝ f x‖ * ‖fderiv ℝ g x‖) +
        (‖g x‖ * ‖fderiv ℝ (fderiv ℝ f) x‖ + ‖fderiv ℝ g x‖ * ‖fderiv ℝ f x‖) := by
      simp only [ContinuousLinearMap.norm_smulRight_apply]
      exact add_le_add (add_le_add (ContinuousLinearMap.opNorm_smul_le _ _) le_rfl)
        (add_le_add (ContinuousLinearMap.opNorm_smul_le _ _) le_rfl)
    _ = _ := by
      ring

theorem hasFDerivAt_fderiv_scalar_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ → ℝ} {g : E → ℝ} (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (x : E) :
    HasFDerivAt (fderiv ℝ (fun y => h (g y)))
      (deriv h (g x) • fderiv ℝ (fderiv ℝ g) x +
        (deriv (deriv h) (g x) • fderiv ℝ g x).smulRight (fderiv ℝ g x)) x := by
  have hgd := hg.differentiable (by norm_num)
  have hgdd := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun y => h (g y)) =
      (fun y => deriv h (g y) • fderiv ℝ g y) := by
    funext y
    exact ((hh.differentiable (by norm_num) (g y)).hasDerivAt.comp_hasFDerivAt y
      (hgd y).hasFDerivAt).fderiv
  rw [heq]
  exact (((hh.differentiable_deriv_two (g x)).hasDerivAt.comp_hasFDerivAt x
    (hgd x).hasFDerivAt).fun_smul (hgdd x).hasFDerivAt)

theorem norm_second_fderiv_scalar_comp_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ → ℝ} {g : E → ℝ} (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun y => h (g y))) x‖ ≤
      |deriv h (g x)| * ‖fderiv ℝ (fderiv ℝ g) x‖ +
      |deriv (deriv h) (g x)| * ‖fderiv ℝ g x‖ ^ 2 := by
  rw [(hasFDerivAt_fderiv_scalar_comp hh hg x).fderiv]
  calc
    _ ≤ ‖deriv h (g x) • fderiv ℝ (fderiv ℝ g) x‖ +
        ‖(deriv (deriv h) (g x) • fderiv ℝ g x).smulRight (fderiv ℝ g x)‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ |deriv h (g x)| * ‖fderiv ℝ (fderiv ℝ g) x‖ +
        |deriv (deriv h) (g x)| * ‖fderiv ℝ g x‖ * ‖fderiv ℝ g x‖ := by
      simp only [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
      apply add_le_add _ le_rfl
      simpa only [Real.norm_eq_abs] using
        ContinuousLinearMap.opNorm_smul_le (deriv h (g x)) (fderiv ℝ (fderiv ℝ g) x)
    _ = _ := by
      ring

theorem norm_second_fderiv_const_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (c : ℝ) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun y => c - f y)) x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  have heq : fderiv ℝ (fun y => c - f y) = (fun y => -fderiv ℝ f y) :=
    funext fun y => fderiv_const_sub c
  rw [heq, fderiv_fun_neg]
  exact ContinuousLinearMap.opNorm_neg _


end

end HeavyTailedNoise
