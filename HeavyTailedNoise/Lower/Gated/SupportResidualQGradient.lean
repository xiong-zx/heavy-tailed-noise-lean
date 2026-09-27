import HeavyTailedNoise.Lower.Gated.SupportResidualGradientBounds
import HeavyTailedNoise.Analysis.CarmonScalarBounds

/-!
Euclidean first-derivative bound for the actual q_k pullback. The coordinate
type `Fin T → ℝ` has the sup norm; its dual norm is not the Euclidean gradient
norm used by the frozen bound 30. Accordingly the quantitative theorem is
stated directly on the shared ambient Euclidean space `Point d`.
-/

namespace HeavyTailedNoise

open Filter
open scoped Topology

noncomputable section

theorem abs_deriv_stepWindow_le {a w : ℝ} (ha : 0 < a) (hw : 0 < w) (z : ℝ) :
    |deriv (stepWindow a w) z| ≤ (15 / 8 : ℝ) / w := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · have harg := ((hasDerivAt_abs_neg hz).sub_const a).div_const w
    have h := ((differentiable_smoothstep _).hasDerivAt).comp z harg
    have heq : deriv (stepWindow a w) z =
        deriv smoothstep ((|z| - a) / w) * (-1 / w) := h.deriv
    rw [heq, abs_mul, abs_div, abs_of_pos hw]
    norm_num only [abs_neg, abs_one]
    calc
      _ ≤ (15 / 8 : ℝ) * (1 / w) :=
        mul_le_mul_of_nonneg_right (abs_deriv_smoothstep_le _) (by positivity)
      _ = _ := by ring
  · have hlocal := stepWindow_eventually_zero hw (show |(0 : ℝ)| < a by simpa using ha)
    have hd : HasDerivAt (stepWindow a w) 0 0 :=
      (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).congr_of_eventuallyEq hlocal
    rw [hd.deriv, abs_zero]
    positivity
  · have harg := ((hasDerivAt_abs_pos hz).sub_const a).div_const w
    have h := ((differentiable_smoothstep _).hasDerivAt).comp z harg
    have heq : deriv (stepWindow a w) z =
        deriv smoothstep ((|z| - a) / w) * (1 / w) := h.deriv
    rw [heq, abs_mul, abs_div, abs_of_pos hw]
    norm_num only [abs_one]
    calc
      _ ≤ (15 / 8 : ℝ) * (1 / w) :=
        mul_le_mul_of_nonneg_right (abs_deriv_smoothstep_le _) (by positivity)
      _ = _ := by ring

theorem abs_deriv_carmonOmega_le (t : ℝ) : |deriv carmonOmega t| ≤ 5 := by
  have h := abs_deriv_stepWindow_le (a := (1 / 8 : ℝ)) (w := (3 / 8 : ℝ))
    (by norm_num) (by norm_num) t
  norm_num at h
  exact h

def frontierPrevCoefficient (a b : ℝ) : ℝ :=
  (deriv carmonPsi a * (carmonPhi b - carmonPhi 0 + 1) -
    deriv carmonPsi (-a) * (carmonPhi 0 - carmonPhi (-b) + 1)) * (1 - carmonOmega b)

/-- The exact partial derivative with respect to the current coordinate. -/
def frontierCurrentCoefficient (a b : ℝ) : ℝ :=
  (carmonPsi a * deriv carmonPhi b + carmonPsi (-a) * deriv carmonPhi (-b)) *
      (1 - carmonOmega b) -
    (carmonPsi a * (carmonPhi b - carmonPhi 0 + 1) +
      carmonPsi (-a) * (carmonPhi 0 - carmonPhi (-b) + 1)) * deriv carmonOmega b

theorem correction_bracket_abs_bounds {b : ℝ} (hb : |b| < 1 / 2) :
    |carmonPhi b - carmonPhi 0 + 1| ≤ (224 / 125 : ℝ) ∧
      |carmonPhi 0 - carmonPhi (-b) + 1| ≤ (224 / 125 : ℝ) := by
  obtain ⟨hA, hB⟩ := carmonPhi_correction_brackets_pos hb
  have hi := abs_lt.mp (carmonPhi_local_increment_abs_lt hb.le)
  have hin := abs_lt.mp (carmonPhi_local_increment_abs_lt (t := -b) (by simpa using hb.le))
  rw [abs_of_pos hA, abs_of_pos hB]
  constructor <;> linarith

theorem abs_one_sub_carmonOmega_le (b : ℝ) : |1 - carmonOmega b| ≤ 1 := by
  have h0 : 0 ≤ carmonOmega b := smoothstep_nonneg _
  have h1 : carmonOmega b ≤ 1 := smoothstep_le_one _
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  linarith

theorem abs_frontierPrevCoefficient_le
    (hψ : ∀ t : ℝ, |deriv carmonPsi t| ≤ (223 / 50 : ℝ))
    {a b : ℝ} (ha : (1 / 2 : ℝ) < |a|) (hb : |b| < 1 / 2) :
    |frontierPrevCoefficient a b| ≤ 8 := by
  obtain ⟨hA, hB⟩ := correction_bracket_abs_bounds hb
  have hc := abs_one_sub_carmonOmega_le b
  rcases lt_abs.mp ha with ha | ha
  · have hd : deriv carmonPsi (-a) = 0 := deriv_carmonPsi_zero_of_le (by linarith)
    simp only [frontierPrevCoefficient, hd, zero_mul, sub_zero, abs_mul]
    calc
      _ ≤ (223 / 50 : ℝ) * (224 / 125) * 1 := by gcongr; exact hψ a
      _ ≤ 8 := by norm_num
  · have hd : deriv carmonPsi a = 0 := deriv_carmonPsi_zero_of_le (by linarith)
    simp only [frontierPrevCoefficient, hd, zero_mul, zero_sub, abs_mul, abs_neg]
    calc
      _ ≤ (223 / 50 : ℝ) * (224 / 125) * 1 := by gcongr; exact hψ (-a)
      _ ≤ 8 := by norm_num

lemma current_coefficient_numeric_bound {c A d v w : ℝ}
    (hc : |c| ≤ Real.exp 1) (hA : |A| ≤ (224 / 125 : ℝ))
    (hd : |d| ≤ (33 / 20 : ℝ)) (hv : |v| ≤ 1) (hw : |w| ≤ 5) :
    |c * d * v - c * A * w| ≤ (289 / 10 : ℝ) := by
  calc
    _ ≤ |c * d * v| + |c * A * w| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (c * d * v) (c * A * w)
    _ = |c| * |d| * |v| + |c| * |A| * |w| := by simp only [abs_mul]
    _ ≤ Real.exp 1 * (33 / 20 : ℝ) * 1 + Real.exp 1 * (224 / 125) * 5 := by gcongr
    _ ≤ (2.7182818286 : ℝ) * (33 / 20) * 1 + (2.7182818286 : ℝ) * (224 / 125) * 5 := by
      gcongr <;> exact Real.exp_one_lt_d9.le
    _ ≤ 289 / 10 := by norm_num

theorem abs_frontierCurrentCoefficient_le {a b : ℝ}
    (ha : (1 / 2 : ℝ) < |a|) (hb : |b| < 1 / 2) :
    |frontierCurrentCoefficient a b| ≤ (289 / 10 : ℝ) := by
  obtain ⟨hA, hB⟩ := correction_bracket_abs_bounds hb
  have hc := abs_one_sub_carmonOmega_le b
  have hψabs (t : ℝ) : |carmonPsi t| ≤ Real.exp 1 := by
    rw [abs_of_nonneg (carmonPsi_nonneg t)]
    exact carmonPsi_le_exp_one t
  rcases lt_abs.mp ha with ha | ha
  · have hz : carmonPsi (-a) = 0 := carmonPsi_zero_of_le (by linarith)
    simp only [frontierCurrentCoefficient, hz, zero_mul, add_zero]
    exact current_coefficient_numeric_bound (hψabs a) hA (abs_deriv_carmonPhi_le b) hc
      (abs_deriv_carmonOmega_le b)
  · have hz : carmonPsi a = 0 := carmonPsi_zero_of_le (by linarith)
    simp only [frontierCurrentCoefficient, hz, zero_mul, zero_add]
    exact current_coefficient_numeric_bound (hψabs (-a)) hB (abs_deriv_carmonPhi_le (-b)) hc
      (abs_deriv_carmonOmega_le b)

/-- Chain rule exposing the two scalar partial coefficients; no norm change. -/
theorem hasFDerivAt_frontierCorrection_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {a' b' : E →L[ℝ] ℝ} {x : E}
    (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (fun y => frontierCorrection carmonPsi carmonPhi carmonOmega 1 (a y) (b y))
      (frontierPrevCoefficient (a x) (b x) • a' +
        frontierCurrentCoefficient (a x) (b x) • b') x := by
  have hψa := ((contDiff_carmonPsi_two.differentiable (by norm_num) (a x)).hasDerivAt).comp_hasFDerivAt
    x ha
  have hψn := ((contDiff_carmonPsi_two.differentiable (by norm_num) (-a x)).hasDerivAt).comp_hasFDerivAt
    x ha.fun_neg
  have hφb := ((differentiable_carmonPhi (b x)).hasDerivAt).comp_hasFDerivAt x hb
  have hφn := ((differentiable_carmonPhi (-b x)).hasDerivAt).comp_hasFDerivAt x hb.fun_neg
  have hω := ((contDiff_carmonOmega_two.differentiable (by norm_num) (b x)).hasDerivAt).comp_hasFDerivAt
    x hb
  have h := ((hψa.fun_mul ((hφb.sub_const (carmonPhi 0)).add_const 1)).fun_add
    (hψn.fun_mul ((hφn.const_sub (carmonPhi 0)).add_const 1))).fun_mul (hω.const_sub 1)
  convert! h using 1 <;> ext v <;>
    simp only [frontierCorrection, frontierPrevCoefficient, frontierCurrentCoefficient,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      Function.comp_apply, Pi.neg_apply, smul_eq_mul] <;> ring

/-- The first predecessor is constant, hence its ambient derivative vector is zero. -/
theorem norm_two_orthogonal_coefficients_lt_30 {d : ℕ} {u v : Point d} {A B : ℝ}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (huv : inner ℝ u v = 0)
    (hA : |A| ≤ 8) (hB : |B| ≤ (289 / 10 : ℝ)) :
    ‖A • u + B • v‖ < 30 := by
  have hAu : ‖A • u‖ ≤ 8 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (8 : ℝ) * 1 := by gcongr
      _ = _ := by ring
  have hBv : ‖B • v‖ ≤ (289 / 10 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (289 / 10 : ℝ) * 1 := by gcongr
      _ = _ := by ring
  have hsqA := (sq_le_sq₀ (norm_nonneg (A • u)) (by norm_num : (0 : ℝ) ≤ 8)).mpr hAu
  have hsqB := (sq_le_sq₀ (norm_nonneg (B • v)) (by norm_num : (0 : ℝ) ≤ 289 / 10)).mpr hBv
  apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 30)).mp
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, huv]
  nlinarith

/-- Ambient Euclidean q-gradient bound, conditional only on the exact scalar
Ψ' estimate while its separate module is being completed. -/
theorem norm_fderiv_chainCorrection_pullback_lt_30_of_psi_bound
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U)
    (hψ : ∀ t : ℝ, |deriv carmonPsi t| ≤ (223 / 50 : ℝ))
    (k : Fin T) (y : Point d)
    (hactive : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0) :
    ‖fderiv ℝ (fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
      (frameCoordinates U x) k) y‖ < 30 := by
  let a := chainPredecessor (frameCoordinates U y) k
  let b := frameCoordinates U y k
  have hcur : HasFDerivAt (fun x => frameCoordinates U x k) (innerSL ℝ (U k)) y :=
    (innerSL ℝ (U k)).hasFDerivAt
  have hd := hasFDerivAt_frontierCorrection_comp (hasFDerivAt_chainPredecessor_pullback U k y) hcur
  have hmap : frontierPrevCoefficient a b • innerSL ℝ (chainPredecessorVector U k) +
      frontierCurrentCoefficient a b • innerSL ℝ (U k) =
      innerSL ℝ (frontierPrevCoefficient a b • chainPredecessorVector U k +
        frontierCurrentCoefficient a b • U k) := by
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, inner_add_left, real_inner_smul_left, smul_eq_mul]
  rw [show fderiv ℝ (fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
      (frameCoordinates U x) k) y = _ from hd.fderiv, hmap, innerSL_apply_norm]
  obtain ⟨ha, hb, _⟩ := chainGateTerm_support (fun _ ht => carmonPsi_zero_of_le ht)
    (fun _ ht => carmonOmega_one ht) (fun _ ht => carmonOmegaThree_one ht) hactive
  exact norm_two_orthogonal_coefficients_lt_30 (chainPredecessorVector_norm_le hU k)
    (hU.norm_eq_one k).le (chainPredecessorVector_orthogonal hU k)
    (abs_frontierPrevCoefficient_le hψ ha hb) (abs_frontierCurrentCoefficient_le ha hb)

/-- The scalar Ψ' premise is discharged by the exact checked Carmon bound. -/
theorem norm_fderiv_chainCorrection_pullback_lt_30
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U)
    (k : Fin T) (y : Point d)
    (hactive : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0) :
    ‖fderiv ℝ (fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
      (frameCoordinates U x) k) y‖ < 30 := by
  apply norm_fderiv_chainCorrection_pullback_lt_30_of_psi_bound hU _ k y hactive
  intro t
  rw [abs_of_nonneg (deriv_carmonPsi_nonneg t)]
  exact (deriv_carmonPsi_lt_446 t).le

/-- After the q-gradient estimate, only the selector-product and residual
gradient estimates remain in the dimension-independent Q bound. -/
theorem norm_gradient_gatedCorrection_le_100_of_selector_residual_bounds
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (y : Point d)
    (hbounds : ∀ k : Fin T,
      chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
        (frameCoordinates U y) k ≠ 0 →
      ‖fderiv ℝ (fun x => chainSelector carmonOmegaThree (frameCoordinates U x) k) y‖ ≤
          (68 / 5 : ℝ) ∧
      (deriv carmonChi (gatedResidual U k y) ≠ 0 →
        ‖fderiv ℝ (gatedResidual U k) y‖ ≤ (3169 / 10 : ℝ))) :
    ‖gradient (gatedCorrection U) y‖ ≤ 100 := by
  apply norm_gradient_gatedCorrection_le_100_of_derivative_bounds U y
  intro k hk
  exact ⟨(norm_fderiv_chainCorrection_pullback_lt_30 hU k y hk).le, hbounds k hk⟩

end

end HeavyTailedNoise
