import HeavyTailedNoise.Lower.Gated.SupportResidualSelectorGradient

/-!
Final first-order residual estimate for the actual gated construction.
The exact safe Glaeser constant is 14784/5 = 2956.8, which gives
8 + (14784/5)/32 = 502/5 = 100.4. The authoritative residual and Q
definitions remain in `SupportResidualGate`.
-/

namespace HeavyTailedNoise

open Set Filter
open scoped BigOperators Topology

noncomputable section

theorem abs_second_deriv_carmonOmegaSix_le (t : ℝ) :
    |deriv (deriv carmonOmegaSix) t| ≤ (7392 / 5 : ℝ) := by
  have h := abs_second_deriv_stepWindow_le (a := (1 / 16 : ℝ)) (w := (1 / 16 : ℝ))
    (by norm_num) (by norm_num) t
  norm_num at h
  exact h

theorem carmonOmegaSix_complement_glaeser (t : ℝ) :
    (deriv carmonOmegaSix t) ^ 2 ≤ (14784 / 5 : ℝ) * (1 - carmonOmegaSix t) := by
  have hc : ContDiff ℝ 2 (fun u => 1 - carmonOmegaSix u) :=
    contDiff_const.sub contDiff_carmonOmegaSix_two
  have h2 (u : ℝ) : |deriv (deriv (fun v => 1 - carmonOmegaSix v)) u| ≤ (7392 / 5 : ℝ) := by
    rw [deriv_const_sub', deriv.fun_neg, abs_neg]
    exact abs_second_deriv_carmonOmegaSix_le u
  have h := scalar_glaeser hc (fun u => sub_nonneg.mpr (carmonOmegaSix_le_one u))
    (by norm_num : (0 : ℝ) < 7392 / 5) h2 t
  rw [deriv_const_sub, neg_sq] at h
  convert h using 1 <;> ring

theorem deriv_carmonOmegaSix_eq_zero_of_abs_ge {t : ℝ} (ht : 1 / 8 ≤ |t|) :
    deriv carmonOmegaSix t = 0 := by
  have hflat : ZeroTwoJet (fun u => 1 - carmonOmegaSix u) t :=
    stepWindow_complement_zeroTwoJet (by norm_num) (by norm_num) (by linarith)
  have hd : deriv (fun u => 1 - carmonOmegaSix u) t = 0 := by
    simpa using hflat.first.hasDerivAt.deriv
  rw [deriv_const_sub] at hd
  linarith

theorem omegaSix_deriv_coordinate_sq_le (t : ℝ) :
    (deriv carmonOmegaSix t * t ^ 2) ^ 2 ≤
      (231 / 5 : ℝ) * (1 - carmonOmegaSix t) * t ^ 2 := by
  by_cases ht : |t| ≤ 1 / 8
  · have hsq : t ^ 2 ≤ (1 / 64 : ℝ) := by
      have h := (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1 / 8)).mpr ht
      norm_num [sq_abs] at h
      exact h
    have hg := carmonOmegaSix_complement_glaeser t
    have hb : 0 ≤ 1 - carmonOmegaSix t := sub_nonneg.mpr (carmonOmegaSix_le_one t)
    calc
      _ = (deriv carmonOmegaSix t) ^ 2 * t ^ 2 * t ^ 2 := by ring
      _ ≤ ((14784 / 5 : ℝ) * (1 - carmonOmegaSix t)) * t ^ 2 * (1 / 64) := by gcongr
      _ = _ := by ring
  · have hge : (1 / 8 : ℝ) ≤ |t| := (lt_of_not_ge ht).le
    simp [deriv_carmonOmegaSix_eq_zero_of_abs_ge hge, carmonOmegaSix_one hge]

/-- The exact coefficient of a remaining chain coordinate in Dσ. -/
def residualCoordinateGradient (t : ℝ) : ℝ :=
  2 * (1 - carmonOmegaSix t) * t - deriv carmonOmegaSix t * t ^ 2

theorem residualCoordinateGradient_sq_le (t : ℝ) :
    (residualCoordinateGradient t) ^ 2 ≤
      (502 / 5 : ℝ) * (1 - carmonOmegaSix t) * t ^ 2 := by
  have hb0 : 0 ≤ 1 - carmonOmegaSix t := sub_nonneg.mpr (carmonOmegaSix_le_one t)
  have hb1 : 1 - carmonOmegaSix t ≤ 1 := by linarith [carmonOmegaSix_nonneg t]
  have hbsq : (1 - carmonOmegaSix t) ^ 2 ≤ 1 - carmonOmegaSix t := by nlinarith
  have hfirst : (2 * (1 - carmonOmegaSix t) * t) ^ 2 ≤
      4 * (1 - carmonOmegaSix t) * t ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hbsq (sq_nonneg t)
    nlinarith
  have hsecond := omegaSix_deriv_coordinate_sq_le t
  calc
    _ ≤ 2 * (2 * (1 - carmonOmegaSix t) * t) ^ 2 +
        2 * (deriv carmonOmegaSix t * t ^ 2) ^ 2 := by
      unfold residualCoordinateGradient
      nlinarith [sq_nonneg (2 * (1 - carmonOmegaSix t) * t + deriv carmonOmegaSix t * t ^ 2)]
    _ ≤ 2 * (4 * (1 - carmonOmegaSix t) * t ^ 2) +
        2 * ((231 / 5 : ℝ) * (1 - carmonOmegaSix t) * t ^ 2) := by gcongr
    _ = _ := by ring

/-- Exact positive-energy decomposition of the already defined σ. -/
theorem gatedResidual_eq_energy {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    gatedResidual U k y = ‖frameOrthogonalResidual U Finset.univ y‖ ^ 2 +
      ∑ i ∈ Finset.univ.filter (k < ·),
        (1 - carmonOmegaSix (frameCoordinates U y i)) * (frameCoordinates U y i) ^ 2 := by
  have hp := frameOrthogonalResidual_norm_sq hU (Finset.univ.filter (· ≤ k)) y
  have hf := frameOrthogonalResidual_norm_sq hU Finset.univ y
  have hpart :
      (∑ i ∈ Finset.univ.filter (· ≤ k), (frameCoordinates U y i) ^ 2) +
      (∑ i ∈ Finset.univ.filter (k < ·), (frameCoordinates U y i) ^ 2) =
        ∑ i : Fin T, (frameCoordinates U y i) ^ 2 := by
    simpa only [not_le] using Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun i : Fin T => i ≤ k) (fun i => (frameCoordinates U y i) ^ 2)
  unfold gatedResidual
  rw [hp, hf]
  simp_rw [sub_mul, one_mul]
  rw [Finset.sum_sub_distrib]
  linarith

private theorem innerSL_real_smul {d : ℕ} (a : ℝ) (u : Point d) :
    innerSL ℝ (a • u) = a • innerSL ℝ u := by
  ext v
  simp only [innerSL_apply_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem innerSL_sum_smul {d : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (v : ι → Point d) :
    innerSL ℝ (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • innerSL ℝ (v i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact innerSL_real_smul _ _

theorem hasFDerivAt_frameResidual_norm_sq {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (y : Point d) :
    HasFDerivAt (fun x => ‖frameOrthogonalResidual U s x‖ ^ 2)
      (innerSL ℝ ((2 : ℝ) • frameOrthogonalResidual U s y)) y := by
  have hi (i : Fin T) : HasFDerivAt (fun x => (frameCoordinates U x i) ^ 2)
      ((2 * frameCoordinates U y i) • innerSL ℝ (U i)) y := by
    have h : HasFDerivAt (fun x => frameCoordinates U x i) (innerSL ℝ (U i)) y :=
      (innerSL ℝ (U i)).hasFDerivAt
    convert! h.fun_mul h using 1 <;> ext v <;>
      simp only [pow_two, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul] <;> ring
  have h := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.sub
    (HasFDerivAt.fun_sum (u := s) (fun i _ => hi i))
  have heq : (fun x => ‖frameOrthogonalResidual U s x‖ ^ 2) =
      (fun x => ‖x‖ ^ 2 - ∑ i ∈ s, (frameCoordinates U x i) ^ 2) :=
    funext (frameOrthogonalResidual_norm_sq hU s)
  rw [heq]
  have hmap : (2 : ℝ) • innerSL ℝ y -
      (∑ i ∈ s, (2 * frameCoordinates U y i) • innerSL ℝ (U i)) =
      innerSL ℝ ((2 : ℝ) • frameOrthogonalResidual U s y) := by
    simp only [frameOrthogonalResidual, innerSL_real_smul, map_sub, innerSL_sum_smul,
      smul_sub, Finset.smul_sum, smul_smul]
  apply h.congr_fderiv
  simpa only [two_smul] using hmap

theorem hasDerivAt_residual_coordinate (t : ℝ) :
    HasDerivAt (fun u => (1 - carmonOmegaSix u) * u ^ 2) (residualCoordinateGradient t) t := by
  have hω := (contDiff_carmonOmegaSix_two.differentiable (by norm_num) t).hasDerivAt
  have h := (hω.const_sub 1).mul ((hasDerivAt_id t).pow 2)
  convert! h using 1 <;> simp only [residualCoordinateGradient, Pi.pow_apply, id_eq] <;> ring

/-- Orthogonal-complement and suffix-coordinate representation of ∇σ. -/
def residualGradientVector {d T : ℕ} (U : Fin T → Point d) (k : Fin T) (y : Point d) : Point d :=
  (2 : ℝ) • frameOrthogonalResidual U Finset.univ y +
    ∑ i ∈ Finset.univ.filter (k < ·), residualCoordinateGradient (frameCoordinates U y i) • U i

theorem hasFDerivAt_gatedResidual {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    HasFDerivAt (gatedResidual U k) (innerSL ℝ (residualGradientVector U k y)) y := by
  have hi (i : Fin T) : HasFDerivAt
      (fun x => (1 - carmonOmegaSix (frameCoordinates U x i)) * (frameCoordinates U x i) ^ 2)
      (residualCoordinateGradient (frameCoordinates U y i) • innerSL ℝ (U i)) y :=
    (hasDerivAt_residual_coordinate _).comp_hasFDerivAt y (innerSL ℝ (U i)).hasFDerivAt
  have h := (hasFDerivAt_frameResidual_norm_sq hU Finset.univ y).fun_add
    (HasFDerivAt.fun_sum (u := Finset.univ.filter (k < ·)) (fun i _ => hi i))
  have heq : gatedResidual U k = (fun x => ‖frameOrthogonalResidual U Finset.univ x‖ ^ 2 +
      ∑ i ∈ Finset.univ.filter (k < ·),
        (1 - carmonOmegaSix (frameCoordinates U x i)) * (frameCoordinates U x i) ^ 2) :=
    funext (gatedResidual_eq_energy hU k)
  rw [heq]
  have hmap : innerSL ℝ ((2 : ℝ) • frameOrthogonalResidual U Finset.univ y) +
      (∑ i ∈ Finset.univ.filter (k < ·),
        residualCoordinateGradient (frameCoordinates U y i) • innerSL ℝ (U i)) =
      innerSL ℝ (residualGradientVector U k y) := by
    simp only [residualGradientVector, map_add, innerSL_sum_smul]
  exact h.congr_fderiv hmap

theorem full_frameResidual_orthogonal {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (y : Point d) (i : Fin T) :
    inner ℝ (frameOrthogonalResidual U Finset.univ y) (U i) = 0 := by
  have hi : U i ∈ selectedFrameSpan U Finset.univ :=
    Submodule.subset_span ⟨i, Finset.mem_univ i, rfl⟩
  exact Submodule.inner_left_of_mem_orthogonal hi
    (frameOrthogonalResidual_mem_orthogonal hU Finset.univ y)

theorem residualGradientVector_norm_sq {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    ‖residualGradientVector U k y‖ ^ 2 =
      4 * ‖frameOrthogonalResidual U Finset.univ y‖ ^ 2 +
        ∑ i ∈ Finset.univ.filter (k < ·), (residualCoordinateGradient (frameCoordinates U y i)) ^ 2 := by
  have hn : ‖∑ i ∈ Finset.univ.filter (k < ·),
      residualCoordinateGradient (frameCoordinates U y i) • U i‖ ^ 2 =
      ∑ i ∈ Finset.univ.filter (k < ·), (residualCoordinateGradient (frameCoordinates U y i)) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa [pow_two] using hU.inner_sum
      (fun i => residualCoordinateGradient (frameCoordinates U y i))
      (fun i => residualCoordinateGradient (frameCoordinates U y i)) (Finset.univ.filter (k < ·))
  have ho : inner ℝ ((2 : ℝ) • frameOrthogonalResidual U Finset.univ y)
      (∑ i ∈ Finset.univ.filter (k < ·), residualCoordinateGradient (frameCoordinates U y i) • U i) = 0 := by
    rw [real_inner_smul_left, inner_sum]
    simp only [inner_smul_right, full_frameResidual_orthogonal hU, mul_zero,
      Finset.sum_const_zero]
  unfold residualGradientVector
  rw [norm_add_sq_real, ho, hn, norm_smul]
  norm_num <;> ring

/-- The full global residual-gradient energy bound, with the exact safe constant. -/
theorem norm_fderiv_gatedResidual_sq_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    ‖fderiv ℝ (gatedResidual U k) y‖ ^ 2 ≤ (502 / 5 : ℝ) * gatedResidual U k y := by
  rw [(hasFDerivAt_gatedResidual hU k y).fderiv, innerSL_apply_norm,
    residualGradientVector_norm_sq hU, gatedResidual_eq_energy hU]
  have hs : (∑ i ∈ Finset.univ.filter (k < ·),
      (residualCoordinateGradient (frameCoordinates U y i)) ^ 2) ≤
      (502 / 5 : ℝ) * ∑ i ∈ Finset.univ.filter (k < ·),
        (1 - carmonOmegaSix (frameCoordinates U y i)) * (frameCoordinates U y i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_assoc] using residualCoordinateGradient_sq_le (frameCoordinates U y i)
  nlinarith [sq_nonneg ‖frameOrthogonalResidual U Finset.univ y‖]

theorem carmonChi_deriv_ne_zero_support {s : ℝ} (hs : deriv carmonChi s ≠ 0) :
    (1 / 16 : ℝ) < s ∧ s < 1000 + 1 / 16 := by
  constructor
  · by_contra h
    have harg : (s - 1 / 16) / 1000 ≤ (0 : ℝ) := by linarith
    apply hs
    rw [deriv_carmonChi, deriv_smoothstep_formula, if_pos harg]
    norm_num
  · by_contra h
    have harg : (1 : ℝ) ≤ (s - 1 / 16) / 1000 := by linarith
    have harg0 : ¬(s - 1 / 16) / 1000 ≤ (0 : ℝ) := by linarith
    apply hs
    rw [deriv_carmonChi, deriv_smoothstep_formula, if_neg harg0, if_pos harg]
    norm_num

theorem norm_fderiv_gatedResidual_le_on_chi_deriv_support
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d)
    (hχ : deriv carmonChi (gatedResidual U k y) ≠ 0) :
    ‖fderiv ℝ (gatedResidual U k) y‖ ≤ (3169 / 10 : ℝ) := by
  have hσ := (carmonChi_deriv_ne_zero_support hχ).2.le
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3169 / 10)).mp
  calc
    _ ≤ (502 / 5 : ℝ) * gatedResidual U k y := norm_fderiv_gatedResidual_sq_le hU k y
    _ ≤ (502 / 5 : ℝ) * (1000 + 1 / 16) := mul_le_mul_of_nonneg_left hσ (by norm_num)
    _ ≤ (3169 / 10 : ℝ) ^ 2 := by norm_num

/-- Complete dimension-independent first-order bound for the actual Q.
All scalar and component-gradient premises have been discharged. -/
theorem norm_gradient_gatedCorrection_le_100_of_orthonormal
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (y : Point d) :
    ‖gradient (gatedCorrection U) y‖ ≤ 100 := by
  apply norm_gradient_gatedCorrection_le_100_of_residual_bounds hU y
  intro k hk hχ
  exact norm_fderiv_gatedResidual_le_on_chi_deriv_support hU k y hχ

end

end HeavyTailedNoise
