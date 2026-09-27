import HeavyTailedNoise.Lower.Gated.HardProjectionOperatorBounds
import HeavyTailedNoise.Lower.Gated.SupportResidualHessian

/-!
Second derivative of the exact radial soft projection. The dimension-free
bound `6/R` suffices for the final `4300` smoothness budget.
-/

namespace HeavyTailedNoise

noncomputable section

def softProjectionScale {d : ℕ} (R : ℝ) (x : Point d) : ℝ :=
  (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹

theorem hasFDerivAt_softProjectionScale {d : ℕ} {R : ℝ} (hR : 0 < R) (x : Point d) :
    HasFDerivAt (softProjectionScale (d := d) R)
      (-(softProjectionScale R x ^ 3 / R ^ 2) • innerSL ℝ x) x := by
  let b : Point d → ℝ := fun y => 1 + ‖y‖ ^ 2 / R ^ 2
  have hbpos : 0 < b x := by dsimp [b]; positivity
  have hb : HasFDerivAt b ((R ^ 2)⁻¹ • (2 • innerSL ℝ x)) x := by
    have hnorm := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have hscale := hnorm.const_smul ((R ^ 2)⁻¹)
    have hsum := (hasFDerivAt_const (1 : ℝ) x).add hscale
    convert hsum using 1
    · funext y
      dsimp [b]
      simp [div_eq_mul_inv, mul_comm]
    · simp
  have hs : 0 < Real.sqrt (b x) := Real.sqrt_pos.mpr hbpos
  have hi := (hasFDerivAt_inv (𝕜 := ℝ) hs.ne').comp x (hb.sqrt hbpos.ne')
  apply hi.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  dsimp [softProjectionScale, b] at *
  field_simp [hR.ne', hs.ne']
  <;> ring

def softProjectionRankBilinear (d : ℕ) : Point d →L[ℝ] Point d →L[ℝ] Point d →L[ℝ] Point d :=
  (ContinuousLinearMap.smulRightL ℝ (Point d) (Point d)).comp (realInnerLinearMap d)

@[simp] theorem softProjectionRankBilinear_apply (d : ℕ) (x y : Point d) :
    softProjectionRankBilinear d x y = (innerSL ℝ x).smulRight y := rfl

def softProjectionRank {d : ℕ} (x : Point d) : Point d →L[ℝ] Point d :=
  softProjectionRankBilinear d x x

def softProjectionRankDerivative {d : ℕ} (x : Point d) :
    Point d →L[ℝ] Point d →L[ℝ] Point d :=
  softProjectionRankBilinear d x + (softProjectionRankBilinear d).flip x

theorem norm_softProjectionRank {d : ℕ} (x : Point d) : ‖softProjectionRank x‖ = ‖x‖ ^ 2 := by
  simp [softProjectionRank, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, pow_two]

theorem norm_softProjectionRankBilinear_left {d : ℕ} (x : Point d) :
    ‖softProjectionRankBilinear d x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
  intro v
  simp [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

theorem norm_softProjectionRankBilinear_right {d : ℕ} (x : Point d) :
    ‖(softProjectionRankBilinear d).flip x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
  intro v
  simp [ContinuousLinearMap.flip_apply, ContinuousLinearMap.norm_smulRight_apply,
    innerSL_apply_norm, mul_comm]

theorem norm_softProjectionRankDerivative_le {d : ℕ} (x : Point d) :
    ‖softProjectionRankDerivative x‖ ≤ 2 * ‖x‖ := by
  unfold softProjectionRankDerivative
  exact (ContinuousLinearMap.opNorm_add_le _ _).trans (by
    have hl := norm_softProjectionRankBilinear_left x
    have hr := norm_softProjectionRankBilinear_right x
    linarith)

theorem hasFDerivAt_softProjectionRank {d : ℕ} (x : Point d) :
    HasFDerivAt (softProjectionRank (d := d)) (softProjectionRankDerivative x) x := by
  have h := (softProjectionRankBilinear d).hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
  apply h.congr_fderiv
  ext h v
  simp [softProjectionRankDerivative, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply]

theorem fderiv_softProjection_eq_rank {d : ℕ} {R : ℝ} (hR : 0 < R) (x : Point d) :
    fderiv ℝ (softProjection R) x =
      softProjectionScale R x • ContinuousLinearMap.id ℝ (Point d) -
        (softProjectionScale R x ^ 3 / R ^ 2) • softProjectionRank x := by
  let B : ℝ := 1 + ‖x‖ ^ 2 / R ^ 2
  let S := Real.sqrt B
  have hB : 0 < B := by dsimp [B]; positivity
  have hS : 0 < S := Real.sqrt_pos.mpr hB
  have hSsq : S ^ 2 = B := Real.sq_sqrt hB.le
  have hc : (1 : ℝ) / (R ^ 2 * B * S) = S⁻¹ ^ 3 / R ^ 2 := by
    rw [← hSsq]
    field_simp [hR.ne', hS.ne']
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_softProjection_apply hR]
  change S⁻¹ • v - (inner ℝ x v / (R ^ 2 * B * S)) • x =
    S⁻¹ • v - (S⁻¹ ^ 3 / R ^ 2) • (inner ℝ x v • x)
  rw [smul_smul]
  congr 2
  calc
    _ = inner ℝ x v * (1 / (R ^ 2 * B * S)) := by ring
    _ = _ := by rw [hc]; ring

theorem hasFDerivAt_softProjectionCoeff {d : ℕ} {R : ℝ} (hR : 0 < R) (x : Point d) :
    HasFDerivAt (fun y : Point d => softProjectionScale R y ^ 3 / R ^ 2)
      (-(3 * softProjectionScale R x ^ 5 / R ^ 4) • innerSL ℝ x) x := by
  have h := ((hasFDerivAt_softProjectionScale hR x).pow 3).const_smul ((R ^ 2)⁻¹)
  convert h using 1
  · funext y
    simp [div_eq_mul_inv, mul_comm]
  · ext v
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    field_simp [hR.ne']
    <;> ring

def softProjectionSecondMap {d : ℕ} (R : ℝ) (x : Point d) :
    Point d →L[ℝ] Point d →L[ℝ] Point d :=
  (-(softProjectionScale R x ^ 3 / R ^ 2) • innerSL ℝ x).smulRight
      (ContinuousLinearMap.id ℝ (Point d)) -
    ((softProjectionScale R x ^ 3 / R ^ 2) • softProjectionRankDerivative x +
      (-(3 * softProjectionScale R x ^ 5 / R ^ 4) • innerSL ℝ x).smulRight
        (softProjectionRank x))

theorem hasFDerivAt_fderiv_softProjection {d : ℕ} {R : ℝ} (hR : 0 < R) (x : Point d) :
    HasFDerivAt (fderiv ℝ (softProjection R)) (softProjectionSecondMap R x) x := by
  have heq : fderiv ℝ (softProjection (d := d) R) = (fun y =>
      softProjectionScale R y • ContinuousLinearMap.id ℝ (Point d) -
        (softProjectionScale R y ^ 3 / R ^ 2) • softProjectionRank y) :=
    funext (fderiv_softProjection_eq_rank hR)
  rw [heq]
  exact ((hasFDerivAt_softProjectionScale hR x).smul_const (ContinuousLinearMap.id ℝ (Point d))).fun_sub
    ((hasFDerivAt_softProjectionCoeff hR x).fun_smul (hasFDerivAt_softProjectionRank x))

theorem softProjection_second_numeric {a r R : ℝ} (hR : 0 < R)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 ≤ r) (har : a * r ≤ R) :
    3 * (a ^ 3 / R ^ 2) * r + (3 * a ^ 5 / R ^ 4) * r ^ 3 ≤ 6 / R := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hleft : a ^ 3 * r ≤ R := by
    calc
      _ = a ^ 2 * (a * r) := by ring
      _ ≤ 1 * R := mul_le_mul ha2 har (mul_nonneg ha hr) (by norm_num)
      _ = R := one_mul R
  have hcube : (a * r) ^ 3 ≤ R ^ 3 := by gcongr
  have hright : a ^ 5 * r ^ 3 ≤ R ^ 3 := by
    calc
      _ = a ^ 2 * (a * r) ^ 3 := by ring
      _ ≤ 1 * R ^ 3 := mul_le_mul ha2 hcube (by positivity) (by norm_num)
      _ = R ^ 3 := one_mul _
  have hleft' : a ^ 3 * r / R ^ 2 ≤ 1 / R := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    convert hleft using 1 <;> field_simp [hR.ne']
  have hright' : a ^ 5 * r ^ 3 / R ^ 4 ≤ 1 / R := by
    apply (div_le_iff₀ (pow_pos hR 4)).mpr
    convert hright using 1 <;> field_simp [hR.ne']
  calc
    _ = 3 * (a ^ 3 * r / R ^ 2) + 3 * (a ^ 5 * r ^ 3 / R ^ 4) := by ring
    _ ≤ 3 * (1 / R) + 3 * (1 / R) := by linarith
    _ = 6 / R := by ring


theorem softProjectionScale_mul_norm_le_radius {d : ℕ} {R : ℝ}
    (hR : 0 < R) (x : Point d) : softProjectionScale R x * ‖x‖ ≤ R := by
  have hscale := (softProjection_scale_pos_le_one hR x).1
  have hnorm : ‖softProjection R x‖ = softProjectionScale R x * ‖x‖ := by
    simp [softProjection, softProjectionScale, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
  rw [← hnorm]
  exact (norm_softProjection_lt_radius hR x).le

/-- Operator accounting for the derivative of a radial rank-one Jacobian. -/
theorem norm_softProjectionSecond_algebra {d : ℕ} (x : Point d) (c e : ℝ)
    (hc : 0 ≤ c) (he : 0 ≤ e) :
    ‖(-c • innerSL ℝ x).smulRight (ContinuousLinearMap.id ℝ (Point d)) -
      (c • softProjectionRankDerivative x + (-e • innerSL ℝ x).smulRight (softProjectionRank x))‖ ≤
      3 * c * ‖x‖ + e * ‖x‖ ^ 3 := by
  let A : Point d →L[ℝ] ℝ := -c • innerSL ℝ x
  let C : Point d →L[ℝ] ℝ := -e • innerSL ℝ x
  have hA : ‖A‖ = c * ‖x‖ := by
    simp only [A, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hc, innerSL_apply_norm]
  have hC : ‖C‖ = e * ‖x‖ := by
    simp only [C, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg he, innerSL_apply_norm]
  have hfirst : ‖A.smulRight (ContinuousLinearMap.id ℝ (Point d))‖ ≤ c * ‖x‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply, hA]
    simpa using mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Point d))
      (mul_nonneg hc (norm_nonneg x))
  have hsecond : ‖c • softProjectionRankDerivative x‖ ≤ c * (2 * ‖x‖) := by
    calc
      _ ≤ |c| * ‖softProjectionRankDerivative x‖ := by
        simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le c (softProjectionRankDerivative x)
      _ ≤ c * (2 * ‖x‖) := by rw [abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left (norm_softProjectionRankDerivative_le x) hc
  have hthird : ‖C.smulRight (softProjectionRank x)‖ = e * ‖x‖ ^ 3 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, hC, norm_softProjectionRank]
    ring
  change ‖A.smulRight (ContinuousLinearMap.id ℝ (Point d)) -
    (c • softProjectionRankDerivative x + C.smulRight (softProjectionRank x))‖ ≤ 3 * c * ‖x‖ + e * ‖x‖ ^ 3
  calc
    _ ≤ ‖A.smulRight (ContinuousLinearMap.id ℝ (Point d))‖ +
        ‖c • softProjectionRankDerivative x + C.smulRight (softProjectionRank x)‖ := by
      have hsub : A.smulRight (ContinuousLinearMap.id ℝ (Point d)) -
          (c • softProjectionRankDerivative x + C.smulRight (softProjectionRank x)) =
          A.smulRight (ContinuousLinearMap.id ℝ (Point d)) +
            -(c • softProjectionRankDerivative x + C.smulRight (softProjectionRank x)) := by
        ext h v i
        simp [sub_eq_add_neg]
      rw [hsub]
      simpa only [ContinuousLinearMap.opNorm_neg] using
        ContinuousLinearMap.opNorm_add_le (A.smulRight (ContinuousLinearMap.id ℝ (Point d)))
          (-(c • softProjectionRankDerivative x + C.smulRight (softProjectionRank x)))
    _ ≤ ‖A.smulRight (ContinuousLinearMap.id ℝ (Point d))‖ +
        (‖c • softProjectionRankDerivative x‖ + ‖C.smulRight (softProjectionRank x)‖) :=
      add_le_add le_rfl (ContinuousLinearMap.opNorm_add_le _ _)
    _ ≤ c * ‖x‖ + (c * (2 * ‖x‖) + e * ‖x‖ ^ 3) := by
      rw [hthird]
      exact add_le_add hfirst (add_le_add hsecond le_rfl)
    _ = 3 * c * ‖x‖ + e * ‖x‖ ^ 3 := by ring

/-- The actual ambient Euclidean second-derivative bound for every positive radius. -/
theorem norm_second_fderiv_softProjection_le_six_div_radius {d : ℕ} {R : ℝ}
    (hR : 0 < R) (x : Point d) :
    ‖fderiv ℝ (fderiv ℝ (softProjection R)) x‖ ≤ 6 / R := by
  let a := softProjectionScale R x
  have ha : 0 ≤ a := (softProjection_scale_pos_le_one hR x).1.le
  have ha1 : a ≤ 1 := (softProjection_scale_pos_le_one hR x).2
  rw [(hasFDerivAt_fderiv_softProjection hR x).fderiv]
  exact (norm_softProjectionSecond_algebra x (a ^ 3 / R ^ 2) (3 * a ^ 5 / R ^ 4)
    (by positivity) (by positivity)).trans
      (softProjection_second_numeric hR ha ha1 (norm_nonneg x) (softProjectionScale_mul_norm_le_radius hR x))

end

end HeavyTailedNoise
