import HeavyTailedNoise.Lower.Gated.HardProjectionDerivative

/-!
Operator-norm contraction of the exact radial soft projection.  This is a
separate quantitative obligation from its already checked derivative formula.
-/

namespace HeavyTailedNoise

noncomputable section

private theorem softProjection_coeff_le_scale {d : ℕ} {R : ℝ}
    (hR : 0 < R) (x : Point d) :
    let B : ℝ := 1 + ‖x‖ ^ 2 / R ^ 2
    let a : ℝ := (Real.sqrt B)⁻¹
    let c : ℝ := 1 / (R ^ 2 * B * Real.sqrt B)
    0 < a ∧ a ≤ 1 ∧ 0 ≤ c ∧ c * ‖x‖ ^ 2 ≤ a := by
  dsimp
  let B : ℝ := 1 + ‖x‖ ^ 2 / R ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hden : 0 < R ^ 2 * B * Real.sqrt B := by positivity
  have hbase : R ^ 2 * B = R ^ 2 + ‖x‖ ^ 2 := by
    dsimp [B]
    field_simp [hR.ne']
  have hfrac :
      ‖x‖ ^ 2 / (R ^ 2 * B * Real.sqrt B) ≤
        1 / Real.sqrt B := by
    apply (div_le_iff₀ hden).2
    calc
      ‖x‖ ^ 2 ≤ R ^ 2 * B := by rw [hbase]; nlinarith [sq_nonneg R]
      _ = (1 / Real.sqrt B) * (R ^ 2 * B * Real.sqrt B) := by
        field_simp [hs.ne']
  have hscale := softProjection_scale_pos_le_one hR x
  constructor
  · simpa [B] using hscale.1
  constructor
  · simpa [B] using hscale.2
  constructor
  · positivity
  · simpa [B, div_eq_mul_inv, mul_comm] using hfrac

private theorem norm_fderiv_softProjection_apply_le {d : ℕ} {R : ℝ}
    (hR : 0 < R) (x v : Point d) :
    ‖fderiv ℝ (softProjection R) x v‖ ≤ ‖v‖ := by
  let B : ℝ := 1 + ‖x‖ ^ 2 / R ^ 2
  let a : ℝ := (Real.sqrt B)⁻¹
  let c : ℝ := 1 / (R ^ 2 * B * Real.sqrt B)
  let t : ℝ := inner ℝ x v
  have hcoeff := softProjection_coeff_le_scale hR x
  have ha : 0 < a := by simpa [a, B] using hcoeff.1
  have ha1 : a ≤ 1 := by simpa [a, B] using hcoeff.2.1
  have hc : 0 ≤ c := by simpa [c, B] using hcoeff.2.2.1
  have hcn : c * ‖x‖ ^ 2 ≤ a := by
    simpa [a, c, B] using hcoeff.2.2.2
  have hvec :
      fderiv ℝ (softProjection R) x v = a • v - (c * t) • x := by
    rw [fderiv_softProjection_apply hR]
    simp [a, c, t, B, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hinner : inner ℝ (a • v) ((c * t) • x) = a * c * t ^ 2 := by
    simp [real_inner_smul_left, inner_smul_right, real_inner_comm,
      t, pow_two]
    ring
  have hnorm_a : ‖a • v‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    ring
  have hnorm_c : ‖(c * t) • x‖ ^ 2 = (c * t) ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [sq_abs (c * t)]
  have hnormsq :
      ‖fderiv ℝ (softProjection R) x v‖ ^ 2 =
        a ^ 2 * ‖v‖ ^ 2 - c * (2 * a - c * ‖x‖ ^ 2) * t ^ 2 := by
    rw [hvec, norm_sub_sq_real, hnorm_a, hnorm_c, hinner]
    ring
  have hdrop : 0 ≤ c * (2 * a - c * ‖x‖ ^ 2) * t ^ 2 :=
    mul_nonneg (mul_nonneg hc (by linarith)) (sq_nonneg t)
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hsmall : a ^ 2 * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg ‖v‖)]
  have hsq : ‖fderiv ℝ (softProjection R) x v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    linarith [hnormsq, hdrop, hsmall]
  nlinarith [norm_nonneg (fderiv ℝ (softProjection R) x v), norm_nonneg v]

/-- The manuscript's first operator estimate `‖Dρ_R(x)‖≤1`. -/
theorem norm_fderiv_softProjection_le_one {d : ℕ} {R : ℝ}
    (hR : 0 < R) (x : Point d) :
    ‖fderiv ℝ (softProjection R) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa using norm_fderiv_softProjection_apply_le hR x v

end

end HeavyTailedNoise
