import HeavyTailedNoise.Analysis.CarmonScalar

/-!
Elementary global bounds on the manuscript's exact Carmon cutoff. Stronger
uniform first- and second-derivative constants remain separate obligations.
-/

namespace HeavyTailedNoise

theorem carmonPsi_lt_exp_one (t : ℝ) : carmonPsi t < Real.exp 1 := by
  rcases le_or_gt t (1 / 2) with ht | ht
  · rw [carmonPsi_zero_of_le ht]
    exact Real.exp_pos _
  · rw [carmonPsi_eq_exp_of_gt ht]
    have hpos : 0 < 2 * t - 1 := by linarith
    have hinv : 0 < (2 * t - 1)⁻¹ := inv_pos.mpr hpos
    apply Real.exp_lt_exp.mpr
    nlinarith [sq_pos_of_pos hinv]

theorem deriv_carmonPsi_nonneg (t : ℝ) : 0 ≤ deriv carmonPsi t := by
  rw [deriv_carmonPsi]
  by_cases h : 2 * t - 1 ≤ 0
  · rw [carmonPsiBaseFirst_zero_of_nonpos h]
    norm_num
  · rw [carmonPsiBaseFirst_eq_of_pos (lt_of_not_ge h)]
    have hinv : 0 ≤ (2 * t - 1)⁻¹ := (inv_pos.mpr (lt_of_not_ge h)).le
    positivity

/-- An exact finite-series certificate for the decimal rounding in the
first-derivative bound. -/
theorem exp_one_ge_163_div_60 : (163 / 60 : ℝ) ≤ Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  exact h

theorem sqrt_54_div_exp_one_lt_446 :
    Real.sqrt (54 / Real.exp 1) < (223 / 50 : ℝ) := by
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 223 / 50)).2
  apply (div_lt_iff₀ hpos).2
  nlinarith [exp_one_ge_163_div_60]

private theorem carmonPsi_first_sq_aux (x : ℝ) :
    (4 * x ^ 3 * Real.exp (1 - x ^ 2)) ^ 2 ≤ 54 / Real.exp 1 := by
  let y : ℝ := (2 / 3) * x ^ 2
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hA : y * Real.exp (-y) ≤ Real.exp (-1) :=
    Real.mul_exp_neg_le_exp_neg_one y
  have hA0 : 0 ≤ y * Real.exp (-y) := mul_nonneg hy (Real.exp_pos _).le
  have hcube : (y * Real.exp (-y)) ^ 3 ≤ (Real.exp (-1)) ^ 3 :=
    pow_le_pow_left₀ hA0 hA 3
  have hexp : Real.exp (1 - x ^ 2) = Real.exp 1 * Real.exp (-x ^ 2) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have hpow : (Real.exp (-x ^ 2)) ^ 2 = (Real.exp (-y)) ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    dsimp [y]
    ring
  have hident : (4 * x ^ 3 * Real.exp (1 - x ^ 2)) ^ 2 =
      54 * (Real.exp 1) ^ 2 * (y * Real.exp (-y)) ^ 3 := by
    calc
      _ = 16 * x ^ 6 * (Real.exp 1) ^ 2 * (Real.exp (-x ^ 2)) ^ 2 := by
        rw [hexp]
        ring
      _ = 54 * (Real.exp 1) ^ 2 * (y * Real.exp (-y)) ^ 3 := by
        rw [hpow]
        dsimp [y]
        ring
  have hrest : 54 * (Real.exp 1) ^ 2 * (Real.exp (-1)) ^ 3 =
      54 / Real.exp 1 := by
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos 1).ne']
  rw [hident]
  calc
    _ ≤ 54 * (Real.exp 1) ^ 2 * (Real.exp (-1)) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = 54 / Real.exp 1 := hrest

theorem deriv_carmonPsi_le_sqrt_54_div_exp_one (t : ℝ) :
    deriv carmonPsi t ≤ Real.sqrt (54 / Real.exp 1) := by
  by_cases h : 2 * t - 1 ≤ 0
  · rw [deriv_carmonPsi, carmonPsiBaseFirst_zero_of_nonpos h]
    simpa using Real.sqrt_nonneg (54 / Real.exp 1)
  · let x : ℝ := (2 * t - 1)⁻¹
    have hder : deriv carmonPsi t = 4 * x ^ 3 * Real.exp (1 - x ^ 2) := by
      rw [deriv_carmonPsi, carmonPsiBaseFirst_eq_of_pos (lt_of_not_ge h)]
      dsimp [x]
      ring
    rw [hder]
    exact Real.le_sqrt_of_sq_le (carmonPsi_first_sq_aux x)

theorem deriv_carmonPsi_lt_446 (t : ℝ) : deriv carmonPsi t < (223 / 50 : ℝ) :=
  (deriv_carmonPsi_le_sqrt_54_div_exp_one t).trans_lt sqrt_54_div_exp_one_lt_446

end HeavyTailedNoise
