import HeavyTailedNoise.Analysis.CarmonScalarBounds

/-!
Exact rational/exponential certificates for the manuscript's global
second-derivative bound `|Ψ''| ≤ 32.5`.
-/

namespace HeavyTailedNoise

theorem exp_eight_thirds_gt_23328_div_1625 :
    (23328 / 1625 : ℝ) < Real.exp (8 / 3) := by
  have h := Real.sum_le_exp_of_nonneg
    (x := (8 / 3 : ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem second_deriv_certificate_lt_32_5 :
    (11664 / 25 : ℝ) * Real.exp (-(8 / 3)) < 65 / 2 := by
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos (8 / 3))).2
  nlinarith [exp_eight_thirds_gt_23328_div_1625]

private theorem second_deriv_profile_lt_32_5 (s : ℝ) (hs : 0 ≤ s) :
    |8 * s ^ 2 * (2 * s - 3) * Real.exp (1 - s)| < 65 / 2 := by
  by_cases hsmall : s ≤ 3 / 2
  · have hp : s ^ 2 * (3 - 2 * s) ≤ 1 := by
      nlinarith [mul_nonneg (sq_nonneg (s - 1)) (by linarith : 0 ≤ 2 * s + 1)]
    have hp0 : 0 ≤ s ^ 2 * (3 - 2 * s) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    have he : 0 < Real.exp (1 - s) := Real.exp_pos _
    have hneg : 8 * s ^ 2 * (2 * s - 3) * Real.exp (1 - s) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) he.le
    rw [abs_of_nonpos hneg]
    have hexp : Real.exp (1 - s) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by linarith)
    have hprod : s ^ 2 * (3 - 2 * s) * Real.exp (1 - s) ≤ Real.exp 1 := by
      calc
        _ ≤ 1 * Real.exp (1 - s) :=
          mul_le_mul_of_nonneg_right hp he.le
        _ ≤ Real.exp 1 := by simpa using hexp
    have hmargin : 8 * Real.exp 1 < (65 / 2 : ℝ) := by
      nlinarith [Real.exp_one_lt_three]
    have hrewrite :
        -(8 * s ^ 2 * (2 * s - 3) * Real.exp (1 - s)) =
          8 * (s ^ 2 * (3 - 2 * s) * Real.exp (1 - s)) := by ring
    rw [hrewrite]
    exact (mul_le_mul_of_nonneg_left hprod (by norm_num)).trans_lt hmargin
  · let r : ℝ := s - 3 / 2
    let A : ℝ := (4 / 9) * r * Real.exp (-(4 / 9) * r)
    let C : ℝ := (5 / 18) * s * Real.exp (-(5 / 18) * s)
    have hr : 0 ≤ r := by dsimp [r]; linarith
    have hA0 : 0 ≤ A := by dsimp [A]; positivity
    have hC0 : 0 ≤ C := by dsimp [C]; positivity
    have hA : A ≤ Real.exp (-1) := by
      dsimp [A]
      simpa [neg_mul] using Real.mul_exp_neg_le_exp_neg_one ((4 / 9) * r)
    have hC : C ≤ Real.exp (-1) := by
      dsimp [C]
      simpa [neg_mul] using Real.mul_exp_neg_le_exp_neg_one ((5 / 18) * s)
    have hC2 : C ^ 2 ≤ (Real.exp (-1)) ^ 2 :=
      pow_le_pow_left₀ hC0 hC 2
    have hAC : A * C ^ 2 ≤ (Real.exp (-1)) ^ 3 := by
      calc
        _ ≤ Real.exp (-1) * C ^ 2 :=
          mul_le_mul_of_nonneg_right hA (sq_nonneg C)
        _ ≤ Real.exp (-1) * (Real.exp (-1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hC2 (Real.exp_pos _).le
        _ = (Real.exp (-1)) ^ 3 := by ring
    have he : Real.exp (1 / 3) * Real.exp (-(4 / 9) * r) *
        (Real.exp (-(5 / 18) * s)) ^ 2 = Real.exp (1 - s) := by
      calc
        _ = Real.exp (1 / 3 + (-(4 / 9) * r) + 2 * (-(5 / 18) * s)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
          norm_num
        _ = Real.exp (1 - s) := by
          congr 1
          dsimp [r]
          ring
    have hident : 16 * r * s ^ 2 * Real.exp (1 - s) =
        (11664 / 25) * Real.exp (1 / 3) * A * C ^ 2 := by
      calc
        _ = 16 * r * s ^ 2 *
            (Real.exp (1 / 3) * Real.exp (-(4 / 9) * r) *
              (Real.exp (-(5 / 18) * s)) ^ 2) := by rw [he]
        _ = _ := by dsimp [A, C]; ring
    have hconst : (11664 / 25) * Real.exp (1 / 3) *
        (Real.exp (-1)) ^ 3 =
        (11664 / 25) * Real.exp (-(8 / 3)) := by
      calc
        _ = (11664 / 25) * (Real.exp (1 / 3) * Real.exp (3 * (-1))) := by
          rw [← Real.exp_nat_mul]
          ring
        _ = (11664 / 25) * Real.exp (1 / 3 + 3 * (-1)) := by
          rw [Real.exp_add]
        _ = _ := by congr 1; ring
    have hB0 : 0 ≤ 8 * s ^ 2 * (2 * s - 3) * Real.exp (1 - s) := by
      apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · linarith
      · positivity
    rw [abs_of_nonneg hB0]
    have hrewrite : 8 * s ^ 2 * (2 * s - 3) * Real.exp (1 - s) =
        16 * r * s ^ 2 * Real.exp (1 - s) := by dsimp [r]; ring
    rw [hrewrite, hident]
    calc
      _ ≤ (11664 / 25) * Real.exp (1 / 3) * (Real.exp (-1)) ^ 3 := by
        have hfactor : 0 ≤ (11664 / 25 : ℝ) * Real.exp (1 / 3) := by positivity
        simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hAC hfactor)
      _ = (11664 / 25) * Real.exp (-(8 / 3)) := hconst
      _ < 65 / 2 := second_deriv_certificate_lt_32_5

theorem abs_second_deriv_carmonPsi_lt_32_5 (t : ℝ) :
    |deriv (deriv carmonPsi) t| < (65 / 2 : ℝ) := by
  by_cases h : 2 * t - 1 ≤ 0
  · rw [second_deriv_carmonPsi, carmonPsiBaseSecond_zero_of_nonpos h]
    norm_num
  · let x : ℝ := (2 * t - 1)⁻¹
    let s : ℝ := x ^ 2
    have hs : 0 ≤ s := by dsimp [s]; positivity
    have hform : deriv (deriv carmonPsi) t =
        8 * s ^ 2 * (2 * s - 3) * Real.exp (1 - s) := by
      rw [second_deriv_carmonPsi,
        carmonPsiBaseSecond_eq_of_pos (lt_of_not_ge h)]
      dsimp [s, x]
      ring
    rw [hform]
    exact second_deriv_profile_lt_32_5 s hs

end HeavyTailedNoise
