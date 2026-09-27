import HeavyTailedNoise.Lower.Gated.HardGaussianFailureProbability

/-! Exact probability slack converting the T≥64 completion tail and 1/10
accident allowance into a strict less-than-half failure probability. -/

namespace HeavyTailedNoise

noncomputable section

theorem gated_completion_exp_le_quarter {T : ℕ} (hT : 64 ≤ T) :
    Real.exp (-(T : ℝ) / 32) ≤ (1 / 4 : ℝ) := by
  have hTR : (64 : ℝ) ≤ T := by exact_mod_cast hT
  have hmono : Real.exp (-(T : ℝ) / 32) ≤ Real.exp (-2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 : (2 : ℝ) < Real.exp 1 := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
      (Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0))
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hinv : Real.exp (-2) ≤ (1 / 4 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_le_inv₀ (Real.exp_pos (2 : ℝ)) (by norm_num : (0 : ℝ) < 4)).mpr h2
  exact hmono.trans hinv

theorem gated_failure_budget_lt_half {T : ℕ} (hT : 64 ≤ T) :
    Real.exp (-(T : ℝ) / 32) + (1 / 10 : ℝ) ≤ 7 / 20 ∧
      (7 / 20 : ℝ) < 1 / 2 := by
  constructor
  · linarith [gated_completion_exp_le_quarter hT]
  · norm_num

end

end HeavyTailedNoise
