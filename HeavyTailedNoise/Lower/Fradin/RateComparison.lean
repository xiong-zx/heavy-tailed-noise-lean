import HeavyTailedNoise.Model.Basic

/-! Elementary combination of a chain lower bound and a small-chain noise
lower bound. All inputs here are numerical inequalities, not oracle axioms. -/

namespace HeavyTailedNoise.Fradin
noncomputable section
set_option autoImplicit false

def combinedRateConstant (cN cC C : ℝ) : ℝ :=
  min (cN/(1+C)) (min cN cC / 2)

theorem combinedRateConstant_pos {cN cC C : ℝ}
    (hcN : 0 < cN) (hcC : 0 < cC) (hC : 0 ≤ C) :
    0 < combinedRateConstant cN cC C := by
  unfold combinedRateConstant
  exact lt_min (div_pos hcN (by linarith)) (div_pos (lt_min hcN hcC) (by norm_num))

theorem combined_rate_of_chain_or_noise
    {A B W Z R cN cC C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 0 ≤ W)
    (hcN : 0 < cN) (hcC : 0 < cC) (hC : 0 ≤ C)
    (hnoise : cN*B ≤ R)
    (hlarge : 2 ≤ Z → cC*(A+A*W) ≤ R)
    (hsmall : Z < 2 → A+A*W ≤ C*B) :
    combinedRateConstant cN cC C * (B+A+A*W) ≤ R := by
  let c := combinedRateConstant cN cC C
  have hc : 0 ≤ c := (combinedRateConstant_pos hcN hcC hC).le
  have hsum : 0 ≤ A+A*W := by positivity
  by_cases hz : 2 ≤ Z
  · have hm0 : 0 ≤ min cN cC := le_min hcN.le hcC.le
    have hmN := mul_le_mul_of_nonneg_right (min_le_left cN cC) hB
    have hmC := mul_le_mul_of_nonneg_right (min_le_right cN cC) hsum
    have hb : min cN cC * (B+A+A*W) ≤ 2*R := by
      nlinarith [hlarge hz]
    have hcle : 2*c ≤ min cN cC := by
      have h := min_le_right (cN/(1+C)) (min cN cC/2)
      change c ≤ min cN cC/2 at h
      linarith
    have hmult := mul_le_mul_of_nonneg_right hcle (by positivity : 0 ≤ B+A+A*W)
    nlinarith
  · have htarget := hsmall (lt_of_not_ge hz)
    have hcle : c*(1+C) ≤ cN := by
      have h := min_le_left (cN/(1+C)) (min cN cC/2)
      change c ≤ cN/(1+C) at h
      exact (le_div_iff₀ (by linarith : (0 : ℝ) < 1+C)).1 h
    have hmult := mul_le_mul_of_nonneg_left (show B+A+A*W ≤ (1+C)*B by nlinarith) hc
    have hcoef := mul_le_mul_of_nonneg_right hcle hB
    nlinarith

end
end HeavyTailedNoise.Fradin
