import HeavyTailedNoise.Lower.Fradin.PublicRegime
import HeavyTailedNoise.Lower.Fradin.RateComparison
import HeavyTailedNoise.Analysis.LowerBoundArithmetic

namespace HeavyTailedNoise.Fradin
noncomputable section
set_option autoImplicit false

/-- A scalar clip gives the reciprocal polynomial work at every noise level. -/
theorem power_ratio_le_inv_revealRate {c S r : ℝ}
    (hc : 0 < c) (hS : 0 ≤ S) (hr : 0 ≤ r) :
    (S/c)^r ≤ 1/revealRate c S r := by
  by_cases hs : S ≤ c
  · rw [revealRate, if_pos hs]
    simp only [div_one]
    exact Real.rpow_le_one (div_nonneg hS hc.le) ((div_le_one hc).2 hs) hr
  · have hSpos : 0 < S := hc.trans (lt_of_not_ge hs)
    have hθ : 0 < (c/S)^r := Real.rpow_pos_of_pos (div_pos hc hSpos) r
    rw [revealRate, if_neg hs]
    apply (le_div_iff₀ hθ).2
    have hprod : (S/c)^r * (c/S)^r = 1 := by
      rw [← Real.mul_rpow (div_nonneg hS hc.le) (div_nonneg hc.le hS)]
      have hbase : (S/c)*(c/S) = 1 := by field_simp [hc.ne', hSpos.ne']
      rw [hbase, Real.one_rpow]
    exact hprod.le

def noiseRateCoefficient (p : ℝ) : ℝ := 1/(4*(8 : ℝ)^tailExponent p)
def chainRateCoefficient (p : ℝ) : ℝ :=
  1/(768*oracleSmoothnessBudget*(92 : ℝ)^tailExponent p)
def smallChainMultiplier : ℝ := 192*oracleSmoothnessBudget

def publicRateCoefficient (p : ℝ) : ℝ :=
  combinedRateConstant (noiseRateCoefficient p) (chainRateCoefficient p) smallChainMultiplier

theorem noiseRateCoefficient_pos (p : ℝ) : 0 < noiseRateCoefficient p := by
  unfold noiseRateCoefficient
  exact div_pos (by norm_num) (mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _))

theorem chainRateCoefficient_pos (p : ℝ) : 0 < chainRateCoefficient p := by
  unfold chainRateCoefficient oracleSmoothnessBudget
  exact div_pos (by norm_num) (mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _))

theorem publicRateCoefficient_pos (p : ℝ) : 0 < publicRateCoefficient p := by
  unfold publicRateCoefficient
  apply combinedRateConstant_pos (noiseRateCoefficient_pos p) (chainRateCoefficient_pos p)
  norm_num [smallChainMultiplier, oracleSmoothnessBudget]

theorem noiseRateCoefficient_work_bound {S p : ℝ} (hS : 0 ≤ S) (hp : 1 < p) :
    noiseRateCoefficient p * S ^ tailExponent p ≤
      1/(4*revealRate 8 S (tailExponent p)) := by
  have h := power_ratio_le_inv_revealRate (by norm_num : (0 : ℝ) < 8)
    hS (tailExponent_pos hp).le
  calc
    _ = (S/8)^tailExponent p / 4 := by
      unfold noiseRateCoefficient
      rw [Real.div_rpow hS (by norm_num : (0 : ℝ) ≤ 8)]
      ring
    _ ≤ (1/revealRate 8 S (tailExponent p))/4 :=
      div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by ring

end
end HeavyTailedNoise.Fradin
