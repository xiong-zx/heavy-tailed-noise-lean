import HeavyTailedNoise.Upper.K1.BudgetRateConstant

/-!
The published response rate uses a maximum of two powers, rather than a
power of the maximum exponent. For `S ≥ 1` these expressions agree exactly.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem paperS_pow_max_eq_max (σ ε e : ℝ) :
    (paperS σ ε) ^ (max 2 e) =
      max ((paperS σ ε) ^ 2) ((paperS σ ε) ^ e) := by
  have hS : 1 ≤ paperS σ ε := one_le_paperS σ ε
  by_cases h : (2 : ℝ) ≤ e
  · have hpow : (paperS σ ε) ^ 2 ≤ (paperS σ ε) ^ e := by
      calc
        (paperS σ ε) ^ 2 = (paperS σ ε) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ ≤ (paperS σ ε) ^ e := Real.rpow_le_rpow_of_exponent_le hS h
    calc
      (paperS σ ε) ^ (max 2 e) = (paperS σ ε) ^ e := by rw [max_eq_right h]
      _ = max ((paperS σ ε) ^ 2) ((paperS σ ε) ^ e) :=
        (max_eq_right hpow).symm
  · have h' : e ≤ (2 : ℝ) := le_of_not_ge h
    have hpow : (paperS σ ε) ^ e ≤ (paperS σ ε) ^ 2 := by
      calc
        (paperS σ ε) ^ e ≤ (paperS σ ε) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hS h'
        _ = (paperS σ ε) ^ 2 := Real.rpow_natCast _ 2
    calc
      (paperS σ ε) ^ (max 2 e) = (paperS σ ε) ^ (2 : ℝ) := by rw [max_eq_left h']
      _ = (paperS σ ε) ^ 2 := Real.rpow_natCast _ 2
      _ = max ((paperS σ ε) ^ 2) ((paperS σ ε) ^ e) :=
        (max_eq_left hpow).symm

/-- Literal exact fixed response cap with the theorem's `max{S²,S^(r/q)}`
notation. The coefficient still displays the chosen manuscript constants. -/
theorem paperSchedule_responseCount_le_rate_max
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hq : 1 ≤ q)
    (hε : 0 < ε) (hCtail : 12 ≤ Ctail)
    (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI) :
    (responseCount (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI) : ℝ) ≤
      paperRateConstant p q Ctail ch Cb CI *
        ((paperS σ ε) ^ (p / (p - 1)) +
          paperAplus Lbar Δ ε *
            max ((paperS σ ε) ^ 2)
              ((paperS σ ε) ^ ((p / (p - 1)) / q))) := by
  have h := paperSchedule_responseCount_le_rate_constant
    p q Δ σ Lbar ε Ctail ch κ Cb CI
    hp hp2 hq hε hCtail hch hCb hCI
  rwa [paperS_pow_max_eq_max] at h

end

end HeavyTailedNoise.UpperK1
