import HeavyTailedNoise.Upper.K1.BudgetRateEnvelope

/-!
One explicit dimension-independent response-count coefficient. It depends on
the manuscript's chosen numerical constants and exponents, not on the
dimension, objective, noise magnitude, smoothness, gap, or accuracy.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

def paperRateConstant (p q Ctail ch Cb CI : ℝ) : ℝ :=
  max (2 + CI * (2 * Ctail) ^ paperA p)
    ((4 / ch + 1) * (Cb * (2 * Ctail) ^ paperEplus p q + 1))

theorem paperSchedule_responseCount_le_rate_constant
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hq : 1 ≤ q)
    (hε : 0 < ε) (hCtail : 12 ≤ Ctail)
    (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI) :
    (responseCount (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI) : ℝ) ≤
      paperRateConstant p q Ctail ch Cb CI *
        ((paperS σ ε) ^ (p / (p - 1)) +
          paperAplus Lbar Δ ε *
            (paperS σ ε) ^ (max 2 ((p / (p - 1)) / q))) := by
  let A := paperAplus Lbar Δ ε
  let B := (paperS σ ε) ^ (p / (p - 1))
  let R := (paperS σ ε) ^ (max 2 ((p / (p - 1)) / q))
  let cI := CI * (2 * Ctail) ^ paperA p
  let cB := Cb * (2 * Ctail) ^ paperEplus p q
  let d := (4 / ch + 1) * (cB + 1)
  let C := paperRateConstant p q Ctail ch Cb CI
  have hS : 1 ≤ paperS σ ε := one_le_paperS σ ε
  have hA : 1 ≤ A := le_max_left 1 _
  have hB : 1 ≤ B := by
    dsimp [B]
    apply Real.one_le_rpow hS
    have hp0 : 0 ≤ p := by linarith
    exact div_nonneg hp0 (sub_nonneg.mpr hp.le)
  have hR : 1 ≤ R := by
    dsimp [R]
    apply Real.one_le_rpow hS
    exact le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left 2 _)
  have hcB : 0 ≤ cB := by
    dsimp [cB]
    have hC : 0 ≤ 2 * Ctail := by linarith
    positivity
  have h4 : 0 ≤ 4 / ch := div_nonneg (by norm_num) hch.le
  have hIter : 4 * A / ch + 1 ≤ (4 / ch + 1) * A := by
    have he : 4 * A / ch = (4 / ch) * A := by ring
    rw [he]
    nlinarith [hA]
  have hBatch : cB * R + 1 ≤ (cB + 1) * R := by
    nlinarith [hR]
  have hProd : (4 * A / ch + 1) * (cB * R + 1) ≤
      d * A * R := by
    have hm := mul_le_mul hIter hBatch
      (by nlinarith [mul_nonneg hcB (by linarith : 0 ≤ R)])
      (by nlinarith [h4, hA])
    dsimp [d]
    nlinarith
  have hFirst : 2 + cI * B ≤ (2 + cI) * B := by
    nlinarith [hB]
  have hEnv := paperSchedule_responseCount_le_rate_envelope
    p q Δ σ Lbar ε Ctail ch κ Cb CI hp hp2 hq hε hCtail hch hCb hCI
  have hN : (responseCount (paperSchedule p q Δ σ Lbar ε Ctail
      ch κ Cb CI hε hch hCb hCI) : ℝ) ≤
      (2 + cI) * B + d * A * R := by
    dsimp [A, B, R, cI, cB] at hProd hFirst ⊢
    nlinarith [hEnv]
  have hC1 : 2 + cI ≤ C := by
    dsimp [C, paperRateConstant, cI]
    exact le_max_left _ _
  have hC2 : d ≤ C := by
    dsimp [C, paperRateConstant, d, cB]
    exact le_max_right _ _
  have hCB := mul_le_mul_of_nonneg_right hC1 (by linarith : 0 ≤ B)
  have hCR := mul_le_mul_of_nonneg_right hC2
    (mul_nonneg (by linarith : 0 ≤ A) (by linarith : 0 ≤ R))
  change (responseCount (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI) : ℝ) ≤ C * (B + A * R)
  nlinarith

end

end HeavyTailedNoise.UpperK1
