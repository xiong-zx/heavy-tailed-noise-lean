import HeavyTailedNoise.Lower.Fradin.RateParameters

/-! Public arithmetic for the large-chain and small-chain branches. -/

namespace HeavyTailedNoise.Fradin

open HeavyTailedNoise
noncomputable section

theorem chain_floor_argument_eq {L Δ ε θ q : ℝ} (hL : 0 < L)
    (hε : 0 < ε) (hθ : 0 < θ) :
    Δ / (12 * chainScaleAlpha L ε θ q) =
      (L * Δ / ε ^ 2) * θ ^ ((q - 1) / q) / (48 * oracleSmoothnessBudget) := by
  unfold chainScaleAlpha chainScaleBeta oracleSmoothnessBudget
  field_simp [hL.ne', hε.ne', (Real.rpow_pos_of_pos hθ ((q - 1) / q)).ne'] <;> ring

/-- Above the clip threshold, the two powers split exactly. -/
theorem revealRate_chain_power_identity {S r q : ℝ} (hS : 92 < S) (hq : 1 ≤ q) :
    S ^ r * (revealRate 92 S r) ^ ((q - 1) / q) =
      (92 : ℝ) ^ (r * ((q - 1) / q)) * S ^ (r / q) := by
  have hS0 : 0 < S := by linarith
  have hq0 : 0 < q := by linarith
  have hexp : r * ((q - 1) / q) + r / q = r := by
    field_simp [hq0.ne'] <;> ring
  have hθpow : (revealRate 92 S r) ^ ((q - 1) / q) =
      (92 : ℝ) ^ (r * ((q - 1) / q)) / S ^ (r * ((q - 1) / q)) := by
    rw [revealRate, if_neg (not_le.mpr hS),
      ← Real.rpow_mul (div_nonneg (by norm_num) hS0.le),
      Real.div_rpow (by norm_num) hS0.le]
  have hsplit : S ^ r = S ^ (r * ((q - 1) / q)) * S ^ (r / q) := by
    rw [← Real.rpow_add hS0]
    rw [hexp]
  rw [hθpow, hsplit]
  field_simp [(Real.rpow_pos_of_pos hS0 (r * ((q - 1) / q))).ne'] <;> ring

theorem revealRate_chain_factor_bounds {S r q : ℝ}
    (hS : 0 ≤ S) (hr : 0 < r) (hq : 1 ≤ q) :
    1 ≤ (92 : ℝ) ^ r * (revealRate 92 S r) ^ ((q - 1) / q) / revealRate 92 S r ∧
    S ^ (r / q) ≤ (92 : ℝ) ^ r * (revealRate 92 S r) ^ ((q - 1) / q) /
      revealRate 92 S r := by
  have hq0 : 0 < q := by linarith
  have he : 0 ≤ (q - 1) / q := div_nonneg (by linarith) hq0.le
  have hw0 : 0 ≤ S ^ (r / q) := Real.rpow_nonneg hS _
  by_cases hs : S ≤ 92
  · simp only [revealRate, if_pos hs, Real.one_rpow, mul_one, div_one]
    refine ⟨Real.one_le_rpow (by norm_num) hr.le, ?_⟩
    have he0 : 0 ≤ r / q := div_nonneg hr.le hq0.le
    have hele : r / q ≤ r := by
      apply (div_le_iff₀ hq0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hq hr.le]
    exact (Real.rpow_le_rpow hS hs he0).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 92) hele)
  · have hs92 : 92 < S := lt_of_not_ge hs
    have hS0 : 0 < S := by linarith
    have hθ0 : 0 < revealRate 92 S r := revealRate_pos (by norm_num)
    have hθB : revealRate 92 S r * S ^ r = (92 : ℝ) ^ r := by
      rw [revealRate, if_neg hs, Real.div_rpow (by norm_num) hS0.le]
      exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hS0 r).ne'
    have hD : (92 : ℝ) ^ r * (revealRate 92 S r) ^ ((q - 1) / q) /
        revealRate 92 S r = S ^ r * (revealRate 92 S r) ^ ((q - 1) / q) := by
      rw [← hθB]
      field_simp [hθ0.ne'] <;> ring
    simp only [hD, revealRate_chain_power_identity hs92 hq]
    have hc : 1 ≤ (92 : ℝ) ^ (r * ((q - 1) / q)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hr.le he)
    have hw : 1 ≤ S ^ (r / q) :=
      Real.one_le_rpow (by linarith) (div_nonneg hr.le hq0.le)
    have hmul : S ^ (r / q) ≤ (92 : ℝ) ^ (r * ((q - 1) / q)) * S ^ (r / q) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hw0
    exact ⟨hw.trans hmul, hmul⟩

/-- Flooring loses at most a factor two in the large-chain branch. -/
theorem large_chain_rate_bound {A S p q : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hp : 1 < p) (hq : 1 ≤ q)
    (hZ : 2 ≤ A * (revealRate 92 S (tailExponent p)) ^ ((q - 1) / q) /
      (48 * oracleSmoothnessBudget)) :
    0 < ⌊A * (revealRate 92 S (tailExponent p)) ^ ((q - 1) / q) /
      (48 * oracleSmoothnessBudget)⌋₊ ∧
    chainRateCoefficient p * (A + A * S ^ (tailExponent p / q)) ≤
      (⌊A * (revealRate 92 S (tailExponent p)) ^ ((q - 1) / q) /
        (48 * oracleSmoothnessBudget)⌋₊ : ℝ) /
        (4 * revealRate 92 S (tailExponent p)) := by
  let θ := revealRate 92 S (tailExponent p)
  let Z := A * θ ^ ((q - 1) / q) / (48 * oracleSmoothnessBudget)
  let D := (92 : ℝ) ^ tailExponent p * θ ^ ((q - 1) / q) / θ
  have hθ : 0 < θ := revealRate_pos (by norm_num)
  have hpow : 0 < (92 : ℝ) ^ tailExponent p := Real.rpow_pos_of_pos (by norm_num) _
  have hfactor := revealRate_chain_factor_bounds hS (tailExponent_pos hp) hq
  have hsum : A + A * S ^ (tailExponent p / q) ≤ 2 * A * D := by
    have h1 := mul_le_mul_of_nonneg_left hfactor.1 hA
    have h2 := mul_le_mul_of_nonneg_left hfactor.2 hA
    change A * 1 ≤ A * D at h1
    change A * S ^ (tailExponent p / q) ≤ A * D at h2
    nlinarith
  have hfloor : Z / 2 ≤ (⌊Z⌋₊ : ℝ) := natFloor_ge_half_of_ge_two hZ
  have hN : (2 : ℕ) ≤ ⌊Z⌋₊ := Nat.le_floor hZ
  refine ⟨by change 0 < ⌊Z⌋₊; omega, ?_⟩
  change chainRateCoefficient p * (A + A * S ^ (tailExponent p / q)) ≤
    (⌊Z⌋₊ : ℝ) / (4 * θ)
  calc
    _ ≤ chainRateCoefficient p * (2 * A * D) :=
      mul_le_mul_of_nonneg_left hsum (chainRateCoefficient_pos p).le
    _ = (Z / 2) / (4 * θ) := by
      dsimp [D, Z, chainRateCoefficient, oracleSmoothnessBudget]
      field_simp [hθ.ne', hpow.ne'] <;> ring
    _ ≤ (⌊Z⌋₊ : ℝ) / (4 * θ) := div_le_div_of_nonneg_right hfloor (by positivity)

/-- A small chain is covered by the noise work term alone. -/
theorem small_chain_rate_bound {A S p q : ℝ}
    (hA : chainPublicThreshold ≤ A) (hS : 0 ≤ S) (hp : 1 < p) (hq : 1 ≤ q)
    (hZ : A * (revealRate 92 S (tailExponent p)) ^ ((q - 1) / q) /
      (48 * oracleSmoothnessBudget) < 2) :
    A + A * S ^ (tailExponent p / q) ≤ smallChainMultiplier * S ^ tailExponent p := by
  have hC : 0 < oracleSmoothnessBudget := by norm_num [oracleSmoothnessBudget]
  have hA0 : 0 ≤ A := le_trans
    (by norm_num [chainPublicThreshold, oracleSmoothnessBudget]) hA
  have hq0 : 0 < q := by linarith
  have hr := tailExponent_pos hp
  have he : 0 ≤ (q - 1) / q := div_nonneg (by linarith) hq0.le
  by_cases hs : S ≤ 92
  · rw [revealRate, if_pos hs, Real.one_rpow, mul_one] at hZ
    have h := (div_lt_iff₀ (by positivity : 0 < 48 * oracleSmoothnessBudget)).mp hZ
    dsimp [chainPublicThreshold] at hA
    nlinarith
  · have hs92 : 92 < S := lt_of_not_ge hs
    have hS0 : 0 < S := by linarith
    have hw0 : 0 ≤ S ^ (tailExponent p / q) := Real.rpow_nonneg hS _
    have hB0 : 0 ≤ S ^ tailExponent p := Real.rpow_nonneg hS _
    have hprod := revealRate_chain_power_identity (r := tailExponent p) hs92 hq
    have hc : 1 ≤ (92 : ℝ) ^ (tailExponent p * ((q - 1) / q)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hr.le he)
    have hw : 1 ≤ S ^ (tailExponent p / q) :=
      Real.one_le_rpow (by linarith) (div_nonneg hr.le hq0.le)
    have hFW : S ^ (tailExponent p / q) ≤ S ^ tailExponent p *
        (revealRate 92 S (tailExponent p)) ^ ((q - 1) / q) := by
      rw [hprod]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hw0
    have hF1 := hw.trans hFW
    have hAZ : A * (revealRate 92 S (tailExponent p)) ^ ((q - 1) / q) <
        96 * oracleSmoothnessBudget := by
      have h := (div_lt_iff₀ (by positivity : 0 < 48 * oracleSmoothnessBudget)).mp hZ
      nlinarith
    have hmZ := mul_le_mul_of_nonneg_right hAZ.le hB0
    have hm1 := mul_le_mul_of_nonneg_left hF1 hA0
    have hmW := mul_le_mul_of_nonneg_left hFW hA0
    unfold smallChainMultiplier
    nlinarith

end
end HeavyTailedNoise.Fradin
