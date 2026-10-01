import HeavyTailedNoise.Upper.K1.NoiseScale

/-!
The exact paper schedule with the legal fixed choice `c_h = 1/8` satisfies
every coefficient gate used by the coarse tracker, including at `σ = 0` and
when the normalized noise scale lies just above a ceiling boundary.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem paperBeta_pos (σ ε : ℝ) : 0 < paperBeta σ ε := by
  have hk : (1 : ℝ) ≤ (Nat.ceil (paperS σ ε) : ℝ) :=
    (one_le_paperS σ ε).trans (paperS_le_ceil σ ε)
  unfold paperBeta
  have hden : 0 < 4 * (Nat.ceil (paperS σ ε) : ℝ) := by nlinarith
  exact inv_pos.mpr hden

theorem paperBeta_le_quarter (σ ε : ℝ) : paperBeta σ ε ≤ 1 / 4 := by
  have hk : (1 : ℝ) ≤ (Nat.ceil (paperS σ ε) : ℝ) :=
    (one_le_paperS σ ε).trans (paperS_le_ceil σ ε)
  have hden : (4 : ℝ) ≤ 4 * (Nat.ceil (paperS σ ε) : ℝ) := by nlinarith
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hden
  simpa only [paperBeta, one_div] using h

theorem paperTau_zero_ge_twelve_sigma (σ ε : ℝ) :
    12 * σ ≤ paperTau σ ε 0 := by
  have hν : σ ≤ paperNu σ ε := le_max_left σ ε
  simp only [paperTau, pow_zero, mul_one]
  nlinarith

theorem paperStep_eighth_nonneg {ε Lbar : ℝ}
    (hε : 0 < ε) (hLbar : 0 < Lbar) :
    0 ≤ paperStep (1 / 8) ε Lbar := by
  unfold paperStep
  positivity

theorem Lbar_mul_paperStep_eighth {ε Lbar : ℝ}
    (hLbar : 0 < Lbar) :
    Lbar * paperStep (1 / 8) ε Lbar = ε / 8 := by
  unfold paperStep
  field_simp [ne_of_gt hLbar]

/-- The weak step gate uses `ceil S ≤ 2S`, so it holds uniformly across
integer ceilings without requiring a smaller noise regime. -/
theorem paperStep_eighth_tracker_move
    {σ ε Lbar : ℝ} (hε : 0 < ε) (hLbar : 0 < Lbar) :
    Lbar * paperStep (1 / 8) ε Lbar ≤
      paperBeta σ ε * paperTau σ ε 0 / 8 := by
  let S := paperS σ ε
  let k : ℝ := Nat.ceil S
  let ν := paperNu σ ε
  have hS : 0 < S := paperS_pos σ ε
  have hk : 0 < k := by
    have h := (one_le_paperS σ ε).trans (paperS_le_ceil σ ε)
    dsimp [k, S]
    linarith
  have hkUpper : k ≤ 2 * S := paperS_ceil_le_two_mul σ ε
  have hν : ν = ε * S := paperNu_eq_eps_mul_paperS hε
  have hRatio : ε / 8 ≤ 3 * ε * S / (8 * k) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * k)).mpr
    have hprod : ε * k ≤ ε * (2 * S) :=
      mul_le_mul_of_nonneg_left hkUpper hε.le
    nlinarith [hprod, mul_nonneg hε.le hS.le]
  have hFormula : paperBeta σ ε * paperTau σ ε 0 / 8 =
      3 * ε * S / (8 * k) := by
    simp only [paperBeta, paperTau, pow_zero, mul_one]
    change (4 * k)⁻¹ * (12 * ν) / 8 = _
    rw [hν]
    field_simp [ne_of_gt hk]
    ring
  rw [Lbar_mul_paperStep_eighth hLbar, hFormula]
  exact hRatio

end

end HeavyTailedNoise.UpperK1
