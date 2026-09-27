import HeavyTailedNoise.Lower.Gated.HardObjective

/-!
First quantitative fact about the manuscript's radial soft projection. Its
first- and second-derivative operator bounds remain separate obligations.
-/

namespace HeavyTailedNoise

noncomputable section

theorem norm_softProjection_lt_radius {d : ℕ} {R : ℝ} (hR : 0 < R)
    (x : Point d) : ‖softProjection R x‖ < R := by
  let b : ℝ := 1 + ‖x‖ ^ 2 / R ^ 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsqrt' : 0 < Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2) := by
    simpa [b] using hsqrt
  have hnorm : ‖softProjection R x‖ = ‖x‖ / Real.sqrt b := by
    simp [softProjection, b, norm_smul, Real.norm_eq_abs,
      abs_of_pos hsqrt', div_eq_mul_inv, mul_comm]
  have hRne : R ≠ 0 := ne_of_gt hR
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hmul : R ^ 2 * (‖x‖ ^ 2 / R ^ 2) = ‖x‖ ^ 2 := by
    field_simp [hRne]
  have hsq : (‖x‖ / Real.sqrt b) ^ 2 < R ^ 2 := by
    rw [div_pow, Real.sq_sqrt hb.le]
    apply (div_lt_iff₀ hb).2
    calc
      ‖x‖ ^ 2 < ‖x‖ ^ 2 + R ^ 2 := lt_add_of_pos_right _ hR2
      _ = R ^ 2 * b := by dsimp [b]; rw [mul_add, hmul]; ring
  rw [hnorm]
  have hnonneg : 0 ≤ ‖x‖ / Real.sqrt b :=
    div_nonneg (norm_nonneg _) hsqrt.le
  nlinarith

/-- The radial scale lies in `(0,1]` at every ambient point. -/
theorem softProjection_scale_pos_le_one {d : ℕ} {R : ℝ} (hR : 0 < R)
    (x : Point d) :
    0 < (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹ ∧
      (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹ ≤ 1 := by
  let b : ℝ := 1 + ‖x‖ ^ 2 / R ^ 2
  have hb : 1 ≤ b := by
    have hnonneg : 0 ≤ ‖x‖ ^ 2 / R ^ 2 := by positivity
    dsimp [b]
    linarith
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by linarith)
  have hroot : 1 ≤ Real.sqrt b := by
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ b)
    nlinarith [Real.sqrt_nonneg b]
  have hinv : 0 < (Real.sqrt b)⁻¹ := inv_pos.mpr hs
  have hmul : Real.sqrt b * (Real.sqrt b)⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have hprod : 0 ≤ (Real.sqrt b - 1) * (Real.sqrt b)⁻¹ :=
    mul_nonneg (sub_nonneg.mpr hroot) hinv.le
  constructor
  · simpa [b] using hinv
  · have hle : (Real.sqrt b)⁻¹ ≤ 1 := by nlinarith [hprod]
    simpa [b] using hle

/-- The numerical radial scale used in the near-origin stationarity case. -/
theorem softProjection_scale_gt_97_of_scaled_norm_sq_le
    {d : ℕ} {R : ℝ} (hR : 0 < R) (x : Point d)
    (hx : ‖x‖ ^ 2 / R ^ 2 ≤ (1 / 16 : ℝ)) :
    (97 / 100 : ℝ) < (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹ := by
  let b : ℝ := 1 + ‖x‖ ^ 2 / R ^ 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbupper : b ≤ (17 / 16 : ℝ) := by dsimp [b]; linarith
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have hrootlt : Real.sqrt b < (100 / 97 : ℝ) := by
    nlinarith [Real.sqrt_nonneg b]
  have hsmall : (97 / 100 : ℝ) * Real.sqrt b < 1 := by nlinarith
  have hmul : Real.sqrt b * (Real.sqrt b)⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have htarget : (97 / 100 : ℝ) < (Real.sqrt b)⁻¹ := by
    by_contra h
    have hle : (Real.sqrt b)⁻¹ ≤ (97 / 100 : ℝ) := le_of_not_gt h
    have hmul_le := mul_le_mul_of_nonneg_left hle hs.le
    nlinarith [hmul_le]
  simpa [b] using htarget

end

end HeavyTailedNoise
