import HeavyTailedNoise.Upper.K1.StationarityConditionalRisk

/-!
Scalar descent-budget arithmetic for the literal manuscript horizon and
normalized step. This does not address the estimator-error premise or add an
oracle restriction; it discharges only the public physical schedule's numeric
inputs to conditional stationarity.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem paperT_descent_horizon
    {Lbar Δ ε ch : ℝ} (hε : 0 < ε) (hch : 0 < ch) :
    4 * Lbar * Δ ≤
      ch * (paperT Lbar Δ ε ch : ℝ) * ε ^ 2 := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hA : Lbar * Δ / ε ^ 2 ≤ paperAplus Lbar Δ ε :=
    le_max_right 1 _
  have hT : 4 * paperAplus Lbar Δ ε / ch ≤
      (paperT Lbar Δ ε ch : ℝ) := by
    simpa only [paperT] using
      (Nat.le_ceil (4 * paperAplus Lbar Δ ε / ch))
  have hA_mul : Lbar * Δ ≤ paperAplus Lbar Δ ε * ε ^ 2 :=
    (div_le_iff₀ hεsq).mp hA
  have hT_mul : 4 * paperAplus Lbar Δ ε ≤
      ch * (paperT Lbar Δ ε ch : ℝ) := by
    have h := (div_le_iff₀ hch).mp hT
    nlinarith
  have hmult := mul_le_mul_of_nonneg_right hT_mul (sq_nonneg ε)
  calc
    4 * Lbar * Δ ≤ 4 * paperAplus Lbar Δ ε * ε ^ 2 := by
      nlinarith [hA_mul]
    _ ≤ ch * (paperT Lbar Δ ε ch : ℝ) * ε ^ 2 := by
      nlinarith [hmult]

theorem paperStep_descent_budget
    {Lbar Δ ε ch : ℝ} (hL : 0 < Lbar) (hε : 0 < ε)
    (hch : 0 < ch) (hchle : ch ≤ 1 / 4) :
    Δ + (paperT Lbar Δ ε ch : ℝ) * Lbar *
      (paperStep ch ε Lbar) ^ 2 ≤
        paperStep ch ε Lbar *
          ((paperT Lbar Δ ε ch : ℝ) * ε / 2) := by
  let h := paperStep ch ε Lbar
  let T : ℝ := (paperT Lbar Δ ε ch : ℝ)
  have hh : 0 < h := by
    dsimp [h, paperStep]
    exact div_pos (mul_pos hch hε) hL
  have hT : 0 ≤ T := Nat.cast_nonneg _
  have hLh : Lbar * h = ch * ε := by
    dsimp [h, paperStep]
    field_simp [ne_of_gt hL]
  have hhor := paperT_descent_horizon hε hch (Lbar := Lbar) (Δ := Δ)
  have hidentity : ch * T * ε ^ 2 = Lbar * (h * T * ε) := by
    calc
      ch * T * ε ^ 2 = (ch * ε) * T * ε := by ring
      _ = (Lbar * h) * T * ε := by rw [hLh]
      _ = Lbar * (h * T * ε) := by ring
  have hΔ : 4 * Δ ≤ h * T * ε := by
    have hmul : Lbar * (4 * Δ) ≤ Lbar * (h * T * ε) := by
      calc
        _ = 4 * Lbar * Δ := by ring
        _ ≤ ch * T * ε ^ 2 := hhor
        _ = Lbar * (h * T * ε) := hidentity
    exact (mul_le_mul_iff_of_pos_left hL).mp hmul
  have hLhsmall : Lbar * h ≤ ε / 4 := by
    calc
      _ = ch * ε := hLh
      _ ≤ (1 / 4 : ℝ) * ε :=
        mul_le_mul_of_nonneg_right hchle hε.le
      _ = ε / 4 := by ring
  have hquad : T * Lbar * h ^ 2 ≤ h * T * ε / 4 := by
    have h := mul_le_mul_of_nonneg_left hLhsmall
      (mul_nonneg hh.le hT)
    nlinarith [h]
  change Δ + T * Lbar * h ^ 2 ≤ h * (T * ε / 2)
  have hΔquarter : Δ ≤ h * T * ε / 4 := by linarith [hΔ]
  nlinarith [hΔquarter, hquad]

/-- `K = Tε/2` spends half the stationarity budget on deterministic
descent, leaving the other half for the doubled estimator error. -/
theorem stationarity_uniform_ratio_budget
    {T : ℕ} (hT : 0 < T) {ε : ℝ} (hε : 0 ≤ ε) :
    (T : ENNReal)⁻¹ * ENNReal.ofReal ((T : ℝ) * ε / 2) +
      2 * ENNReal.ofReal (ε / 8) ≤ ENNReal.ofReal ε := by
  have hT0 : (T : ENNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hTtop : (T : ENNReal) ≠ ⊤ := by simp
  have hfirst : (T : ENNReal)⁻¹ * ENNReal.ofReal ((T : ℝ) * ε / 2) =
      ENNReal.ofReal (ε / 2) := by
    calc
      _ = (T : ENNReal)⁻¹ *
          ((T : ENNReal) * ENNReal.ofReal (ε / 2)) := by
            congr 1
            rw [show (T : ℝ) * ε / 2 = (T : ℝ) * (ε / 2) by ring,
              ENNReal.ofReal_mul (Nat.cast_nonneg T), ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (ε / 2) :=
        ENNReal.inv_mul_cancel_left hT0 hTtop
  have hsecond : 2 * ENNReal.ofReal (ε / 8) =
      ENNReal.ofReal (ε / 4) := by
    have hreal : (2 : ℝ) * (ε / 8) = ε / 4 := by ring
    rw [← hreal, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hfirst, hsecond]
  calc
    ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) =
        ENNReal.ofReal (ε / 2 + ε / 4) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ε :=
      ENNReal.ofReal_le_ofReal (by linarith)

end

end HeavyTailedNoise.UpperK1
