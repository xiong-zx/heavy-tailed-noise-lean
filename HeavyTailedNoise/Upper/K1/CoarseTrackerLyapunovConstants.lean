import HeavyTailedNoise.Upper.K1.CoarseTrackerUniformMoment

/-!
Dimension-free scalar constants for the shifted coarse-tracker Lyapunov
argument.  This file only simplifies the actual Hoeffding half-range
coefficient and chooses one positive exponent and one numerical geometric
bound; it imposes no extra stochastic or oracle condition.
-/

namespace HeavyTailedNoise.UpperK1

open scoped NNReal

noncomputable section

theorem tracker_halfRange_sq_eq (C : ℝ) (hC : 0 ≤ C) :
    ((((‖C - -C‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)) = C ^ 2 := by
  have htwice : 0 ≤ C - -C := by linarith
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
    coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg htwice]
  ring

/-- If a bounded increment has drift at least `δ` and cap `C≤9δ`, the
paper choice `lam=δ/C²` contracts the exponential moment by enough for the
uniform numerical Lyapunov bound `K=163`. -/
theorem tracker_scalar_choice (δ C : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hCδ : C ≤ 9 * δ) :
    let lam := δ / C ^ 2
    0 < lam ∧
      Real.exp
        (((((‖C - -C‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * lam ^ 2 / 2) -
          lam * δ) * 163 + 1 ≤ 163 := by
  dsimp only
  have hlam : 0 < δ / C ^ 2 := div_pos hδ (sq_pos_of_pos hC)
  have hcoef := tracker_halfRange_sq_eq C hC.le
  have hexponent :
      C ^ 2 * (δ / C ^ 2) ^ 2 / 2 - (δ / C ^ 2) * δ =
        -(δ ^ 2 / (2 * C ^ 2)) := by
    field_simp [ne_of_gt hC]
    ring
  have hsq : C ^ 2 ≤ (9 * δ) ^ 2 :=
    pow_le_pow_left₀ hC.le hCδ 2
  have hratio : (1 / 162 : ℝ) ≤ δ ^ 2 / (2 * C ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * C ^ 2)).mpr
    nlinarith [hsq]
  have hexpbound : Real.exp (-(δ ^ 2 / (2 * C ^ 2))) ≤
      Real.exp (-(1 / 162 : ℝ)) :=
    Real.exp_le_exp.mpr (neg_le_neg hratio)
  have hone : (163 / 162 : ℝ) ≤ Real.exp (1 / 162 : ℝ) := by
    linarith [Real.add_one_le_exp (1 / 162 : ℝ)]
  have hinv := one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 163 / 162) hone
  have hnumeric : Real.exp (-(1 / 162 : ℝ)) ≤ 162 / 163 := by
    rw [Real.exp_neg]
    have hfrac : (1 : ℝ) / (163 / 162) = 162 / 163 := by norm_num
    rw [hfrac] at hinv
    simpa only [one_div] using hinv
  constructor
  · exact hlam
  · rw [hcoef, hexponent]
    have hr := hexpbound.trans hnumeric
    nlinarith

theorem tracker_scalar_lambda_inv_le (δ C : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hCδ : C ≤ 9 * δ) :
    (δ / C ^ 2)⁻¹ ≤ 81 * δ := by
  have hsq : C ^ 2 ≤ (9 * δ) ^ 2 :=
    pow_le_pow_left₀ hC.le hCδ 2
  have heq : (δ / C ^ 2)⁻¹ = C ^ 2 / δ := by
    field_simp [ne_of_gt hδ, ne_of_gt hC]
  rw [heq]
  apply (div_le_iff₀ hδ).mpr
  nlinarith [hsq]

variable {q : ℝ} (P : Schedule q)

/-- Instantiate the scalar choice using the exact drift and increment cap
proved for the shared-batch tracker.  The physical schedule supplies
`β>0` and the step-size inequality; no condition on `σ` is used here. -/
theorem tracker_schedule_scalar_choice
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hbeta : 0 < P.beta) (hh : 0 ≤ P.h)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8) :
    let δ := (1 / 8 : ℝ) *
      (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
    let lam := δ / C ^ 2
    0 < lam ∧
      trackerMGFContraction P Lbar lam * 163 + 1 ≤ 163 := by
  dsimp only
  let a := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  have ha : 0 < a := mul_pos hbeta
    (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩)
  have hδ : 0 < (1 / 8 : ℝ) * a := by positivity
  have hC : 0 < a + Lbar * P.h :=
    lt_of_lt_of_le ha (le_add_of_nonneg_right
      (mul_nonneg I.Lbar_pos.le hh))
  have hCδ : a + Lbar * P.h ≤
      9 * ((1 / 8 : ℝ) * a) := by
    dsimp [a] at hmove ⊢
    linarith
  simpa only [trackerMGFContraction, a] using
    (tracker_scalar_choice ((1 / 8 : ℝ) * a)
      (a + Lbar * P.h) hδ hC hCδ)

/-- The scalar exponent's inverse and the below-threshold overshoot both
scale with the physical low clipping threshold. -/
theorem tracker_schedule_exponent_overshoot_scale
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hbeta : 0 < P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8) :
    let τ := P.tau ⟨0, Nat.zero_lt_succ P.J⟩
    let δ := (1 / 8 : ℝ) * (P.beta * τ)
    let C := P.beta * τ + Lbar * P.h
    (δ / C ^ 2)⁻¹ ≤ (81 / 32 : ℝ) * τ ∧
      2 * τ + C ≤ 3 * τ := by
  dsimp only
  let τ := P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  let a := P.beta * τ
  let δ := (1 / 8 : ℝ) * a
  let C := a + Lbar * P.h
  have hτ : 0 < τ := P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩
  have ha : 0 < a := mul_pos hbeta hτ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hC : 0 < C := by
    dsimp [C]
    have hnonneg := mul_nonneg I.Lbar_pos.le hh
    linarith
  have hCδ : C ≤ 9 * δ := by
    have hmove' : Lbar * P.h ≤ a / 8 := hmove
    dsimp [C, δ]
    nlinarith [hmove']
  have hδτ : δ ≤ τ / 32 := by
    dsimp [δ, a]
    have hmul := mul_le_mul_of_nonneg_right hbeta_le hτ.le
    nlinarith
  have hCτ : C ≤ τ := by
    have h := hCδ
    linarith [hδτ]
  constructor
  · calc
      (δ / C ^ 2)⁻¹ ≤ 81 * δ :=
        tracker_scalar_lambda_inv_le δ C hδ hC hCδ
      _ ≤ (81 / 32 : ℝ) * τ := by linarith [hδτ]
  · linarith [hCτ]

end

end HeavyTailedNoise.UpperK1
