import HeavyTailedNoise.Upper.Foundations.CoarseTrackerNegativeDrift

/-!
The coarse tracker's bad-event probability follows from the original centered
`p`-moment at each fixed pre-batch decision. The event concerns the first new
oracle response, without a moment assumption at a random clipping center.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

private theorem six_sigma_rpow_le_half_threshold_rpow
    {p σ τ : ℝ} (hp : 1 ≤ p) (hσ : 0 ≤ σ) (hτ : 0 < τ)
    (hscale : 12 * σ ≤ τ) :
    6 * σ ^ p ≤ (τ / 2) ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have h6pow : (6 : ℝ) ≤ (6 : ℝ) ^ p :=
    Real.self_le_rpow_of_one_le (by norm_num) hp
  have hσpow : 0 ≤ σ ^ p := Real.rpow_nonneg hσ _
  have h6σ : 6 * σ ≤ τ / 2 := by linarith
  calc
    6 * σ ^ p ≤ (6 : ℝ) ^ p * σ ^ p :=
      mul_le_mul_of_nonneg_right h6pow hσpow
    _ = (6 * σ) ^ p := (Real.mul_rpow (by norm_num) hσ).symm
    _ ≤ (τ / 2) ^ p :=
      Real.rpow_le_rpow (mul_nonneg (by norm_num) hσ) h6σ hp0

/-- The fresh first response misses the tracker's good event with probability
at most `1/6`, uniformly in the fixed pre-batch point. -/
theorem Admissible.firstResponse_badEvent_measure_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar τ : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hτ : 0 < τ) (hscale : 12 * σ ≤ τ) (x : Point d) :
    I.oracle.law {ξ | τ / 2 < ‖I.oracle.response x ξ - I.objective.grad x‖} ≤
      (1 / 6 : ENNReal) := by
  let f : Seed → ENNReal := fun ξ =>
    ENNReal.ofReal (‖I.oracle.response x ξ - I.objective.grad x‖ ^ p)
  let a : ENNReal := ENNReal.ofReal ((τ / 2) ^ p)
  have hp0 : 0 ≤ p := le_trans (by norm_num : (0 : ℝ) ≤ 1) I.p_range.1.le
  have hhalf : 0 < τ / 2 := by positivity
  have hapow : 0 ≤ (τ / 2) ^ p := Real.rpow_nonneg hhalf.le _
  have ha0 : a ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hhalf _)
  have hatop : a ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have hresponse : Measurable (I.oracle.response x) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hf : Measurable f := by
    unfold f
    fun_prop
  have hsubset :
      {ξ | τ / 2 < ‖I.oracle.response x ξ - I.objective.grad x‖} ⊆
        {ξ | a ≤ f ξ} := by
    intro ξ hξ
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hhalf.le hξ.le hp0)
  have hmarkov : a * I.oracle.law {ξ | a ≤ f ξ} ≤
      ∫⁻ ξ, f ξ ∂I.oracle.law :=
    mul_meas_ge_le_lintegral hf a
  have hmoment : (∫⁻ ξ, f ξ ∂I.oracle.law) ≤ ENNReal.ofReal (σ ^ p) :=
    I.centered_moment x
  have hbad : a * I.oracle.law
      {ξ | τ / 2 < ‖I.oracle.response x ξ - I.objective.grad x‖} ≤
        ENNReal.ofReal (σ ^ p) := by
    calc
      _ ≤ a * I.oracle.law {ξ | a ≤ f ξ} :=
        mul_le_mul' le_rfl (measure_mono hsubset)
      _ ≤ ∫⁻ ξ, f ξ ∂I.oracle.law := hmarkov
      _ ≤ ENNReal.ofReal (σ ^ p) := hmoment
  have hreal : σ ^ p ≤ (τ / 2) ^ p * (1 / 6 : ℝ) := by
    have hpow := six_sigma_rpow_le_half_threshold_rpow
      I.p_range.1.le I.sigma_nonneg hτ hscale
    nlinarith
  have hscaled : ENNReal.ofReal (σ ^ p) ≤ a * (1 / 6 : ENNReal) := by
    calc
      _ ≤ ENNReal.ofReal ((τ / 2) ^ p * (1 / 6 : ℝ)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = a * (1 / 6 : ENNReal) := by
        have hfrac : ENNReal.ofReal (1 / 6 : ℝ) = (1 / 6 : ENNReal) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 6)]
          norm_num
        rw [ENNReal.ofReal_mul hapow, hfrac]
  have hmul :
      I.oracle.law
        {ξ | τ / 2 < ‖I.oracle.response x ξ - I.objective.grad x‖} * a ≤
        (1 / 6 : ENNReal) * a := by
    calc
      _ = a * I.oracle.law
          {ξ | τ / 2 < ‖I.oracle.response x ξ - I.objective.grad x‖} :=
            mul_comm _ _
      _ ≤ ENNReal.ofReal (σ ^ p) := hbad
      _ ≤ a * (1 / 6 : ENNReal) := hscaled
      _ = (1 / 6 : ENNReal) * a := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_left ha0 hatop).mp hmul

end

end HeavyTailedNoise.UpperK1
