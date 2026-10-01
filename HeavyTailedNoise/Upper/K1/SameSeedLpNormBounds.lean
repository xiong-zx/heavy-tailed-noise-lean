import HeavyTailedNoise.Upper.K1.SameSeedMomentLp

/-!
The oracle records its `p` and same-seed `q` assumptions as ENNReal raw
moments.  This module takes their positive roots to obtain real `lpNorm`
bounds, without adding a moment assumption on an absolute residual.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

private theorem lpNorm_le_of_lintegral_norm_rpow_le
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) (f : α → E) {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (hf : MemLp f (ENNReal.ofReal r) μ)
    (hm : (∫⁻ a, ENNReal.ofReal (‖f a‖ ^ r) ∂μ) ≤
      ENNReal.ofReal (C ^ r)) :
    lpNorm f (ENNReal.ofReal r) μ ≤ C := by
  have hint : Integrable (fun a => ‖f a‖ ^ r) μ := by
    simpa only [ENNReal.toReal_ofReal hr.le] using
      (hf.integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top)
  have hnonneg : 0 ≤ᵐ[μ] (fun a => ‖f a‖ ^ r) :=
    Filter.Eventually.of_forall (fun a => Real.rpow_nonneg (norm_nonneg _) _)
  have hreal : (∫ a, ‖f a‖ ^ r ∂μ) ≤ C ^ r := by
    apply (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hC _)).mp
    calc
      ENNReal.ofReal (∫ a, ‖f a‖ ^ r ∂μ) =
          ∫⁻ a, ENNReal.ofReal (‖f a‖ ^ r) ∂μ :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg
      _ ≤ ENNReal.ofReal (C ^ r) := hm
  have hint0 : 0 ≤ ∫ a, ‖f a‖ ^ r ∂μ :=
    integral_nonneg (fun a => Real.rpow_nonneg (norm_nonneg _) _)
  calc
    lpNorm f (ENNReal.ofReal r) μ =
        (∫ a, ‖f a‖ ^ r ∂μ) ^ r⁻¹ := by
      rw [lpNorm_eq_integral_norm_rpow_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hr)
        ENNReal.ofReal_ne_top hf.aestronglyMeasurable]
      simp only [ENNReal.toReal_ofReal hr.le]
    _ ≤ (C ^ r) ^ r⁻¹ :=
      Real.rpow_le_rpow hint0 hreal (inv_nonneg.mpr hr.le)
    _ = C := by
      rw [← Real.rpow_mul hC, mul_inv_cancel₀ hr.ne', Real.rpow_one]

theorem Admissible.centered_response_lpNorm_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x : Point d) :
    lpNorm (fun ξ => I.oracle.response x ξ - I.objective.grad x)
      (ENNReal.ofReal p) I.oracle.law ≤ σ :=
  lpNorm_le_of_lintegral_norm_rpow_le I.oracle.law
    (fun ξ => I.oracle.response x ξ - I.objective.grad x)
    (lt_trans zero_lt_one I.p_range.1) I.sigma_nonneg
    (Admissible.centered_response_memLp I x) (I.centered_moment x)

theorem Admissible.same_seed_increment_lpNorm_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x y : Point d) :
    lpNorm (fun ξ => I.oracle.response x ξ - I.oracle.response y ξ)
      (ENNReal.ofReal q) I.oracle.law ≤ Lbar * ‖x - y‖ :=
  lpNorm_le_of_lintegral_norm_rpow_le I.oracle.law
    (fun ξ => I.oracle.response x ξ - I.oracle.response y ξ)
    (lt_of_lt_of_le zero_lt_one I.q_range)
    (mul_nonneg I.Lbar_pos.le (norm_nonneg _))
    (Admissible.same_seed_increment_memLp I x y)
    (I.same_seed_increment x y)

end

end HeavyTailedNoise.UpperK1
