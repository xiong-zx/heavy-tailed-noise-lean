import HeavyTailedNoise.Model.Basic

open MeasureTheory

noncomputable section

namespace HeavyTailedNoise

/-- On a probability space, a finite `q ≥ 1` moment bounds the norm of the Bochner integral. -/
theorem norm_integral_le_of_lintegral_norm_rpow_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → E)
    (hf : Integrable f μ) {q C : ℝ} (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hm : (∫⁻ ξ, ENNReal.ofReal (‖f ξ‖ ^ q) ∂μ) ≤ ENNReal.ofReal (C ^ q)) :
    ‖∫ ξ, f ξ ∂μ‖ ≤ C := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmoment : (∫⁻ ξ, ‖f ξ‖ₑ ^ q ∂μ) ≤ ENNReal.ofReal (C ^ q) := by
    convert hm using 1
    congr 1
    funext ξ
    simpa only [ofReal_norm] using
      (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f ξ)) hqpos.le)
  have hcompare : (∫⁻ ξ, ‖f ξ‖ₑ ∂μ) ≤
      (∫⁻ ξ, ‖f ξ‖ₑ ^ q ∂μ) ^ (1 / q) := by
    have h := eLpNorm'_le_eLpNorm'_of_exponent_le
      (f := f) (p := 1) (q := q) (by norm_num) hq μ hf.aestronglyMeasurable
    simpa [eLpNorm'] using h
  have hroot : (∫⁻ ξ, ‖f ξ‖ₑ ^ q ∂μ) ^ (1 / q) ≤ ENNReal.ofReal C := by
    calc
      _ ≤ (ENNReal.ofReal (C ^ q)) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hmoment (by positivity)
      _ = ENNReal.ofReal C := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hC hqpos.le, ← ENNReal.rpow_mul]
        have hmul : q * (1 / q) = 1 := by field_simp
        rw [hmul, ENNReal.rpow_one]
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  calc
    ENNReal.ofReal ‖∫ ξ, f ξ ∂μ‖ ≤ ∫⁻ ξ, ‖f ξ‖ₑ ∂μ := by
      simpa only [ofReal_norm] using enorm_integral_le_lintegral_enorm f
    _ ≤ (∫⁻ ξ, ‖f ξ‖ₑ ^ q ∂μ) ^ (1 / q) := hcompare
    _ ≤ ENNReal.ofReal C := hroot

/-- Global same-seed q-WAS and unbiasedness give the manuscript's population smoothness. -/
theorem Admissible.grad_lipschitz
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x y : Point d) :
    ‖I.objective.grad x - I.objective.grad y‖ ≤ Lbar * ‖x - y‖ := by
  let : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  have hint : Integrable (fun ξ => I.oracle.response x ξ - I.oracle.response y ξ)
      I.oracle.law := (I.integrable_response x).sub (I.integrable_response y)
  have hbound := norm_integral_le_of_lintegral_norm_rpow_le I.oracle.law
    (fun ξ => I.oracle.response x ξ - I.oracle.response y ξ) hint
    I.q_range (mul_nonneg I.Lbar_pos.le (norm_nonneg _))
    (I.same_seed_increment x y)
  simpa [integral_sub (I.integrable_response x) (I.integrable_response y),
    I.unbiased x, I.unbiased y] using hbound

end HeavyTailedNoise
