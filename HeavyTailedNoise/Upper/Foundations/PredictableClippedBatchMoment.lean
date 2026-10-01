import HeavyTailedNoise.Upper.Foundations.ClippedBatchMoment

/-!
The fixed-history clipped-batch variance bound averaged over an arbitrary
probability law of the whole pre-batch history. Fresh seeds have the product
law and are conditioned on only after the complete history is fixed.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace HeavyTailedNoise

theorem upperClippedBatchMean_norm_le
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) {τ : ℝ} (hτ : 0 < τ)
    (x w : Point d) (hb : 0 < b) (seeds : Fin b → Seed) :
    ‖upperResidualBatchMean O (upperClip τ) x w seeds‖ ≤ τ := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hbReal : (b : ℝ) ≠ 0 := ne_of_gt hbpos
  have hinv : 0 ≤ (b : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hbpos)
  unfold upperResidualBatchMean
  calc
    ‖(b : ℝ)⁻¹ • ∑ i : Fin b, upperClip τ (O.response x (seeds i) - w)‖ =
        (b : ℝ)⁻¹ * ‖∑ i : Fin b, upperClip τ (O.response x (seeds i) - w)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbpos)]
    _ ≤ (b : ℝ)⁻¹ * ∑ i : Fin b,
        ‖upperClip τ (O.response x (seeds i) - w)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hinv
    _ ≤ (b : ℝ)⁻¹ * ∑ _i : Fin b, τ := by
          apply mul_le_mul_of_nonneg_left _ hinv
          apply Finset.sum_le_sum
          intro i hi
          exact upperClip_norm_le hτ _
    _ = τ := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      field_simp [hbReal]

theorem upperClippedSourceMean_norm_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) {τ : ℝ} (hτ : 0 < τ)
    (x w : Point d) :
    ‖upperResidualSourceMean O (upperClip τ) x w‖ ≤ τ := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  unfold upperResidualSourceMean
  simpa using (norm_integral_le_of_norm_le_const (μ := O.law)
    (Filter.Eventually.of_forall (fun ξ =>
      upperClip_norm_le hτ (O.response x ξ - w))))

/-- The centered clipped-batch error has an ordinary, integrable squared norm
on the full product space. This uses bounded clipping, not an assumption on
the history-dependent residual. -/
theorem Admissible.predictable_upperClippedBatchError_sq_integrable
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar τ : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hτ : 0 < τ) (historyLaw : Measure History)
    [IsProbabilityMeasure historyLaw]
    (x w : History → Point d) (hx : Measurable x) (hw : Measurable w)
    (hb : 0 < b) :
    Integrable (fun z : History × (Fin b → Seed) =>
      ‖upperResidualBatchMean I.oracle (upperClip τ) (x z.1) (w z.1) z.2 -
        upperResidualSourceMean I.oracle (upperClip τ) (x z.1) (w z.1)‖ ^ 2)
      (historyLaw.prod (freshSeedLaw I.oracle b)) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle b) := by
    unfold freshSeedLaw
    infer_instance
  have hbatch : Measurable (fun z : History × (Fin b → Seed) =>
      upperResidualBatchMean I.oracle (upperClip τ) (x z.1) (w z.1) z.2) :=
    measurable_upperClippedBatchMean (b := b) I.oracle hτ x w hx hw
  have hsource := measurable_upperResidualSourceMean I.oracle (upperClip τ)
    (measurable_upperClip hτ) x w hx hw
  have herr : Measurable (fun z : History × (Fin b → Seed) =>
      upperResidualBatchMean I.oracle (upperClip τ) (x z.1) (w z.1) z.2 -
        upperResidualSourceMean I.oracle (upperClip τ) (x z.1) (w z.1)) :=
    hbatch.sub (hsource.comp measurable_fst)
  have hsq : Measurable (fun z : History × (Fin b → Seed) =>
      ‖upperResidualBatchMean I.oracle (upperClip τ) (x z.1) (w z.1) z.2 -
        upperResidualSourceMean I.oracle (upperClip τ) (x z.1) (w z.1)‖ ^ 2) :=
    herr.norm.pow_const 2
  have hbound (z : History × (Fin b → Seed)) :
      ‖upperResidualBatchMean I.oracle (upperClip τ) (x z.1) (w z.1) z.2 -
        upperResidualSourceMean I.oracle (upperClip τ) (x z.1) (w z.1)‖ ≤
          2 * τ := by
    calc
      _ ≤ ‖upperResidualBatchMean I.oracle (upperClip τ) (x z.1) (w z.1) z.2‖ +
          ‖upperResidualSourceMean I.oracle (upperClip τ) (x z.1) (w z.1)‖ :=
            norm_sub_le _ _
      _ ≤ τ + τ := add_le_add
        (upperClippedBatchMean_norm_le I.oracle hτ (x z.1) (w z.1) hb z.2)
        (upperClippedSourceMean_norm_le I.oracle hτ (x z.1) (w z.1))
      _ = 2 * τ := by ring
  refine Integrable.of_bound hsq.aestronglyMeasurable ((2 * τ) ^ 2) ?_
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [hbound z, norm_nonneg
    (upperResidualBatchMean I.oracle (upperClip τ) (x z.1) (w z.1) z.2 -
      upperResidualSourceMean I.oracle (upperClip τ) (x z.1) (w z.1))]

/-- Averaging the fixed-history variance bound gives the same `1/b` rate
for arbitrary measurable predictable decisions and centers. -/
theorem Admissible.predictable_upperClippedBatchMean_secondMoment_le
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar τ : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hτ : 0 < τ) (historyLaw : Measure History)
    [IsProbabilityMeasure historyLaw]
    (x w : History → Point d) (hx : Measurable x) (hw : Measurable w)
    (hb : 0 < b) :
    (∫ z : History × (Fin b → Seed),
      ‖upperResidualBatchMean I.oracle (upperClip τ) (x z.1) (w z.1) z.2 -
        upperResidualSourceMean I.oracle (upperClip τ) (x z.1) (w z.1)‖ ^ 2
      ∂historyLaw.prod (freshSeedLaw I.oracle b)) ≤
      (b : ℝ)⁻¹ * ((2 * τ) ^ (2 - p) * σ ^ p) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle b) := by
    unfold freshSeedLaw
    infer_instance
  have hInt := I.predictable_upperClippedBatchError_sq_integrable hτ
    historyLaw x w hx hw hb
  rw [integral_prod _ hInt]
  calc
    (∫ h : History, ∫ seeds : Fin b → Seed,
      ‖upperResidualBatchMean I.oracle (upperClip τ) (x h) (w h) seeds -
        upperResidualSourceMean I.oracle (upperClip τ) (x h) (w h)‖ ^ 2
      ∂freshSeedLaw I.oracle b ∂historyLaw) ≤
      ∫ _h : History, (b : ℝ)⁻¹ * ((2 * τ) ^ (2 - p) * σ ^ p)
      ∂historyLaw := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun h => integral_nonneg
            (fun seeds => sq_nonneg _))
        · exact integrable_const _
        · exact Filter.Eventually.of_forall (fun h =>
            I.upperClippedBatchMean_secondMoment_le hτ (x h) (w h) hb)
    _ = (b : ℝ)⁻¹ * ((2 * τ) ^ (2 - p) * σ ^ p) := by simp

end HeavyTailedNoise
