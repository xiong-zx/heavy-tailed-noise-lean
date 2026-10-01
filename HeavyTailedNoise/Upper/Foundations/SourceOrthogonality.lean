import HeavyTailedNoise.Upper.Foundations.ClippedBatch

/-!
Orthogonality of one whole fresh-batch transformed error to a bounded vector
chosen from the history before that batch. The deterministic transform acts on
each returned residual as a whole; it may reuse that response across scales.
-/

namespace HeavyTailedNoise

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- A bounded measurable pre-batch vector is orthogonal in expectation to the
centered mean of one entire fresh batch. No within-batch partial history is
conditioned on, and no moment of the raw residual beyond boundedness of `φ`
is needed. -/
theorem upperResidualBatchMean_centered_predictable_inner
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x w h : History → Point d)
    (hx : Measurable x) (hw : Measurable w) (hh : Measurable h)
    (H : ℝ) (hH : ∀ η, ‖h η‖ ≤ H) (hb : 0 < b) :
    (∫ z : History × (Fin b → Seed),
      ⟪h z.1,
        upperResidualBatchMean O φ (x z.1) (w z.1) z.2 -
          upperResidualSourceMean O φ (x z.1) (w z.1)⟫_ℝ
      ∂historyLaw.prod (freshSeedLaw O b)) = 0 := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw O b) := by
    unfold freshSeedLaw
    infer_instance
  let μ := historyLaw.prod (freshSeedLaw O b)
  let err : History × (Fin b → Seed) → Point d := fun z =>
    upperResidualBatchMean O φ (x z.1) (w z.1) z.2 -
      upperResidualSourceMean O φ (x z.1) (w z.1)
  have herrInt : Integrable err μ :=
    (upperResidualBatchMean_joint_integrable O φ hφ C hC
      historyLaw x w hx hw).sub
      (upperResidualSourceMean_joint_integrable O φ hφ C hC
        historyLaw x w hx hw)
  have herrMeas : Measurable err :=
    (measurable_upperResidualBatchMean O φ hφ x w hx hw).sub
      ((measurable_upperResidualSourceMean O φ hφ x w hx hw).comp
        measurable_fst)
  have hhMeas : Measurable (fun z : History × (Fin b → Seed) => h z.1) :=
    hh.comp measurable_fst
  have hinnerMeas : Measurable (fun z => ⟪h z.1, err z⟫_ℝ) :=
    hhMeas.inner herrMeas
  have hinnerInt : Integrable (fun z => ⟪h z.1, err z⟫_ℝ) μ := by
    apply Integrable.mono' (herrInt.norm.const_mul H)
      hinnerMeas.aestronglyMeasurable
    filter_upwards [] with z
    calc
      ‖⟪h z.1, err z⟫_ℝ‖ = |⟪h z.1, err z⟫_ℝ| := Real.norm_eq_abs _
      _ ≤ ‖h z.1‖ * ‖err z‖ := abs_real_inner_le_norm _ _
      _ ≤ H * ‖err z‖ :=
        mul_le_mul_of_nonneg_right (hH z.1) (norm_nonneg _)
  have hfixed (η : History) :
      (∫ seeds : Fin b → Seed,
        ⟪h η, upperResidualBatchMean O φ (x η) (w η) seeds -
          upperResidualSourceMean O φ (x η) (w η)⟫_ℝ
        ∂freshSeedLaw O b) = 0 := by
    have hint : Integrable
        (fun seeds : Fin b → Seed =>
          upperResidualBatchMean O φ (x η) (w η) seeds -
            upperResidualSourceMean O φ (x η) (w η))
        (freshSeedLaw O b) :=
      (upperResidualBatchMean_integrable O φ hφ C hC (x η) (w η)).sub
        (integrable_const _)
    rw [integral_inner hint (h η),
      upperResidualBatchMean_centered_inner O φ hφ C hC (x η) (w η) hb]
    simp
  change (∫ z, ⟪h z.1, err z⟫_ℝ ∂μ) = 0
  rw [integral_prod _ hinnerInt]
  change (∫ η : History,
    ∫ seeds : Fin b → Seed,
      ⟪h η, upperResidualBatchMean O φ (x η) (w η) seeds -
        upperResidualSourceMean O φ (x η) (w η)⟫_ℝ
      ∂freshSeedLaw O b ∂historyLaw) = 0
  simp_rw [hfixed]
  simp

end

end HeavyTailedNoise
