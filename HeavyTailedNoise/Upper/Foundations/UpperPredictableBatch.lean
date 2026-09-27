import HeavyTailedNoise.Upper.Foundations.UpperBatchProtocol
import HeavyTailedNoise.Upper.Foundations.UpperMomentFoundations

/-!
Predictable fixed batches in the shared gradient-only model. History has an arbitrary
probability law and is independent of the fresh batch. Uniform centered moments make
the centered batch mean integrable without an integrability assumption on the decision.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace HeavyTailedNoise

/-- Integrating the fresh batch first fixes every pre-batch decision. -/
theorem Admissible.predictable_upperBatchMean_inner
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x : History → Point d) (hb : 0 < b) (h : History) :
    (∫ seeds, upperBatchMean I.oracle (x h) seeds
      ∂freshSeedLaw I.oracle b) = I.objective.grad (x h) := by
  exact upperBatchMean_unbiased I.oracle (x h) (I.objective.grad (x h)) hb
    (I.integrable_response (x h)) (I.unbiased (x h))

/-- Exact outer integral identity without an implicit Fubini assumption. -/
theorem Admissible.predictable_upperBatchMean_iterated_integral
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (historyLaw : Measure History) (x : History → Point d) (hb : 0 < b) :
    (∫ h, ∫ seeds, upperBatchMean I.oracle (x h) seeds
      ∂freshSeedLaw I.oracle b ∂historyLaw) =
      ∫ h, I.objective.grad (x h) ∂historyLaw := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (I.predictable_upperBatchMean_inner x hb)

/-- Each centered fresh coordinate is jointly integrable under independent history. -/
theorem Admissible.predictable_freshBatch_coordinate_centered_integrable
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x : History → Point d) (hx : Measurable x) (i : Fin b) :
    Integrable (fun z : History × (Fin b → Seed) =>
      I.oracle.response (x z.1) (z.2 i) - I.objective.grad (x z.1))
      (historyLaw.prod (freshSeedLaw I.oracle b)) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle b) := by
    unfold freshSeedLaw
    infer_instance
  let e : History × (Fin b → Seed) → Point d := fun z =>
    I.oracle.response (x z.1) (z.2 i) - I.objective.grad (x z.1)
  have he : Measurable e := by
    exact (I.oracle.measurable_response.comp
      ((hx.comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))).sub
      (I.objective.continuous_grad.measurable.comp (hx.comp measurable_fst))
  have heMoment : Measurable (fun z => ENNReal.ofReal (‖e z‖ ^ p)) := by
    fun_prop
  have hmoment : (∫⁻ z, ENNReal.ofReal (‖e z‖ ^ p)
      ∂historyLaw.prod (freshSeedLaw I.oracle b)) ≤ ENNReal.ofReal (σ ^ p) := by
    rw [lintegral_prod _ heMoment.aemeasurable]
    exact I.predictable_freshBatch_coordinate_centered_moment historyLaw x hx b i
  have hnorm (z : History × (Fin b → Seed)) : ‖e z‖ ≤ 1 + ‖e z‖ ^ p := by
    by_cases h : ‖e z‖ ≤ 1
    · linarith [Real.rpow_nonneg (norm_nonneg (e z)) p]
    · have hpow := Real.self_le_rpow_of_one_le (le_of_not_ge h) I.p_range.1.le
      linarith
  refine ⟨he.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hbound : (∫⁻ z, ENNReal.ofReal ‖e z‖
      ∂historyLaw.prod (freshSeedLaw I.oracle b)) ≤ 1 + ENNReal.ofReal (σ ^ p) := by
    calc
      _ ≤ ∫⁻ z, 1 + ENNReal.ofReal (‖e z‖ ^ p)
          ∂historyLaw.prod (freshSeedLaw I.oracle b) := by
        apply lintegral_mono
        intro z
        calc
          _ ≤ ENNReal.ofReal (1 + ‖e z‖ ^ p) := ENNReal.ofReal_le_ofReal (hnorm z)
          _ = _ := by
            rw [ENNReal.ofReal_add (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)]
            simp
      _ = 1 + ∫⁻ z, ENNReal.ofReal (‖e z‖ ^ p)
          ∂historyLaw.prod (freshSeedLaw I.oracle b) := by
        rw [lintegral_add_left measurable_const _]
        simp
      _ ≤ _ := add_le_add le_rfl hmoment
  exact lt_of_le_of_lt hbound (by finiteness)

/-- The centered mean is integrable even if the predicted gradient is not. -/
theorem Admissible.predictable_upperBatchMean_centered_integrable
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x : History → Point d) (hx : Measurable x) (hb : 0 < b) :
    Integrable (fun z : History × (Fin b → Seed) =>
      upperBatchMean I.oracle (x z.1) z.2 - I.objective.grad (x z.1))
      (historyLaw.prod (freshSeedLaw I.oracle b)) := by
  have hbReal : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hsum : Integrable (fun z : History × (Fin b → Seed) =>
      ∑ i : Fin b, (I.oracle.response (x z.1) (z.2 i) - I.objective.grad (x z.1)))
      (historyLaw.prod (freshSeedLaw I.oracle b)) := by
    apply integrable_finsetSum
    intro i hi
    exact I.predictable_freshBatch_coordinate_centered_integrable historyLaw x hx i
  have hrepr : (fun z : History × (Fin b → Seed) =>
      upperBatchMean I.oracle (x z.1) z.2 - I.objective.grad (x z.1)) =
      (b : ℝ)⁻¹ • (fun z : History × (Fin b → Seed) =>
        ∑ i : Fin b, (I.oracle.response (x z.1) (z.2 i) - I.objective.grad (x z.1))) := by
    funext z
    simp only [Pi.smul_apply, upperBatchMean, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_fin, smul_sub]
    rw [← Nat.cast_smul_eq_nsmul ℝ b (I.objective.grad (x z.1)), smul_smul,
      inv_mul_cancel₀ hbReal, one_smul]
  rw [hrepr]
  exact hsum.smul (b : ℝ)⁻¹

/-- Each fixed history has zero integrated centered batch mean. -/
theorem Admissible.predictable_upperBatchMean_centered_inner
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x : History → Point d) (hb : 0 < b) (h : History) :
    (∫ seeds, upperBatchMean I.oracle (x h) seeds - I.objective.grad (x h)
      ∂freshSeedLaw I.oracle b) = 0 := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle b) := by
    unfold freshSeedLaw
    infer_instance
  have hbatch : Integrable (upperBatchMean I.oracle (x h))
      (freshSeedLaw I.oracle b) :=
    upperBatchMean_integrable (b := b) I.oracle (x h) (I.integrable_response (x h))
  rw [integral_sub hbatch (integrable_const _),
    I.predictable_upperBatchMean_inner x hb h]
  simp

/-- Conditional unbiasedness of the centered fixed batch given arbitrary independent
pre-batch history, with no integrability assumption on the predicted gradient. -/
theorem Admissible.predictable_upperBatchMean_centered_condExp
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x : History → Point d) (hx : Measurable x) (hb : 0 < b) :
    (historyLaw.prod (freshSeedLaw I.oracle b))[
      (fun z : History × (Fin b → Seed) =>
        upperBatchMean I.oracle (x z.1) z.2 - I.objective.grad (x z.1)) |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace History)]
      =ᵐ[historyLaw.prod (freshSeedLaw I.oracle b)] 0 := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle b) := by
    unfold freshSeedLaw
    infer_instance
  have hm : MeasurableSpace.comap (Prod.fst : History × (Fin b → Seed) → History)
      (inferInstance : MeasurableSpace History) ≤
      (inferInstance : MeasurableSpace (History × (Fin b → Seed))) :=
    (measurable_fst : Measurable (Prod.fst : History × (Fin b → Seed) → History)).comap_le
  have hInt := I.predictable_upperBatchMean_centered_integrable historyLaw x hx hb
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hInt ?_ ?_ ?_
  · intro s hs hfinite
    exact integrable_zero _ _ _
  · intro s hs hfinite
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hset : (Prod.fst ⁻¹' t : Set (History × (Fin b → Seed))) = t ×ˢ Set.univ := by
      ext z
      simp
    rw [hset]
    simp only [Pi.zero_apply, integral_zero]
    rw [setIntegral_prod _ hInt.integrableOn]
    simp only [Measure.restrict_univ]
    simp_rw [I.predictable_upperBatchMean_centered_inner x hb]
    simp
  · exact stronglyMeasurable_zero.aestronglyMeasurable

/-- The centered mean has zero joint expectation. -/
theorem Admissible.predictable_upperBatchMean_centered_integral
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x : History → Point d) (hx : Measurable x) (hb : 0 < b) :
    (∫ z : History × (Fin b → Seed),
      upperBatchMean I.oracle (x z.1) z.2 - I.objective.grad (x z.1)
      ∂historyLaw.prod (freshSeedLaw I.oracle b)) = 0 := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle b) := by
    unfold freshSeedLaw
    infer_instance
  rw [integral_prod _ (I.predictable_upperBatchMean_centered_integrable historyLaw x hx hb)]
  simp_rw [I.predictable_upperBatchMean_centered_inner x hb]
  simp


/-- The uncentered mean is conditionally unbiased when the predicted gradient is integrable. -/
theorem Admissible.predictable_upperBatchMean_condExp
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x : History → Point d) (hx : Measurable x) (hb : 0 < b)
    (hgrad : Integrable (fun h => I.objective.grad (x h)) historyLaw) :
    (historyLaw.prod (freshSeedLaw I.oracle b))[
      (fun z : History × (Fin b → Seed) => upperBatchMean I.oracle (x z.1) z.2) |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace History)]
      =ᵐ[historyLaw.prod (freshSeedLaw I.oracle b)]
        (fun z => I.objective.grad (x z.1)) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle b) := by
    unfold freshSeedLaw
    infer_instance
  have hm : MeasurableSpace.comap (Prod.fst : History × (Fin b → Seed) → History)
      (inferInstance : MeasurableSpace History) ≤
      (inferInstance : MeasurableSpace (History × (Fin b → Seed))) :=
    (measurable_fst : Measurable (Prod.fst : History × (Fin b → Seed) → History)).comap_le
  have hgInt : Integrable (fun z : History × (Fin b → Seed) =>
      I.objective.grad (x z.1)) (historyLaw.prod (freshSeedLaw I.oracle b)) :=
    hgrad.comp_fst (freshSeedLaw I.oracle b)
  have hgMeas : StronglyMeasurable[MeasurableSpace.comap Prod.fst
    (inferInstance : MeasurableSpace History)] (fun z : History × (Fin b → Seed) =>
      I.objective.grad (x z.1)) := by
    exact ((I.objective.continuous_grad.measurable.comp hx).comp
      (Measurable.of_comap_le (le_refl
        (MeasurableSpace.comap (Prod.fst : History × (Fin b → Seed) → History)
          (inferInstance : MeasurableSpace History))))).stronglyMeasurable
  have hrepr : (fun z : History × (Fin b → Seed) =>
      upperBatchMean I.oracle (x z.1) z.2) =
      (fun z : History × (Fin b → Seed) =>
        upperBatchMean I.oracle (x z.1) z.2 - I.objective.grad (x z.1)) +
      (fun z : History × (Fin b → Seed) => I.objective.grad (x z.1)) := by
    funext z
    simp
  rw [hrepr]
  refine (condExp_add
    (I.predictable_upperBatchMean_centered_integrable historyLaw x hx hb) hgInt
    (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace History))).trans ?_
  rw [condExp_of_stronglyMeasurable hm hgMeas hgInt]
  filter_upwards [I.predictable_upperBatchMean_centered_condExp historyLaw x hx hb] with z hz
  simpa only [Pi.add_apply, hz, Pi.zero_apply, zero_add]

end HeavyTailedNoise
