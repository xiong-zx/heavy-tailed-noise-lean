import HeavyTailedNoise.Upper.K1.ActualBatchMomentTransfer

/-!
The actual shared-kernel batch error has conditional mean zero given the
complete transcript and private index before that batch. The conditioning
sigma-field is generated once at the batch boundary, never after a response
inside the current shared batch.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Pull a set-restricted Bochner integral through an arbitrary measurable,
measure-preserving map. Injectivity is not required: the map may discard the
future seed coordinates. -/
private theorem setIntegral_preimage_of_measurePreserving
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {ν : Measure β} {F : α → β}
    (hF : MeasurePreserving F μ ν) (g : β → E)
    (hg : StronglyMeasurable g) {s : Set β} (hs : MeasurableSet s) :
    (∫ x in F ⁻¹' s, g (F x) ∂μ) = ∫ y in s, g y ∂ν := by
  have hpre : MeasurableSet (F ⁻¹' s) := hF.measurable hs
  calc
    (∫ x in F ⁻¹' s, g (F x) ∂μ) =
        ∫ x, s.indicator g (F x) ∂μ := by
          rw [← integral_indicator hpre]
          rfl
    _ = ∫ y, s.indicator g y ∂ν := by
      rw [← hF.map_eq]
      exact (integral_map_of_stronglyMeasurable hF.measurable
        (hg.indicator hs)).symm
    _ = ∫ y in s, g y ∂ν := integral_indicator hs

/-- On the actual full private/seed space, conditioning on the complete
pre-batch history annihilates the whole centered `kernelPhi` batch error. -/
theorem actualKernelBatchError_condExp_prebatch_zero
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u : Fin P.T) (k : ℕ) :
    (((algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw O (responseCount P)))[
        (actualKernelBatchError P O u k) |
        MeasurableSpace.comap
          (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
            batchHistoryOfRun P O u z)
          (inferInstance : MeasurableSpace (BatchHistory P d u))])
      =ᵐ[((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))] 0 := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw O (responseCount P)) :=
    freshSeedLaw_probability O (responseCount P)
  letI : IsProbabilityMeasure (freshSeedLaw O P.n) :=
    freshSeedLaw_probability O P.n
  letI : IsProbabilityMeasure (batchPastHistoryLaw P O u) := by
    unfold batchPastHistoryLaw
    infer_instance
  let globalLaw := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw O (responseCount P))
  let targetLaw := (batchPastHistoryLaw P O u).prod (freshSeedLaw O P.n)
  let pathMap : (Fin P.T × (Fin (responseCount P) → Seed)) →
      BatchHistory P d u × (Fin P.n → Seed) := fun z =>
    (batchHistoryOfRun P O u z, batchSeedBlock P u z.2)
  let historyMap : (Fin P.T × (Fin (responseCount P) → Seed)) →
      BatchHistory P d u := fun z => batchHistoryOfRun P O u z
  let err := kernelBatchErrorAtHistory P O u k
  have hmap : MeasurePreserving pathMap globalLaw targetLaw :=
    measurePreserving_actualHistory_currentBatch P O u
  have hIntTarget : Integrable err targetLaw :=
    integrable_kernelBatchErrorAtHistory P O u k
  have hInt : Integrable (actualKernelBatchError P O u k) globalLaw := by
    have h := hmap.integrable_comp_of_integrable hIntTarget
    change Integrable (err ∘ pathMap) globalLaw
    exact h
  have hm : MeasurableSpace.comap historyMap
      (inferInstance : MeasurableSpace (BatchHistory P d u)) ≤
      (inferInstance : MeasurableSpace
        (Fin P.T × (Fin (responseCount P) → Seed))) :=
    (measurable_batchHistoryOfRun P O u).comap_le
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hInt ?_ ?_ ?_
  · intro s hs hfinite
    exact integrable_zero _ _ _
  · intro s hs hfinite
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hset : (historyMap ⁻¹' t :
        Set (Fin P.T × (Fin (responseCount P) → Seed))) =
        pathMap ⁻¹' (t ×ˢ Set.univ) := by
      ext z
      simp only [historyMap, pathMap, Set.mem_preimage, Set.mem_prod, Set.mem_univ,
        and_true]
    have htargetSet : MeasurableSet (t ×ˢ Set.univ :
        Set (BatchHistory P d u × (Fin P.n → Seed))) :=
      ht.prod MeasurableSet.univ
    have hfixed (H : BatchHistory P d u) :
        (∫ seeds : Fin P.n → Seed, err (H, seeds) ∂freshSeedLaw O P.n) = 0 := by
      change (∫ seeds : Fin P.n → Seed,
        upperResidualBatchMean O (kernelPhi P k)
            (batchDecision P u H) (batchCenter P u H) seeds -
          upperResidualSourceMean O (kernelPhi P k)
            (batchDecision P u H) (batchCenter P u H)
        ∂freshSeedLaw O P.n) = 0
      exact upperResidualBatchMean_centered_inner O (kernelPhi P k)
        (measurable_kernelPhi P k) (kernelPhiBound P k)
        (fun z => kernelPhi_norm_le P k z)
        (batchDecision P u H) (batchCenter P u H) P.n_pos
    have htargetZero : (∫ z in t ×ˢ Set.univ, err z ∂targetLaw) = 0 := by
      rw [setIntegral_prod _ hIntTarget.integrableOn]
      simp only [Measure.restrict_univ]
      simp_rw [hfixed]
      simp
    simp only [Pi.zero_apply, integral_zero]
    rw [hset]
    symm
    change (∫ z in pathMap ⁻¹' (t ×ˢ Set.univ), err (pathMap z)
      ∂globalLaw) = 0
    rw [setIntegral_preimage_of_measurePreserving hmap err
      (measurable_kernelBatchErrorAtHistory P O u k).stronglyMeasurable
      htargetSet]
    exact htargetZero
  · exact stronglyMeasurable_zero.aestronglyMeasurable

end

end HeavyTailedNoise.UpperK1
