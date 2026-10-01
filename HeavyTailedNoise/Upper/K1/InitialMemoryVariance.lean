import HeavyTailedNoise.Upper.K1.InitialMemoryCombined
import HeavyTailedNoise.Upper.K1.InitialSeedProduct

/-!
Exact second moment of the decaying initial high-band sample error on the
one global seed tape. The first seed is integrated as the clipping center;
the optional initialization block remains one independent product block.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

def initialMemoryErrorAtPair {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (t : ℕ)
    (z : Seed × (Fin (initialResponses P) → Seed)) : Point d :=
  upperResidualBatchMean O (initialMemoryKernel P t) 0
      (O.response 0 z.1) z.2 -
    upperResidualSourceMean O (initialMemoryKernel P t) 0
      (O.response 0 z.1)

def actualInitialMemorySampleError {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ) : Point d :=
  if 0 < initialResponses P then
    actualInitialMemoryContribution P O seeds t -
      upperResidualSourceMean O (initialMemoryKernel P t) 0
        (O.response 0 (seeds ⟨0, responseCount_pos P⟩))
  else 0

theorem actualInitialMemorySampleError_zero_of_no_initial
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ)
    (hzero : initialResponses P = 0) :
    actualInitialMemorySampleError P O seeds t = 0 := by
  simp [actualInitialMemorySampleError, hzero]

theorem actualInitialMemorySampleError_eq_pair
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ)
    (hpos : 0 < initialResponses P) :
    actualInitialMemorySampleError P O seeds t =
      initialMemoryErrorAtPair P O t
        (seeds ⟨0, responseCount_pos P⟩, initialSeedBlock P seeds) := by
  simp only [actualInitialMemorySampleError, if_pos hpos,
    initialMemoryErrorAtPair,
    actualInitialMemoryContribution_eq_batchMean P O seeds t hpos]

theorem measurable_initialMemoryErrorAtPair
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ) :
    Measurable (initialMemoryErrorAtPair P O t) := by
  have hw : Measurable (O.response 0) :=
    O.measurable_response.comp (measurable_const.prodMk measurable_id)
  exact (measurable_upperResidualBatchMean O (initialMemoryKernel P t)
    (measurable_initialMemoryKernel P t) (fun _ : Seed => 0)
    (O.response 0) measurable_const hw).sub
      ((measurable_upperResidualSourceMean O (initialMemoryKernel P t)
        (measurable_initialMemoryKernel P t) (fun _ : Seed => 0)
        (O.response 0) measurable_const hw).comp measurable_fst)

/-- The squared error is integrable even though the first raw response may
have no second moment. Every vector evaluated here is clipped before the
square, and the combined transform has a deterministic finite bound. -/
theorem initialMemoryErrorAtPair_sq_integrable
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ) :
    Integrable (fun z : Seed × (Fin (initialResponses P) → Seed) =>
      ‖initialMemoryErrorAtPair P O t z‖ ^ 2)
      (O.law.prod (freshSeedLaw O (initialResponses P))) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw O (initialResponses P)) :=
    freshSeedLaw_probability O (initialResponses P)
  let μ := O.law.prod (freshSeedLaw O (initialResponses P))
  let φ : Point d → Point d := initialMemoryKernel P t
  let C : ℝ := initialMemoryKernelBound P t
  have hw : Measurable (O.response 0) :=
    O.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hcoord (i : Fin (initialResponses P)) : MemLp
      (fun z : Seed × (Fin (initialResponses P) → Seed) =>
        φ (O.response 0 (z.2 i) - O.response 0 z.1)) 2 μ := by
    have hm : Measurable (fun z : Seed ×
        (Fin (initialResponses P) → Seed) =>
        φ (O.response 0 (z.2 i) - O.response 0 z.1)) :=
      (measurable_initialMemoryKernel P t).comp
        ((O.measurable_response.comp
          (measurable_const.prodMk
            ((measurable_pi_apply i).comp measurable_snd))).sub
          (hw.comp measurable_fst))
    exact MemLp.of_bound hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun z =>
        initialMemoryKernel_norm_le P t _))
  have hsum : MemLp
      (fun z : Seed × (Fin (initialResponses P) → Seed) =>
        ∑ i : Fin (initialResponses P),
          φ (O.response 0 (z.2 i) - O.response 0 z.1)) 2 μ := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    exact hcoord i
  have hbatch : MemLp
      (fun z : Seed × (Fin (initialResponses P) → Seed) =>
        upperResidualBatchMean O φ 0 (O.response 0 z.1) z.2) 2 μ := by
    have hrepr :
        (fun z : Seed × (Fin (initialResponses P) → Seed) =>
          upperResidualBatchMean O φ 0 (O.response 0 z.1) z.2) =
        (initialResponses P : ℝ)⁻¹ •
          (fun z => ∑ i : Fin (initialResponses P),
            φ (O.response 0 (z.2 i) - O.response 0 z.1)) := by
      funext z
      rfl
    rw [hrepr]
    exact hsum.const_smul (initialResponses P : ℝ)⁻¹
  have hsourceMeas : Measurable
      (fun z : Seed × (Fin (initialResponses P) → Seed) =>
        upperResidualSourceMean O φ 0 (O.response 0 z.1)) :=
    (measurable_upperResidualSourceMean O φ
      (measurable_initialMemoryKernel P t) (fun _ : Seed => 0)
      (O.response 0) measurable_const hw).comp measurable_fst
  have hsourceBound (ξ₀ : Seed) :
      ‖upperResidualSourceMean O φ 0 (O.response 0 ξ₀)‖ ≤ C := by
    unfold upperResidualSourceMean
    have hprob : O.law.real Set.univ = 1 := by simp
    simpa only [φ, C, hprob, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := O.law)
        (Filter.Eventually.of_forall (fun ξ =>
          initialMemoryKernel_norm_le P t
            (O.response 0 ξ - O.response 0 ξ₀))))
  have hsource : MemLp
      (fun z : Seed × (Fin (initialResponses P) → Seed) =>
        upperResidualSourceMean O φ 0 (O.response 0 z.1)) 2 μ :=
    MemLp.of_bound hsourceMeas.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun z => hsourceBound z.1))
  have herr : MemLp (initialMemoryErrorAtPair P O t) 2 μ := by
    exact hbatch.sub hsource
  exact (herr.norm).integrable_sq

/-- Exact joint L² identity under the original global tape and private
output-index law. Both sides integrate over the first seed; no conditional
moment of the raw residual is introduced. -/
theorem actualInitialMemorySampleError_secondMoment
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ)
    (hpos : 0 < initialResponses P) :
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ‖actualInitialMemorySampleError P O z.2 t‖ ^ 2
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) =
      ∫ ξ₀ : Seed,
        (initialResponses P : ℝ)⁻¹ *
          ∫ ξ : Seed,
            ‖initialMemoryKernel P t
                (O.response 0 ξ - O.response 0 ξ₀) -
              upperResidualSourceMean O (initialMemoryKernel P t) 0
                (O.response 0 ξ₀)‖ ^ 2 ∂O.law ∂O.law := by
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw O (responseCount P)) :=
    freshSeedLaw_probability O (responseCount P)
  letI : IsProbabilityMeasure (freshSeedLaw O (initialResponses P)) :=
    freshSeedLaw_probability O (initialResponses P)
  let globalLaw := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw O (responseCount P))
  let pairLaw := O.law.prod (freshSeedLaw O (initialResponses P))
  let f : Seed × (Fin (initialResponses P) → Seed) → ℝ :=
    fun y => ‖initialMemoryErrorAtPair P O t y‖ ^ 2
  have hfInt : Integrable f pairLaw :=
    initialMemoryErrorAtPair_sq_integrable P O t
  have hfMeas : StronglyMeasurable f :=
    ((measurable_initialMemoryErrorAtPair P O t).norm.pow_const 2).stronglyMeasurable
  have hdrop : MeasurePreserving
      (Prod.snd : Fin P.T × (Fin (responseCount P) → Seed) →
        (Fin (responseCount P) → Seed))
      globalLaw (freshSeedLaw O (responseCount P)) := measurePreserving_snd
  have hpair : MeasurePreserving
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        (z.2 ⟨0, responseCount_pos P⟩, initialSeedBlock P z.2))
      globalLaw pairLaw := by
    exact (measurePreserving_first_initialSeedBlock P O).comp hdrop
  have htransport :
      (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
        f (z.2 ⟨0, responseCount_pos P⟩, initialSeedBlock P z.2)
        ∂globalLaw) = ∫ y, f y ∂pairLaw := by
    rw [← hpair.map_eq]
    exact (integral_map_of_stronglyMeasurable hpair.measurable hfMeas).symm
  have hpoint (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      actualInitialMemorySampleError P O z.2 t =
        initialMemoryErrorAtPair P O t
          (z.2 ⟨0, responseCount_pos P⟩, initialSeedBlock P z.2) :=
    actualInitialMemorySampleError_eq_pair P O z.2 t hpos
  simp_rw [hpoint]
  change (∫ z, f (z.2 ⟨0, responseCount_pos P⟩,
    initialSeedBlock P z.2) ∂globalLaw) = _
  rw [htransport, integral_prod _ hfInt]
  congr 1
  funext ξ₀
  exact initialMemoryKernel_batch_secondMoment P O t
    (O.response 0 ξ₀) hpos

theorem actualInitialMemorySampleError_secondMoment_eq_pair
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ)
    (hpos : 0 < initialResponses P) :
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ‖actualInitialMemorySampleError P O z.2 t‖ ^ 2
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) =
      ∫ ξ₀ : Seed,
        ∫ seeds : Fin (initialResponses P) → Seed,
          ‖initialMemoryErrorAtPair P O t (ξ₀, seeds)‖ ^ 2
          ∂freshSeedLaw O (initialResponses P) ∂O.law := by
  rw [actualInitialMemorySampleError_secondMoment P O t hpos]
  congr 1
  funext ξ₀
  exact (initialMemoryKernel_batch_secondMoment P O t
    (O.response 0 ξ₀) hpos).symm

end

end HeavyTailedNoise.UpperK1
