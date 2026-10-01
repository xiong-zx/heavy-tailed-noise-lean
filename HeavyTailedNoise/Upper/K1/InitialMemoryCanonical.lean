import HeavyTailedNoise.Upper.K1.ActualEstimatorKernelIdentity
import HeavyTailedNoise.Upper.K1.InitialMemoryPhysicalMoment

/-!
Identify the initial term in the canonical completed-estimator identity with
the one-block sample error. In the absent-batch branch the algebraic term
vanishes only at positive runtime times, using the literal `q=1` coefficient
rule or an empty band family. Its squared risk is then read on the seed-only
tape used by the public output rule.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- The source mean at algebraic time zero is evaluated at the actual first
runtime point and the actual seed-zero clipping center. -/
theorem actualBandSourceMean_zero_eq_firstSeed
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (j : Fin P.J) :
    actualBandSourceMean P O seeds j 0 =
      upperResidualSourceMean O (highBand P j) 0
        (O.response 0 (seeds ⟨0, responseCount_pos P⟩)) := by
  let u : Fin P.T := ⟨0, P.T_pos⟩
  let z : Fin P.T × (Fin (responseCount P) → Seed) := (u, seeds)
  let H := batchHistoryOfRun P O u z
  have hpre : boundaryTranscript P O 0 (Nat.zero_le P.T) z = H.2 :=
    boundaryTranscript_eq_batchHistory P O u z
  have hpoint := (stateAt_firstRuntime_point_center P
    (boundaryTranscript P O 0 (Nat.zero_le P.T) z)).1
  have hcenter := firstRuntime_center_eq_firstResponse P O z
  have hdec : batchDecision P u H = 0 := by
    change point P (stateAt P (batchStart P 0) H.2) = 0
    rw [← hpre]
    exact hpoint
  have hcen : batchCenter P u H =
      O.response 0 (seeds ⟨0, responseCount_pos P⟩) := by
    change center P (stateAt P (batchStart P 0) H.2) = _
    rw [← hpre]
    exact hcenter
  rw [actualBandSourceMean]
  simp only [dif_pos P.T_pos]
  change upperResidualSourceMean O (highBand P j)
    (batchDecision P u H) (batchCenter P u H) = _
  rw [hdec, hcen]

/-- The seed-only law gives the same squared sample-error integral as the
full private-index × seed law, because this initialization term ignores the
private output index. -/
theorem actualInitialMemorySampleError_sq_seed_eq_joint
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ) :
    (∫ seeds : Fin (responseCount P) → Seed,
      ‖actualInitialMemorySampleError P O seeds t‖ ^ 2
      ∂freshSeedLaw O (responseCount P)) =
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ‖actualInitialMemorySampleError P O z.2 t‖ ^ 2
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) := by
  by_cases hpos : 0 < initialResponses P
  · letI : IsProbabilityMeasure O.law := O.law_probability
    letI : IsProbabilityMeasure (freshSeedLaw O (initialResponses P)) :=
      freshSeedLaw_probability O (initialResponses P)
    let pairLaw := O.law.prod (freshSeedLaw O (initialResponses P))
    let f : Seed × (Fin (initialResponses P) → Seed) → ℝ :=
      fun y => ‖initialMemoryErrorAtPair P O t y‖ ^ 2
    have hfMeas : StronglyMeasurable f :=
      ((measurable_initialMemoryErrorAtPair P O t).norm.pow_const 2).stronglyMeasurable
    have hfInt : Integrable f pairLaw :=
      initialMemoryErrorAtPair_sq_integrable P O t
    have hmap := measurePreserving_first_initialSeedBlock P O
    have hseed :
        (∫ seeds : Fin (responseCount P) → Seed,
          ‖actualInitialMemorySampleError P O seeds t‖ ^ 2
          ∂freshSeedLaw O (responseCount P)) =
        ∫ y, f y ∂pairLaw := by
      have hpoint (seeds : Fin (responseCount P) → Seed) :
          ‖actualInitialMemorySampleError P O seeds t‖ ^ 2 =
          f (seeds ⟨0, responseCount_pos P⟩,
            initialSeedBlock P seeds) := by
        rw [actualInitialMemorySampleError_eq_pair P O seeds t hpos]
      simp_rw [hpoint]
      change (∫ seeds : Fin (responseCount P) → Seed,
        f (seeds ⟨0, responseCount_pos P⟩,
          initialSeedBlock P seeds)
        ∂freshSeedLaw O (responseCount P)) =
        ∫ y, f y ∂(O.law.prod
          (freshSeedLaw O (initialResponses P)))
      rw [← hmap.map_eq]
      exact (integral_map_of_stronglyMeasurable
        hmap.measurable hfMeas).symm
    have hjoint :
        (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖actualInitialMemorySampleError P O z.2 t‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw O (responseCount P)))) =
        ∫ y, f y ∂pairLaw := by
      calc
        _ = ∫ ξ₀ : Seed,
              ∫ seeds : Fin (initialResponses P) → Seed,
                ‖initialMemoryErrorAtPair P O t (ξ₀, seeds)‖ ^ 2
                ∂freshSeedLaw O (initialResponses P) ∂O.law :=
          actualInitialMemorySampleError_secondMoment_eq_pair P O t hpos
        _ = ∫ y, f y ∂pairLaw :=
          (integral_prod _ hfInt).symm
    exact hseed.trans hjoint.symm
  · have hzero : initialResponses P = 0 := Nat.eq_zero_of_not_pos hpos
    have hfun : (fun seeds : Fin (responseCount P) → Seed =>
        ‖actualInitialMemorySampleError P O seeds t‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext seeds
      rw [actualInitialMemorySampleError_zero_of_no_initial P O seeds t hzero]
      simp
    rw [hfun]
    have hfunJoint : (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        ‖actualInitialMemorySampleError P O z.2 t‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext z
      rw [actualInitialMemorySampleError_zero_of_no_initial P O z.2 t hzero]
      simp
    rw [hfunJoint]
    simp

/-- The initialization error appearing in the estimator identity is exactly
the controlled one-block sample error for every positive runtime time. -/
theorem Admissible.paperSchedule_actualInitialMemoryError_eq_sampleError
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch)
    (hκ : 0 < κ) (hκle : κ ≤ 1)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    (seeds : Fin (responseCount
      (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
        hε hch hCb hCI)) → Seed)
    (t : ℕ) (ht : 0 < t) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    actualInitialMemoryError P I.oracle seeds t =
      actualInitialMemorySampleError P I.oracle seeds t := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  dsimp only
  by_cases hpos : 0 < initialResponses P
  · let w := I.oracle.response 0 (seeds ⟨0, responseCount_pos P⟩)
    have hsource (j : Fin P.J) :
        actualBandSourceMean P I.oracle seeds j 0 =
          upperResidualSourceMean I.oracle (highBand P j) 0 w :=
      actualBandSourceMean_zero_eq_firstSeed P I.oracle seeds j
    calc
      actualInitialMemoryError P I.oracle seeds t =
          actualInitialMemoryContribution P I.oracle seeds t -
            ∑ j : Fin P.J, (1 - P.alpha j) ^ t •
              actualBandSourceMean P I.oracle seeds j 0 := by
        unfold actualInitialMemoryError actualInitialMemoryContribution
        simp_rw [smul_sub]
        rw [Finset.sum_sub_distrib]
      _ = actualInitialMemoryContribution P I.oracle seeds t -
            upperResidualSourceMean I.oracle (initialMemoryKernel P t) 0 w := by
        congr 1
        simp_rw [hsource]
        exact (initialMemoryKernel_sourceMean P I.oracle t 0 w).symm
      _ = actualInitialMemorySampleError P I.oracle seeds t := by
        simp [actualInitialMemorySampleError, hpos, w]
  · have hzero : initialResponses P = 0 := Nat.eq_zero_of_not_pos hpos
    have hnotuse : ¬useInitialBatch P := by
      intro hused
      have hnI : initialResponses P = P.nI := by
        simp [initialResponses, hused]
      have hnIpos := P.nI_pos
      omega
    have herror : actualInitialMemoryError P I.oracle seeds t = 0 := by
      by_cases hJ : P.J = 0
      · simp [actualInitialMemoryError, hJ]
      · have hJpos : 0 < P.J := Nat.pos_of_ne_zero hJ
        have hqle : q ≤ 1 := by
          apply le_of_not_gt
          intro hqgt
          exact hnotuse ⟨hqgt, hJpos⟩
        have hqeq : q = 1 := le_antisymm hqle I.q_range
        have hαone (j : Fin P.J) : P.alpha j = 1 := by
          change paperAlpha p q κ j.val = 1
          calc
            paperAlpha p q κ j.val = paperAlpha p 1 κ j.val :=
              congrArg (fun r => paperAlpha p r κ j.val) hqeq
            _ = 1 := paperAlpha_q_one p κ hκ hκle j.val
        unfold actualInitialMemoryError
        apply Finset.sum_eq_zero
        intro j hj
        rw [hαone j]
        simp [Nat.ne_of_gt ht]
    rw [herror,
      actualInitialMemorySampleError_zero_of_no_initial P I.oracle
        seeds t hzero]

/-- Seed-only L² risk for the exact initialization term used by the
completed estimator; this is the format consumed by the final time average. -/
theorem Admissible.paperSchedule_actualInitialMemoryError_average_seed_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch)
    (hκ : 0 < κ) (hκle : κ ≤ 1)
    (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    (P.T : ℝ)⁻¹ *
      ∑ u : Fin P.T,
        (∫ seeds : Fin (responseCount P) → Seed,
          ‖actualInitialMemoryError P I.oracle seeds (u.val + 1)‖ ^ 2
          ∂freshSeedLaw I.oracle (responseCount P)) ≤
      4 * ε ^ 2 / CI := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  change (P.T : ℝ)⁻¹ *
    (∑ u : Fin P.T,
      ∫ seeds : Fin (responseCount P) → Seed,
        ‖actualInitialMemoryError P I.oracle seeds (u.val + 1)‖ ^ 2
        ∂freshSeedLaw I.oracle (responseCount P)) ≤
      4 * ε ^ 2 / CI
  have hterm (u : Fin P.T) :
      (∫ seeds : Fin (responseCount P) → Seed,
        ‖actualInitialMemoryError P I.oracle seeds (u.val + 1)‖ ^ 2
        ∂freshSeedLaw I.oracle (responseCount P)) =
      (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
        ‖actualInitialMemorySampleError P I.oracle z.2 (u.val + 1)‖ ^ 2
        ∂((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw I.oracle (responseCount P)))) := by
    have hpoint (seeds : Fin (responseCount P) → Seed) :
        actualInitialMemoryError P I.oracle seeds (u.val + 1) =
          actualInitialMemorySampleError P I.oracle seeds (u.val + 1) :=
      Admissible.paperSchedule_actualInitialMemoryError_eq_sampleError I
        ε Ctail ch κ Cb CI hε hch hκ hκle hCb hCI
        seeds (u.val + 1) (Nat.zero_lt_succ _)
    simp_rw [hpoint]
    exact actualInitialMemorySampleError_sq_seed_eq_joint P I.oracle
      (u.val + 1)
  have hsum :
      (∑ u : Fin P.T,
        ∫ seeds : Fin (responseCount P) → Seed,
          ‖actualInitialMemoryError P I.oracle seeds (u.val + 1)‖ ^ 2
          ∂freshSeedLaw I.oracle (responseCount P)) =
      ∑ u : Fin P.T,
        ∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖actualInitialMemorySampleError P I.oracle z.2 (u.val + 1)‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw I.oracle (responseCount P))) := by
    apply Finset.sum_congr rfl
    intro u hu
    exact hterm u
  rw [hsum]
  exact Admissible.paperSchedule_actualInitialMemory_average_secondMoment_le I
    ε Ctail ch κ Cb CI hε hch hκ hCb hCI

end

end HeavyTailedNoise.UpperK1
