import HeavyTailedNoise.Upper.K1.ActualBatchSecondMoment

/-!
Transport the fixed-decision whole-vector `kernelPhi` second-moment bound to
the actual adaptive runtime-batch path. Every high band still shares each
returned vector; no raw-gradient second moment is assumed.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem kernelSourceMoment_joint_integrable {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ) :
    Integrable (fun z : BatchHistory P d u × Seed =>
      ‖kernelPhi P k
        (O.response (batchDecision P u z.1) z.2 - batchCenter P u z.1)‖ ^ 2)
      ((batchPastHistoryLaw P O u).prod O.law) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (batchPastHistoryLaw P O u) := by
    unfold batchPastHistoryLaw
    infer_instance
  have hm : Measurable (fun z : BatchHistory P d u × Seed =>
      ‖kernelPhi P k
        (O.response (batchDecision P u z.1) z.2 - batchCenter P u z.1)‖ ^ 2) := by
    have hvec : Measurable (fun z : BatchHistory P d u × Seed =>
        kernelPhi P k
          (O.response (batchDecision P u z.1) z.2 - batchCenter P u z.1)) :=
      (measurable_kernelPhi P k).comp
        ((O.measurable_response.comp
          (((measurable_batchDecision P u).comp measurable_fst).prodMk
            measurable_snd)).sub
              ((measurable_batchCenter P u).comp measurable_fst))
    exact hvec.norm.pow_const 2
  have hbound (z : BatchHistory P d u × Seed) :
      ‖‖kernelPhi P k
        (O.response (batchDecision P u z.1) z.2 - batchCenter P u z.1)‖ ^ 2‖ ≤
        (kernelPhiBound P k) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (kernelPhi_norm_le P k _) 2
  exact Integrable.of_bound hm.aestronglyMeasurable
    ((kernelPhiBound P k) ^ 2) (Filter.Eventually.of_forall hbound)

/-- Average the already proved fixed-history whole-vector variance bound over
the complete pre-batch history. -/
theorem kernelBatchErrorAtHistory_secondMoment_le {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ) :
    (∫ z : BatchHistory P d u × (Fin P.n → Seed),
      ‖kernelBatchErrorAtHistory P O u k z‖ ^ 2
      ∂(batchPastHistoryLaw P O u).prod (freshSeedLaw O P.n)) ≤
      (P.n : ℝ)⁻¹ *
        ∫ H : BatchHistory P d u,
          ∫ ξ : Seed,
            ‖kernelPhi P k
              (O.response (batchDecision P u H) ξ - batchCenter P u H)‖ ^ 2
            ∂O.law ∂batchPastHistoryLaw P O u := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (batchPastHistoryLaw P O u) := by
    unfold batchPastHistoryLaw
    infer_instance
  letI : IsProbabilityMeasure (freshSeedLaw O P.n) :=
    freshSeedLaw_probability O P.n
  have herrorInt := kernelBatchErrorAtHistory_sq_integrable P O u k
  have hsourceInt := kernelSourceMoment_joint_integrable P O u k
  have hleftInt : Integrable
      (fun H : BatchHistory P d u =>
        ∫ seeds : Fin P.n → Seed,
          ‖kernelBatchErrorAtHistory P O u k (H, seeds)‖ ^ 2
          ∂freshSeedLaw O P.n)
      (batchPastHistoryLaw P O u) := herrorInt.integral_prod_left
  have hrightInt : Integrable
      (fun H : BatchHistory P d u =>
        (P.n : ℝ)⁻¹ * ∫ ξ : Seed,
          ‖kernelPhi P k
            (O.response (batchDecision P u H) ξ - batchCenter P u H)‖ ^ 2
          ∂O.law)
      (batchPastHistoryLaw P O u) :=
    hsourceInt.integral_prod_left.const_mul (P.n : ℝ)⁻¹
  rw [integral_prod _ herrorInt]
  calc
    (∫ H : BatchHistory P d u,
      ∫ seeds : Fin P.n → Seed,
        ‖kernelBatchErrorAtHistory P O u k (H, seeds)‖ ^ 2
        ∂freshSeedLaw O P.n ∂batchPastHistoryLaw P O u) ≤
        ∫ H : BatchHistory P d u,
          (P.n : ℝ)⁻¹ * ∫ ξ : Seed,
            ‖kernelPhi P k
              (O.response (batchDecision P u H) ξ - batchCenter P u H)‖ ^ 2
            ∂O.law ∂batchPastHistoryLaw P O u := by
              apply integral_mono hleftInt hrightInt
              intro H
              exact kernelBatch_secondMoment_le P O k
                (batchDecision P u H) (batchCenter P u H)
    _ = (P.n : ℝ)⁻¹ *
        ∫ H : BatchHistory P d u,
          ∫ ξ : Seed,
            ‖kernelPhi P k
              (O.response (batchDecision P u H) ξ - batchCenter P u H)‖ ^ 2
            ∂O.law ∂batchPastHistoryLaw P O u := by
              rw [integral_const_mul]

/-- The same second-moment bound for the actual complete private/seed path.
The right side is the expected single fresh response moment at the true
pre-batch decision and center. -/
theorem actualKernelBatchError_secondMoment_le {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ) :
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ‖actualKernelBatchError P O u k z‖ ^ 2
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) ≤
      (P.n : ℝ)⁻¹ *
        ∫ H : BatchHistory P d u,
          ∫ ξ : Seed,
            ‖kernelPhi P k
              (O.response (batchDecision P u H) ξ - batchCenter P u H)‖ ^ 2
            ∂O.law ∂batchPastHistoryLaw P O u := by
  let errSq : BatchHistory P d u × (Fin P.n → Seed) → ℝ :=
    fun z => ‖kernelBatchErrorAtHistory P O u k z‖ ^ 2
  let globalLaw := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw O (responseCount P))
  let targetLaw := (batchPastHistoryLaw P O u).prod (freshSeedLaw O P.n)
  have hmap := measurePreserving_actualHistory_currentBatch P O u
  have hmeas : StronglyMeasurable errSq :=
    ((measurable_kernelBatchErrorAtHistory P O u k).norm.pow_const 2).stronglyMeasurable
  have htransport :
      (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
        errSq (batchHistoryOfRun P O u z, batchSeedBlock P u z.2)
        ∂globalLaw) = (∫ y, errSq y ∂targetLaw) := by
    dsimp only [globalLaw, targetLaw]
    rw [← hmap.map_eq]
    exact (integral_map_of_stronglyMeasurable hmap.measurable hmeas).symm
  change (∫ z, errSq (batchHistoryOfRun P O u z,
    batchSeedBlock P u z.2) ∂globalLaw) ≤ _
  rw [htransport]
  exact kernelBatchErrorAtHistory_secondMoment_le P O u k

end

end HeavyTailedNoise.UpperK1
