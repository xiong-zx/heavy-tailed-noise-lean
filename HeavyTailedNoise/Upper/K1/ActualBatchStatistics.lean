import HeavyTailedNoise.Upper.K1.BatchPastProduct
import HeavyTailedNoise.Upper.K1.KernelBatchProbability

/-!
Kernel-batch statistics on the actual complete private/seed path. A runtime
batch uses the original whole-response transform `kernelPhi`; the path map
pushes the global law to the exact pre-batch-history × fresh-batch product law.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Centered shared-`Φ_k` batch error on the proved product history space. -/
def kernelBatchErrorAtHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ)
    (z : BatchHistory P d u × (Fin P.n → Seed)) : Point d :=
  upperResidualBatchMean O (kernelPhi P k)
      (batchDecision P u z.1) (batchCenter P u z.1) z.2 -
    upperResidualSourceMean O (kernelPhi P k)
      (batchDecision P u z.1) (batchCenter P u z.1)

/-- The same error evaluated on one actual full private/seed path. -/
def actualKernelBatchError {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) : Point d :=
  kernelBatchErrorAtHistory P O u k
    (batchHistoryOfRun P O u z, batchSeedBlock P u z.2)

theorem measurable_kernelBatchErrorAtHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ) :
    Measurable (kernelBatchErrorAtHistory P O u k) := by
  exact (measurable_upperResidualBatchMean O (kernelPhi P k)
    (measurable_kernelPhi P k)
    (batchDecision P u) (batchCenter P u)
    (measurable_batchDecision P u) (measurable_batchCenter P u)).sub
      ((measurable_upperResidualSourceMean O (kernelPhi P k)
        (measurable_kernelPhi P k)
        (batchDecision P u) (batchCenter P u)
        (measurable_batchDecision P u) (measurable_batchCenter P u)).comp
          measurable_fst)

theorem integrable_kernelBatchErrorAtHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ) :
    Integrable (kernelBatchErrorAtHistory P O u k)
      ((batchPastHistoryLaw P O u).prod (freshSeedLaw O P.n)) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (batchPastHistoryLaw P O u) := by
    unfold batchPastHistoryLaw
    infer_instance
  exact (upperResidualBatchMean_joint_integrable O (kernelPhi P k)
      (measurable_kernelPhi P k) (kernelPhiBound P k)
      (fun z => kernelPhi_norm_le P k z)
      (batchPastHistoryLaw P O u) (batchDecision P u) (batchCenter P u)
      (measurable_batchDecision P u) (measurable_batchCenter P u)).sub
    (upperResidualSourceMean_joint_integrable O (kernelPhi P k)
      (measurable_kernelPhi P k) (kernelPhiBound P k)
      (fun z => kernelPhi_norm_le P k z)
      (batchPastHistoryLaw P O u) (batchDecision P u) (batchCenter P u)
      (measurable_batchDecision P u) (measurable_batchCenter P u))

/-- The actual complete-seed-path batch error has zero unconditioned mean.
No estimator source is replaced by an idealized oracle: the equality follows
from the measure-preserving actual path map. -/
theorem actualKernelBatchError_integral_zero {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ) :
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      actualKernelBatchError P O u k z
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) = 0 := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (batchPastHistoryLaw P O u) := by
    unfold batchPastHistoryLaw
    infer_instance
  letI : IsProbabilityMeasure (freshSeedLaw O P.n) :=
    freshSeedLaw_probability O P.n
  let err := kernelBatchErrorAtHistory P O u k
  let targetLaw := (batchPastHistoryLaw P O u).prod (freshSeedLaw O P.n)
  let globalLaw := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw O (responseCount P))
  have hInt : Integrable err targetLaw :=
    integrable_kernelBatchErrorAtHistory P O u k
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
  have hproduct : (∫ z, err z ∂targetLaw) = 0 := by
    rw [integral_prod _ hInt]
    simp_rw [hfixed]
    simp
  have hmap := measurePreserving_actualHistory_currentBatch P O u
  have htransport :
      (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
        err (batchHistoryOfRun P O u z, batchSeedBlock P u z.2)
        ∂globalLaw) = (∫ y, err y ∂targetLaw) := by
    dsimp only [targetLaw, globalLaw]
    rw [← hmap.map_eq]
    exact (integral_map_of_stronglyMeasurable hmap.measurable
      (measurable_kernelBatchErrorAtHistory P O u k).stronglyMeasurable).symm
  change (∫ z, err (batchHistoryOfRun P O u z,
    batchSeedBlock P u z.2) ∂globalLaw) = 0
  exact htransport.trans hproduct

end

end HeavyTailedNoise.UpperK1
