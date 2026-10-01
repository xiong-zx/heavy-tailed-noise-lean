import HeavyTailedNoise.Upper.K1.RuntimeKernelNoise
import HeavyTailedNoise.Upper.K1.UniformOutput
import HeavyTailedNoise.Upper.K1.CoarseTrackerBoundaryProcess

/-!
The private output index selects a query after all responses have been
collected.  The complete transcript, each actual shared-source batch error,
and their runtime-kernel sum therefore depend only on the original oracle
seed tape.  This file transfers the product-law `L²` bound to the canonical
fixed-private-index tape used by the final estimator identity.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- A measurable nonnegative readout that ignores the private output index
has the same seed-only and private-times-seed integrals. -/
theorem lintegral_private_independent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (f : Fin P.T × (Fin (responseCount P) → Seed) → ENNReal)
    (hf : Measurable f)
    (r₀ : Fin P.T)
    (hind : ∀ r seeds, f (r, seeds) = f (r₀, seeds)) :
    (∫⁻ z, f z ∂((algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw O (responseCount P)))) =
    ∫⁻ seeds, f (r₀, seeds) ∂freshSeedLaw O (responseCount P) := by
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw O (responseCount P)) :=
    freshSeedLaw_probability O (responseCount P)
  rw [lintegral_prod _ hf.aemeasurable]
  simp_rw [hind]
  simp

/-- The history stores the private index in its first component, but its
entire pre-batch transcript is the same for every private output choice. -/
theorem batchHistoryOfRun_transcript_private_independent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u : Fin P.T)
    (r r' : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    (batchHistoryOfRun P O u (r, seeds)).2 =
      (batchHistoryOfRun P O u (r', seeds)).2 := by
  exact runTranscript_private_independent P O r r'
    (batchStart P u.val)
    (fun i : Fin (batchStart P u.val) =>
      seeds (i.castLE
        (batchStart_le_responseCount_of_le P u.val (Nat.le_of_lt u.isLt))))

theorem actualKernelBatchError_private_independent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ) (r r' : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) :
    actualKernelBatchError P O u k (r, seeds) =
      actualKernelBatchError P O u k (r', seeds) := by
  have htrans := batchHistoryOfRun_transcript_private_independent
    P O u r r' seeds
  unfold actualKernelBatchError kernelBatchErrorAtHistory
    batchDecision batchCenter
  simp only [htrans]

theorem runtimeKernelNoise_private_independent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (t : ℕ) (ht : t ≤ P.T) (r r' : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) :
    runtimeKernelNoise P O t ht (r, seeds) =
      runtimeKernelNoise P O t ht (r', seeds) := by
  unfold runtimeKernelNoise
  apply Finset.sum_congr rfl
  intro u hu
  exact actualKernelBatchError_private_independent P O
    (u.castLE ht) (t - 1 - u.val) r r' seeds

theorem runtimeKernelNoise_memLp_two
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ) (ht : t ≤ P.T) :
    MemLp (runtimeKernelNoise P O t ht) 2
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P))) := by
  change MemLp (fun z => ∑ u : Fin t,
    actualKernelBatchError P O (u.castLE ht) (t - 1 - u.val) z) 2 _
  apply memLp_finsetSum Finset.univ
  intro u hu
  exact actualKernelBatchError_memLp_two P O
    (u.castLE ht) (t - 1 - u.val)

/-- The original seed-only moment at the canonical fixed private anchor is
exactly the already controlled product-law moment. -/
theorem runtimeKernelNoise_sq_seed_integral_eq_joint
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (t : ℕ) (ht : t ≤ P.T) (r₀ : Fin P.T) :
    (∫ seeds : Fin (responseCount P) → Seed,
      ‖runtimeKernelNoise P O t ht (r₀, seeds)‖ ^ 2
      ∂freshSeedLaw O (responseCount P)) =
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ‖runtimeKernelNoise P O t ht z‖ ^ 2
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) := by
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw O (responseCount P)) :=
    freshSeedLaw_probability O (responseCount P)
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw O (responseCount P))
  let f : Fin P.T × (Fin (responseCount P) → Seed) → ℝ :=
    fun z => ‖runtimeKernelNoise P O t ht z‖ ^ 2
  have hmem := runtimeKernelNoise_memLp_two P O t ht
  have hInt : Integrable f μ := hmem.norm.integrable_sq
  have hf (r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
      f (r, seeds) = f (r₀, seeds) := by
    dsimp [f]
    rw [runtimeKernelNoise_private_independent P O t ht r r₀ seeds]
  change (∫ seeds, f (r₀, seeds) ∂freshSeedLaw O (responseCount P)) =
    ∫ z, f z ∂μ
  rw [integral_prod _ hInt]
  have hinner (r : Fin P.T) :
      (∫ seeds, f (r, seeds) ∂freshSeedLaw O (responseCount P)) =
      ∫ seeds, f (r₀, seeds) ∂freshSeedLaw O (responseCount P) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (hf r)
  simp_rw [hinner]
  simp

end

end HeavyTailedNoise.UpperK1
