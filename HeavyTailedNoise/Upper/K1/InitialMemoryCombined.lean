import HeavyTailedNoise.Upper.K1.InitialMemoryActual
import HeavyTailedNoise.Upper.K1.KernelBatch
import HeavyTailedNoise.Upper.Foundations.InitialFreshBatchVariance

/-!
All initial high-band errors at a given runtime time are one transformed
fresh-sample error. The transform sums bands *inside* each seed coordinate;
the variance identity therefore retains arbitrary correlation among bands
of that same response.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- The coefficient on initial band `j` after `t` runtime updates. -/
def initialMemoryKernel {d : ℕ} (t : ℕ) (z : Point d) : Point d :=
  ∑ j : Fin P.J, (1 - P.alpha j) ^ t • highBand P j z

def initialMemoryKernelBound (t : ℕ) : ℝ :=
  ∑ j : Fin P.J,
    |(1 - P.alpha j) ^ t| *
      (P.tau j.succ + P.tau j.castSucc)

@[simp] theorem initialMemoryKernel_zero {d : ℕ} (t : ℕ) :
    initialMemoryKernel P t (0 : Point d) = 0 := by
  simp [initialMemoryKernel, highBand, upperShell]

theorem measurable_initialMemoryKernel {d : ℕ} (t : ℕ) :
    Measurable (initialMemoryKernel (d := d) P t) := by
  classical
  unfold initialMemoryKernel
  apply Finset.measurable_sum
  intro j hj
  exact (measurable_const : Measurable
    (fun _ : Point d => (1 - P.alpha j) ^ t)).smul
      (measurable_highBand P j)

theorem initialMemoryKernel_norm_le {d : ℕ} (t : ℕ) (z : Point d) :
    ‖initialMemoryKernel P t z‖ ≤ initialMemoryKernelBound P t := by
  unfold initialMemoryKernel initialMemoryKernelBound
  calc
    ‖∑ j : Fin P.J, (1 - P.alpha j) ^ t • highBand P j z‖ ≤
        ∑ j : Fin P.J,
          ‖(1 - P.alpha j) ^ t • highBand P j z‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin P.J,
          |(1 - P.alpha j) ^ t| *
            (P.tau j.succ + P.tau j.castSucc) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (highBand_norm_le P j z) (abs_nonneg _)

/-- Linearity of the finite empirical mean in a finite family of transforms.
This moves the band sum inside each seed; it is not an independence claim. -/
theorem initialMemoryKernel_batchMean {d m : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (t : ℕ) (x w : Point d) (seeds : Fin m → Seed) :
    (∑ j : Fin P.J, (1 - P.alpha j) ^ t •
      upperResidualBatchMean O (highBand P j) x w seeds) =
      upperResidualBatchMean O (initialMemoryKernel P t) x w seeds := by
  calc
    (∑ j : Fin P.J, (1 - P.alpha j) ^ t •
      upperResidualBatchMean O (highBand P j) x w seeds) =
        ∑ j : Fin P.J, ∑ i : Fin m,
          ((1 - P.alpha j) ^ t * (m : ℝ)⁻¹) •
            highBand P j (O.response x (seeds i) - w) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [upperResidualBatchMean, smul_smul, Finset.smul_sum]
    _ = ∑ i : Fin m, ∑ j : Fin P.J,
          ((m : ℝ)⁻¹ * (1 - P.alpha j) ^ t) •
            highBand P j (O.response x (seeds i) - w) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              rw [mul_comm]
    _ = upperResidualBatchMean O (initialMemoryKernel P t) x w seeds := by
          unfold upperResidualBatchMean initialMemoryKernel
          simp only [Finset.smul_sum, smul_smul]

/-- The matching source mean is linear in exactly the same within-seed
band sum. This connects the algebraic EMA source component to the centered
initialization error without replacing the sampled seed block. -/
theorem initialMemoryKernel_sourceMean {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (t : ℕ) (x w : Point d) :
    upperResidualSourceMean O (initialMemoryKernel P t) x w =
      ∑ j : Fin P.J, (1 - P.alpha j) ^ t •
        upperResidualSourceMean O (highBand P j) x w := by
  have hhigh (j : Fin P.J) : Integrable
      (fun ξ => highBand P j (O.response x ξ - w)) O.law :=
    upperResidualSource_integrable O (highBand P j)
      (measurable_highBand P j) (P.tau j.succ + P.tau j.castSucc)
      (highBand_norm_le P j) x w
  unfold upperResidualSourceMean initialMemoryKernel
  rw [integral_finsetSum]
  · simp_rw [integral_smul]
  · intro j hj
    exact (hhigh j).smul ((1 - P.alpha j) ^ t)

/-- The actual decaying initialization contribution in the high-band EMA.
No second state or alternative run is introduced. -/
def actualInitialMemoryContribution {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ) : Point d :=
  ∑ j : Fin P.J,
    (1 - P.alpha j) ^ t • actualRuntimeMemory P O seeds j 0

theorem actualInitialMemoryContribution_zero_of_no_initial
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ)
    (hzero : initialResponses P = 0) :
    actualInitialMemoryContribution P O seeds t = 0 := by
  unfold actualInitialMemoryContribution
  apply Finset.sum_eq_zero
  intro j hj
  rw [actualRuntimeMemory_zero_of_no_initial P O seeds j hzero]
  simp

theorem actualInitialMemoryContribution_eq_batchMean
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ)
    (hpos : 0 < initialResponses P) :
    actualInitialMemoryContribution P O seeds t =
      upperResidualBatchMean O (initialMemoryKernel P t) 0
        (O.response 0 (seeds ⟨0, responseCount_pos P⟩))
        (initialSeedBlock P seeds) := by
  unfold actualInitialMemoryContribution
  calc
    (∑ j : Fin P.J,
      (1 - P.alpha j) ^ t • actualRuntimeMemory P O seeds j 0) =
        ∑ j : Fin P.J, (1 - P.alpha j) ^ t •
          upperResidualBatchMean O (highBand P j) 0
            (O.response 0 (seeds ⟨0, responseCount_pos P⟩))
            (initialSeedBlock P seeds) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [actualRuntimeMemory_zero_eq_initialBatch P O seeds j hpos]
    _ = _ := initialMemoryKernel_batchMean P O t 0 _ _

/-- Exact fixed-center L² identity for the complete high-band initialization
transform. The right side is the variance of its *combined* one-seed vector. -/
theorem initialMemoryKernel_batch_secondMoment {d m : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (t : ℕ) (w : Point d) (hm : 0 < m) :
    (∫ seeds : Fin m → Seed,
      ‖upperResidualBatchMean O (initialMemoryKernel P t) 0 w seeds -
        upperResidualSourceMean O (initialMemoryKernel P t) 0 w‖ ^ 2
      ∂freshSeedLaw O m) =
      (m : ℝ)⁻¹ * ∫ ξ : Seed,
        ‖initialMemoryKernel P t (O.response 0 ξ - w) -
          upperResidualSourceMean O (initialMemoryKernel P t) 0 w‖ ^ 2
        ∂O.law := by
  exact upperResidualBatchMean_secondMoment_eq_source O
    (initialMemoryKernel P t) (measurable_initialMemoryKernel P t)
    (initialMemoryKernelBound P t)
    (initialMemoryKernel_norm_le P t) 0 w hm

end

end HeavyTailedNoise.UpperK1
