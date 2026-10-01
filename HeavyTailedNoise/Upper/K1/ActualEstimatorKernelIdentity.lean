import HeavyTailedNoise.Upper.K1.ActualKernelBandIdentity
import HeavyTailedNoise.Upper.K1.StationarityActualEstimatorFormula
import HeavyTailedNoise.Upper.K1.StationarityActualErrorSplit
import HeavyTailedNoise.Upper.K1.EMAAggregateLag

/-!
The actual completed estimator minus its terminal-clipped source mean is
exactly runtime shared-kernel noise, decaying initialization sample error
and source-mean EMA lag. All terms use the original global seed tape.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

def actualInitialMemoryError {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ) : Point d :=
  ∑ j : Fin P.J, (1 - P.alpha j) ^ t •
    (actualRuntimeMemory P O seeds j 0 - actualBandSourceMean P O seeds j 0)

def actualMeanLag {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ) : Point d :=
  aggregateMeanLag P
    (fun j v => actualBandSourceMean P O seeds j (v - 1)) t

theorem actualEstimate_eq_lowBatch_and_memory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) :
    let H := batchHistoryOfRun P O u ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
    actualRuntimeEstimate P O seeds u.val =
      batchCenter P u H + upperResidualBatchMean O (lowBand P)
        (batchDecision P u H) (batchCenter P u H) (batchSeedBlock P u seeds) +
      ∑ j : Fin P.J, actualRuntimeMemory P O seeds j (u.val + 1) := by
  dsimp only
  let z : Fin P.T × (Fin (responseCount P) → Seed) := (⟨0, P.T_pos⟩, seeds)
  let H := batchHistoryOfRun P O u z
  have hpre := boundaryTranscript_eq_batchHistory P O u z
  have hmemory (j : Fin P.J) :
      actualRuntimeMemory P O seeds j u.val =
        memories P (stateAt P (batchStart P u.val) H.2) j := by
    simp only [actualRuntimeMemory, dif_pos (Nat.le_of_lt u.isLt)]
    rw [hpre]
  have hformula := actualRuntimeEstimate_eq_lowBatch_add_highEMA P O seeds u
  calc
    actualRuntimeEstimate P O seeds u.val =
        batchCenter P u H + upperResidualBatchMean O (lowBand P)
          (batchDecision P u H) (batchCenter P u H) (batchSeedBlock P u seeds) +
        ∑ j : Fin P.J,
          ((1 - P.alpha j) • memories P (stateAt P (batchStart P u.val) H.2) j +
            P.alpha j • upperResidualBatchMean O (highBand P j)
              (batchDecision P u H) (batchCenter P u H) (batchSeedBlock P u seeds)) :=
      hformula
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hrec := actualRuntimeMemory_succ P O seeds j u.val u.isLt
      rw [hmemory j] at hrec
      exact hrec.symm

private theorem centered_memory_sum {d J : ℕ}
    (w Lb Ls : Point d) (M Q A E S : Fin J → Point d)
    (hM : ∀ j, M j = Q j + A j + E j) :
    (w + Lb + ∑ j, M j) - (w + Ls + ∑ j, S j) =
      (Lb - Ls + ∑ j, E j) + (∑ j, A j) + ∑ j, (Q j - S j) := by
  have hsum : (∑ j, M j) =
      (∑ j, Q j) + (∑ j, A j) + ∑ j, E j := by
    simp_rw [hM]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsum, Finset.sum_sub_distrib]
  abel

theorem actualEstimator_centered_eq_kernel_initial_lag
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (seeds : Fin (responseCount P) → Seed)
    (u : Fin P.T) :
    actualRuntimeEstimate P O seeds u.val - actualClippedSourceEstimate P O seeds u =
      runtimeKernelNoise P O (u.val + 1) (Nat.succ_le_iff.mpr u.isLt)
        ((⟨0, P.T_pos⟩ : Fin P.T), seeds) +
      actualInitialMemoryError P O seeds (u.val + 1) +
      actualMeanLag P O seeds u.val := by
  let H := batchHistoryOfRun P O u ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
  have hsource (j : Fin P.J) :
      actualBandSourceMean P O seeds j u.val =
        upperResidualSourceMean O (highBand P j)
          (batchDecision P u H) (batchCenter P u H) := by
    rw [actualBandSourceMean]
    simp only [dif_pos u.isLt]
    rfl
  have hclip : actualClippedSourceEstimate P O seeds u =
      batchCenter P u H + upperResidualSourceMean O (lowBand P)
        (batchDecision P u H) (batchCenter P u H) +
        ∑ j : Fin P.J, actualBandSourceMean P O seeds j u.val := by
    rw [actualClippedSourceEstimate_eq_bandMeans]
    simp_rw [hsource]
    abel
  have hmemory := centered_memory_sum
    (batchCenter P u H)
    (upperResidualBatchMean O (lowBand P)
      (batchDecision P u H) (batchCenter P u H) (batchSeedBlock P u seeds))
    (upperResidualSourceMean O (lowBand P) (batchDecision P u H) (batchCenter P u H))
    (fun j => actualRuntimeMemory P O seeds j (u.val + 1))
    (fun j => bandMeanComponent P j
      (fun v => actualBandSourceMean P O seeds j (v - 1)) (u.val + 1))
    (fun j => (1 - P.alpha j) ^ (u.val + 1) •
      (actualRuntimeMemory P O seeds j 0 - actualBandSourceMean P O seeds j 0))
    (fun j => bandCenteredNoise P j (actualBandBatchNoise P O seeds j) (u.val + 1))
    (fun j => actualBandSourceMean P O seeds j u.val)
    (fun j => actualRuntimeMemory_eq_mean_initial_noise P O seeds j
      (u.val + 1) (Nat.succ_le_iff.mpr u.isLt))
  rw [actualEstimate_eq_lowBatch_and_memory, hclip]
  rw [runtimeKernelNoise_eq_low_and_bandNoise P O seeds
    (u.val + 1) (Nat.succ_le_iff.mpr u.isLt) (Nat.zero_lt_succ _)]
  simp only [Nat.add_sub_cancel, actualInitialMemoryError, actualMeanLag, aggregateMeanLag]
  rw [actualLowBatchNoise]
  simp only [dif_pos u.isLt]
  exact hmemory

end

end HeavyTailedNoise.UpperK1
