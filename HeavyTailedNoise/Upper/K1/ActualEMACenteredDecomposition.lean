import HeavyTailedNoise.Upper.K1.EMACenteredAlgebra
import HeavyTailedNoise.Upper.K1.CoarseTrackerActualMemoryProcess

/-!
The exact mean/initial-error/runtime-noise decomposition of the existing
algorithm's high memory on its one canonical global seed tape. Source means
are analysis quantities; the algorithm observes only returned gradients.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

irreducible_def actualBandSourceMean {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (j : Fin P.J)
    (t : ℕ) : Point d :=
  if ht : t < P.T then
    let u : Fin P.T := ⟨t, ht⟩
    let H := batchHistoryOfRun P O u ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
    upperResidualSourceMean O (highBand P j)
      (batchDecision P u H) (batchCenter P u H)
  else 0

irreducible_def actualBandBatchMean {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (j : Fin P.J)
    (t : ℕ) : Point d :=
  if ht : t < P.T then
    let u : Fin P.T := ⟨t, ht⟩
    let H := batchHistoryOfRun P O u ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
    upperResidualBatchMean O (highBand P j)
      (batchDecision P u H) (batchCenter P u H) (batchSeedBlock P u seeds)
  else 0

def actualBandBatchNoise {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (j : Fin P.J)
    (t : ℕ) : Point d :=
  actualBandBatchMean P O seeds j t - actualBandSourceMean P O seeds j t

theorem actualRuntimeMemory_recursion_with_batchMean
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (seeds : Fin (responseCount P) → Seed)
    (j : Fin P.J) (t : ℕ) (ht : t < P.T) :
    actualRuntimeMemory P O seeds j (t + 1) =
      (1 - P.alpha j) • actualRuntimeMemory P O seeds j t +
        P.alpha j • actualBandBatchMean P O seeds j t := by
  rw [actualBandBatchMean]
  simp only [dif_pos ht]
  exact actualRuntimeMemory_succ P O seeds j t ht

theorem actualRuntimeMemory_eq_mean_initial_noise
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (seeds : Fin (responseCount P) → Seed)
    (j : Fin P.J) (t : ℕ) (ht : t ≤ P.T) :
    actualRuntimeMemory P O seeds j t =
      bandMeanComponent P j (fun v => actualBandSourceMean P O seeds j (v - 1)) t +
      (1 - P.alpha j) ^ t •
        (actualRuntimeMemory P O seeds j 0 - actualBandSourceMean P O seeds j 0) +
      bandCenteredNoise P j (actualBandBatchNoise P O seeds j) t := by
  have hrec : ∀ u < P.T,
      actualRuntimeMemory P O seeds j (u + 1) =
        (1 - P.alpha j) • actualRuntimeMemory P O seeds j u +
          P.alpha j • actualBandBatchMean P O seeds j u :=
    fun u hu => actualRuntimeMemory_recursion_with_batchMean P O seeds j u hu
  have h := ema_recursion_eq_mean_initial_noise P j
    (actualRuntimeMemory P O seeds j) (actualBandBatchMean P O seeds j)
    (fun v => actualBandSourceMean P O seeds j (v - 1)) P.T hrec t ht
  have hnoise : actualBandBatchNoise P O seeds j =
      (fun u => actualBandBatchMean P O seeds j u -
        actualBandSourceMean P O seeds j u) := rfl
  rw [hnoise]
  simpa only [Nat.add_sub_cancel, Nat.sub_self] using h

end

end HeavyTailedNoise.UpperK1
