import HeavyTailedNoise.Upper.K1.KernelMeanLinearity
import HeavyTailedNoise.Upper.K1.KernelTemporalAlgebra
import HeavyTailedNoise.Upper.K1.ActualEMACenteredDecomposition
import HeavyTailedNoise.Upper.K1.RuntimeKernelNoise

/-!
The proved complete runtime kernel noise is exactly the low-band current
batch error plus all high-band finite EMA noise terms on the same global
seed tape. This identity does not replace a shared batch by separate bands.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

irreducible_def actualLowBatchNoise {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ) : Point d :=
  if ht : t < P.T then
    let u : Fin P.T := ⟨t, ht⟩
    let H := batchHistoryOfRun P O u ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
    upperResidualBatchMean O (lowBand P)
        (batchDecision P u H) (batchCenter P u H) (batchSeedBlock P u seeds) -
      upperResidualSourceMean O (lowBand P)
        (batchDecision P u H) (batchCenter P u H)
  else 0

theorem actualKernelBatchError_eq_bandNoise {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) (k : ℕ) :
    actualKernelBatchError P O u k ((⟨0, P.T_pos⟩ : Fin P.T), seeds) =
      (if k = 0 then actualLowBatchNoise P O seeds u.val else 0) +
      ∑ j : Fin P.J, (P.alpha j * (1 - P.alpha j) ^ k) •
        actualBandBatchNoise P O seeds j u.val := by
  let H := batchHistoryOfRun P O u ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
  have h := centered_kernelPhi_eq_bands P O
    (batchDecision P u H) (batchCenter P u H) (batchSeedBlock P u seeds) k
  change upperResidualBatchMean O (kernelPhi P k)
      (batchDecision P u H) (batchCenter P u H) (batchSeedBlock P u seeds) -
    upperResidualSourceMean O (kernelPhi P k)
      (batchDecision P u H) (batchCenter P u H) = _
  simpa only [actualLowBatchNoise, actualBandBatchNoise,
    actualBandBatchMean, actualBandSourceMean, dif_pos u.isLt] using h

theorem runtimeKernelNoise_eq_low_and_bandNoise {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ)
    (ht : t ≤ P.T) (htpos : 0 < t) :
    runtimeKernelNoise P O t ht ((⟨0, P.T_pos⟩ : Fin P.T), seeds) =
      actualLowBatchNoise P O seeds (t - 1) +
      ∑ j : Fin P.J,
        bandCenteredNoise P j (actualBandBatchNoise P O seeds j) t := by
  let f : ℕ → Point d := fun u =>
    (if t - 1 - u = 0 then actualLowBatchNoise P O seeds u else 0) +
      ∑ j : Fin P.J, (P.alpha j * (1 - P.alpha j) ^ (t - 1 - u)) •
        actualBandBatchNoise P O seeds j u
  calc
    runtimeKernelNoise P O t ht ((⟨0, P.T_pos⟩ : Fin P.T), seeds) =
        ∑ u : Fin t, f u.val := by
      unfold runtimeKernelNoise
      apply Finset.sum_congr rfl
      intro u hu
      exact actualKernelBatchError_eq_bandNoise P O seeds
        (u.castLE ht) (t - 1 - u.val)
    _ = ∑ u ∈ Finset.range t, f u := Fin.sum_univ_eq_sum_range f t
    _ = actualLowBatchNoise P O seeds (t - 1) +
        ∑ j : Fin P.J,
          bandCenteredNoise P j (actualBandBatchNoise P O seeds j) t :=
      finite_kernel_sum_eq_low_and_bandNoise P
        (actualLowBatchNoise P O seeds) (actualBandBatchNoise P O seeds) t htpos

end

end HeavyTailedNoise.UpperK1
