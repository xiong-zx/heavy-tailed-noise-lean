import HeavyTailedNoise.Upper.K1.KernelBatch

/-!
Linearity of the complete shared-source kernel batch and source means. All
bands are transforms of the same returned vector; these identities retain
their cross terms when the resulting vector is used in a moment estimate.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem batchMean_kernelPsi {d b : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (x w : Point d) (seeds : Fin b → Seed) (k : ℕ) :
    upperResidualBatchMean O (kernelPsi P k) x w seeds =
      ∑ j : Fin P.J, (P.alpha j * (1 - P.alpha j) ^ k) •
        upperResidualBatchMean O (highBand P j) x w seeds := by
  unfold upperResidualBatchMean kernelPsi
  rw [Finset.sum_comm, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.smul_sum, smul_smul, smul_smul, mul_comm]

theorem sourceMean_kernelPsi {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (x w : Point d) (k : ℕ) :
    upperResidualSourceMean O (kernelPsi P k) x w =
      ∑ j : Fin P.J, (P.alpha j * (1 - P.alpha j) ^ k) •
        upperResidualSourceMean O (highBand P j) x w := by
  have hhigh (j : Fin P.J) : Integrable
      (fun ξ => highBand P j (O.response x ξ - w)) O.law :=
    upperResidualSource_integrable O (highBand P j)
      (measurable_highBand P j) (P.tau j.succ + P.tau j.castSucc)
      (highBand_norm_le P j) x w
  unfold upperResidualSourceMean kernelPsi
  rw [integral_finsetSum]
  · simp_rw [integral_smul]
  · intro j hj
    exact (hhigh j).smul (P.alpha j * (1 - P.alpha j) ^ k)

theorem batchMean_kernelPhi {d b : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (x w : Point d) (seeds : Fin b → Seed) (k : ℕ) :
    upperResidualBatchMean O (kernelPhi P k) x w seeds =
      (if k = 0 then upperResidualBatchMean O (lowBand P) x w seeds else 0) +
      ∑ j : Fin P.J, (P.alpha j * (1 - P.alpha j) ^ k) •
        upperResidualBatchMean O (highBand P j) x w seeds := by
  by_cases hk : k = 0
  · subst k
    have hadd : upperResidualBatchMean O (kernelPhi P 0) x w seeds =
        upperResidualBatchMean O (lowBand P) x w seeds +
          upperResidualBatchMean O (kernelPsi P 0) x w seeds := by
      simp only [upperResidualBatchMean, kernelPhi_zero,
        Finset.sum_add_distrib, smul_add]
    rw [hadd, batchMean_kernelPsi]
    simp
  · have hfun : kernelPhi (d := d) P k = kernelPsi P k := by
      funext z
      simp only [kernelPhi, hk, ite_false]
    rw [hfun, batchMean_kernelPsi]
    simp only [hk, ite_false, zero_add]

theorem sourceMean_kernelPhi {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (x w : Point d) (k : ℕ) :
    upperResidualSourceMean O (kernelPhi P k) x w =
      (if k = 0 then upperResidualSourceMean O (lowBand P) x w else 0) +
      ∑ j : Fin P.J, (P.alpha j * (1 - P.alpha j) ^ k) •
        upperResidualSourceMean O (highBand P j) x w := by
  by_cases hk : k = 0
  · subst k
    have hlow := upperResidualSource_integrable O (lowBand P)
      (measurable_lowBand P) (P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
      (fun z => upperClip_norm_le (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩) z) x w
    have hpsi := upperResidualSource_integrable O (kernelPsi P 0)
      (measurable_kernelPsi P 0)
      (∑ j : Fin P.J, |P.alpha j * (1 - P.alpha j) ^ 0| *
        (P.tau j.succ + P.tau j.castSucc))
      (kernelPsi_norm_le P 0) x w
    have hadd : upperResidualSourceMean O (kernelPhi P 0) x w =
        upperResidualSourceMean O (lowBand P) x w +
          upperResidualSourceMean O (kernelPsi P 0) x w := by
      change (∫ ξ, kernelPhi P 0 (O.response x ξ - w) ∂O.law) = _
      simp_rw [kernelPhi_zero]
      exact integral_add hlow hpsi
    rw [hadd, sourceMean_kernelPsi]
    simp
  · have hfun : kernelPhi (d := d) P k = kernelPsi P k := by
      funext z
      simp only [kernelPhi, hk, ite_false]
    rw [hfun, sourceMean_kernelPsi]
    simp only [hk, ite_false, zero_add]

theorem centered_kernelPhi_eq_bands {d b : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (x w : Point d) (seeds : Fin b → Seed) (k : ℕ) :
    upperResidualBatchMean O (kernelPhi P k) x w seeds -
        upperResidualSourceMean O (kernelPhi P k) x w =
      (if k = 0 then upperResidualBatchMean O (lowBand P) x w seeds -
        upperResidualSourceMean O (lowBand P) x w else 0) +
      ∑ j : Fin P.J, (P.alpha j * (1 - P.alpha j) ^ k) •
        (upperResidualBatchMean O (highBand P j) x w seeds -
          upperResidualSourceMean O (highBand P j) x w) := by
  rw [batchMean_kernelPhi, sourceMean_kernelPhi]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib]
  split_ifs <;> abel

end

end HeavyTailedNoise.UpperK1
