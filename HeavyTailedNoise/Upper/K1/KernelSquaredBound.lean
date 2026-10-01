import HeavyTailedNoise.Upper.K1.KernelMinkowskiVector
import HeavyTailedNoise.Upper.K1.KernelShellSupport
import HeavyTailedNoise.Upper.K1.KernelActiveDyadic

/-!
Conservative finite-lag bound for one shared-source high-band kernel.  The
square is taken after summing all bands at each lag; no independence among
bands or separate per-band variance calculation is used.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- A single lag's complete high-band vector is bounded by the scalar sum of
its band norms, with the nonnegative EMA weights left intact. -/
theorem kernelPsi_norm_le_weighted_bands
    {d : ℕ} (k : ℕ) (z : Point d)
    (hα : ∀ j : Fin P.J, 0 < P.alpha j)
    (hαle : ∀ j : Fin P.J, P.alpha j ≤ 1) :
    ‖kernelPsi P k z‖ ≤
      ∑ j : Fin P.J,
        P.alpha j * (1 - P.alpha j) ^ k * ‖highBand P j z‖ := by
  have hcoeff (j : Fin P.J) :
      0 ≤ P.alpha j * (1 - P.alpha j) ^ k :=
    mul_nonneg (hα j).le (pow_nonneg (sub_nonneg.mpr (hαle j)) _)
  unfold kernelPsi
  calc
    ‖∑ j : Fin P.J,
      (P.alpha j * (1 - P.alpha j) ^ k) • highBand P j z‖ ≤
        ∑ j : Fin P.J,
          ‖(P.alpha j * (1 - P.alpha j) ^ k) • highBand P j z‖ :=
            norm_sum_le _ _
    _ = ∑ j : Fin P.J,
        P.alpha j * (1 - P.alpha j) ^ k * ‖highBand P j z‖ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hcoeff j)]

/-- Minkowski's inequality across the band lag vectors.  All same-response
cross-scale terms remain within the complete `kernelPsi` norm. -/
theorem kernelPsi_sq_sum_le_weighted_bands
    {d T : ℕ} (z : Point d)
    (hα : ∀ j : Fin P.J, 0 < P.alpha j)
    (hαle : ∀ j : Fin P.J, P.alpha j ≤ 1) :
    (∑ k ∈ Finset.range T, ‖kernelPsi P k z‖ ^ 2) ≤
      (∑ j : Fin P.J,
        Real.sqrt (P.alpha j) * ‖highBand P j z‖) ^ 2 := by
  have hscalar_nonneg (k : ℕ) :
      0 ≤ ∑ j : Fin P.J,
        P.alpha j * (1 - P.alpha j) ^ k * ‖highBand P j z‖ :=
    Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (hα j).le
        (pow_nonneg (sub_nonneg.mpr (hαle j)) _)) (norm_nonneg _))
  calc
    (∑ k ∈ Finset.range T, ‖kernelPsi P k z‖ ^ 2) ≤
        ∑ k ∈ Finset.range T,
          (∑ j : Fin P.J,
            P.alpha j * (1 - P.alpha j) ^ k * ‖highBand P j z‖) ^ 2 := by
              apply Finset.sum_le_sum
              intro k hk
              exact (sq_le_sq₀ (norm_nonneg _) (hscalar_nonneg k)).mpr
                (kernelPsi_norm_le_weighted_bands P k z hα hαle)
    _ ≤ (∑ j : Fin P.J,
        Real.sqrt (P.alpha j) * ‖highBand P j z‖) ^ 2 :=
      ema_band_sum_sq_range_le P.alpha (fun j => ‖highBand P j z‖)
        hα hαle (fun j => norm_nonneg _)

end

end HeavyTailedNoise.UpperK1
