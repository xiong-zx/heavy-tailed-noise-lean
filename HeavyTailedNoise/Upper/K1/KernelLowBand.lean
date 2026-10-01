import HeavyTailedNoise.Upper.K1.SharedKernel

/-!
The lag-zero low core of the literal shared-batch kernel. The two-vector
square bound controls its cross term with the high-band sum; no independence
between transforms of one response is asserted.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

theorem norm_add_sq_le_twice {d : ℕ} (u v : Point d) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm := norm_add_le u v
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- Across any finite lag horizon, the low-band term incurs only one extra
factor two and one lag-zero cross term. -/
theorem kernelPhi_sq_sum_le_low_add_high {q : ℝ} (P : Schedule q)
    {d : ℕ} (T : ℕ) (z : Point d) :
    (∑ k ∈ Finset.range T, ‖kernelPhi P k z‖ ^ 2) ≤
      2 * ‖lowBand P z‖ ^ 2 +
        2 * ∑ k ∈ Finset.range T, ‖kernelPsi P k z‖ ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
      simp only [Finset.sum_range_succ]
      by_cases hT : T = 0
      · subst T
        simpa [kernelPhi_zero] using
          norm_add_sq_le_twice (lowBand P z) (kernelPsi P 0 z)
      · have hphi : kernelPhi P T z = kernelPsi P T z := by
          simp [kernelPhi, hT]
        rw [hphi]
        have hnonneg : 0 ≤ ‖kernelPsi P T z‖ ^ 2 := sq_nonneg _
        nlinarith

end

end HeavyTailedNoise.UpperK1
