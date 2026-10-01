import HeavyTailedNoise.Upper.K1.KernelGeometric

/-!
Conservative shared-batch kernel route. The finite-lag ℓ² norm is bounded by
the sum of each band's ℓ² norm (Minkowski), so all same-sample cross terms are
retained and bounded without any independence assertion. Constants are wider
than the manuscript's exact double-scale coefficient but have the same rate.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- One EMA band's finite-time squared weights have total mass at most α.
This includes α=1, where the only nonzero weight is at lag zero. -/
theorem ema_band_weight_sq_sum_le {α : ℝ}
    (hα : 0 < α) (hαle : α ≤ 1) (T : ℕ) :
    (∑ k ∈ Finset.range T, (α * (1 - α) ^ k) ^ 2) ≤ α := by
  let b : ℝ := 1 - α
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hterm (k : ℕ) : (α * b ^ k) ^ 2 ≤ α ^ 2 * b ^ k := by
    have hbk0 : 0 ≤ b ^ k := pow_nonneg hb0 _
    have hbk1 : b ^ k ≤ 1 := pow_le_one₀ hb0 hb1.le
    calc
      (α * b ^ k) ^ 2 = α ^ 2 * (b ^ k) ^ 2 := by ring
      _ ≤ α ^ 2 * b ^ k :=
        mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg α)
  calc
    (∑ k ∈ Finset.range T, (α * (1 - α) ^ k) ^ 2) ≤
        ∑ k ∈ Finset.range T, α ^ 2 * b ^ k := by
          apply Finset.sum_le_sum
          intro k hk
          simpa only [b] using hterm k
    _ = α ^ 2 * (∑ k ∈ Finset.range T, b ^ k) := by
          rw [Finset.mul_sum]
    _ ≤ α ^ 2 * (1 - b)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (geometric_partial_le_inv hb0 hb1 T) (sq_nonneg α)
    _ = α := by
      dsimp [b]
      field_simp [ne_of_gt hα] <;> ring

end

end HeavyTailedNoise.UpperK1
