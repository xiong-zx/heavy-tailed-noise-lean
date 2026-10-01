import HeavyTailedNoise.Upper.K1.KernelMinkowski

/-!
Finite-dimensional Minkowski bound for the complete same-source EMA band
sum.  Each band's lag sequence is one Euclidean vector; `norm_sum_le` bounds
their sum without asserting independence or dropping cross terms.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

private theorem sum_fin_nat_eq_range (T : ℕ) (f : ℕ → ℝ) :
    (∑ k : Fin T, f (k : ℕ)) = ∑ k ∈ Finset.range T, f k := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [Finset.mem_range.mp hk]

/-- The first `T` weights of one EMA band, represented as a Euclidean vector. -/
def emaLagVector (α : ℝ) (T : ℕ) : Point T :=
  WithLp.toLp 2 (fun k : Fin T => α * (1 - α) ^ (k : ℕ))

theorem emaLagVector_norm_sq_le {α : ℝ}
    (hα : 0 < α) (hαle : α ≤ 1) (T : ℕ) :
    ‖emaLagVector α T‖ ^ 2 ≤ α := by
  calc
    ‖emaLagVector α T‖ ^ 2 =
        ∑ k : Fin T, (α * (1 - α) ^ (k : ℕ)) ^ 2 := by
          simpa [emaLagVector] using
            (EuclideanSpace.real_norm_sq_eq (emaLagVector α T))
    _ = ∑ k ∈ Finset.range T, (α * (1 - α) ^ k) ^ 2 :=
      sum_fin_nat_eq_range T (fun k => (α * (1 - α) ^ k) ^ 2)
    _ ≤ α := ema_band_weight_sq_sum_le hα hαle T

theorem emaLagVector_norm_le_sqrt {α : ℝ}
    (hα : 0 < α) (hαle : α ≤ 1) (T : ℕ) :
    ‖emaLagVector α T‖ ≤ Real.sqrt α := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa [Real.sq_sqrt hα.le] using emaLagVector_norm_sq_le hα hαle T

/-- Finite-horizon shared-source square bound. All bands are summed inside
each lag before squaring. -/
theorem ema_band_sum_sq_le
    {J T : ℕ} (α d : Fin J → ℝ)
    (hα : ∀ j, 0 < α j) (hαle : ∀ j, α j ≤ 1)
    (hd : ∀ j, 0 ≤ d j) :
    (∑ k : Fin T,
      (∑ j : Fin J, α j * (1 - α j) ^ (k : ℕ) * d j) ^ 2) ≤
      (∑ j : Fin J, Real.sqrt (α j) * d j) ^ 2 := by
  let v : Point T := ∑ j : Fin J, d j • emaLagVector (α j) T
  have hcoord (k : Fin T) :
      v k = ∑ j : Fin J, α j * (1 - α j) ^ (k : ℕ) * d j := by
    simp [v, emaLagVector, Finset.sum_apply, mul_comm, mul_left_comm, mul_assoc]
  have hnorm : ‖v‖ ≤ ∑ j : Fin J, Real.sqrt (α j) * d j := by
    calc
      ‖v‖ ≤ ∑ j : Fin J, ‖d j • emaLagVector (α j) T‖ := by
        dsimp [v]
        exact norm_sum_le _ _
      _ ≤ ∑ j : Fin J, Real.sqrt (α j) * d j := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd j)]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left
            (emaLagVector_norm_le_sqrt (hα j) (hαle j) T) (hd j)
  have hright : 0 ≤ ∑ j : Fin J, Real.sqrt (α j) * d j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Real.sqrt_nonneg _) (hd j))
  calc
    (∑ k : Fin T,
      (∑ j : Fin J, α j * (1 - α j) ^ (k : ℕ) * d j) ^ 2) =
        ‖v‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp_rw [hcoord]
    _ ≤ (∑ j : Fin J, Real.sqrt (α j) * d j) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hright).mpr hnorm

/-- The same statement with manuscript-style natural lag indices. -/
theorem ema_band_sum_sq_range_le
    {J T : ℕ} (α d : Fin J → ℝ)
    (hα : ∀ j, 0 < α j) (hαle : ∀ j, α j ≤ 1)
    (hd : ∀ j, 0 ≤ d j) :
    (∑ k ∈ Finset.range T,
      (∑ j : Fin J, α j * (1 - α j) ^ k * d j) ^ 2) ≤
      (∑ j : Fin J, Real.sqrt (α j) * d j) ^ 2 := by
  calc
    (∑ k ∈ Finset.range T,
      (∑ j : Fin J, α j * (1 - α j) ^ k * d j) ^ 2) =
        ∑ k : Fin T,
          (∑ j : Fin J, α j * (1 - α j) ^ (k : ℕ) * d j) ^ 2 :=
            (sum_fin_nat_eq_range T
              (fun k => (∑ j : Fin J, α j * (1 - α j) ^ k * d j) ^ 2)).symm
    _ ≤ (∑ j : Fin J, Real.sqrt (α j) * d j) ^ 2 :=
      ema_band_sum_sq_le α d hα hαle hd

end

end HeavyTailedNoise.UpperK1
