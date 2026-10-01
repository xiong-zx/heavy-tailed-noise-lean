import HeavyTailedNoise.Upper.K1.EMALagAlgebra

/-!
Finite high-band mean lag in manuscript equation `ema-19`. The statements
sum the already proved one-band identity and use only finite sums and the
triangle inequality. No independence between bands is asserted.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- `t` is one less than the manuscript's current positive time. -/
def aggregateMeanLag {d : ℕ} (μ : Fin P.J → ℕ → Point d) (t : ℕ) : Point d :=
  ∑ j : Fin P.J,
    (bandMeanComponent P j (μ j) (t + 1) - μ j (t + 1))

theorem aggregateMeanLag_eq_source_moves {d : ℕ}
    (μ : Fin P.J → ℕ → Point d) (t : ℕ) :
    aggregateMeanLag P μ t =
      -∑ u ∈ Finset.range t, ∑ j : Fin P.J,
        (1 - P.alpha j) ^ (t - u) •
          (μ j (u + 2) - μ j (u + 1)) := by
  calc
    aggregateMeanLag P μ t =
        ∑ j : Fin P.J, -emaLagSum (1 - P.alpha j) (μ j) t := by
          unfold aggregateMeanLag
          apply Finset.sum_congr rfl
          intro j hj
          exact bandMeanComponent_sub_source P j (μ j) t
    _ = -∑ j : Fin P.J, emaLagSum (1 - P.alpha j) (μ j) t := by
      rw [Finset.sum_neg_distrib]
    _ = -∑ u ∈ Finset.range t, ∑ j : Fin P.J,
          (1 - P.alpha j) ^ (t - u) •
            (μ j (u + 2) - μ j (u + 1)) := by
      simp_rw [emaLagSum]
      rw [Finset.sum_comm]

/-- Pointwise deterministic triangle bound before any geometric-weight or
expected-drift estimate. It keeps absolute retention weights, so it is valid
even before the physical schedule proves `0 ≤ 1-α_j`. -/
theorem aggregateMeanLag_norm_le {d : ℕ}
    (μ : Fin P.J → ℕ → Point d) (t : ℕ) :
    ‖aggregateMeanLag P μ t‖ ≤
      ∑ u ∈ Finset.range t, ∑ j : Fin P.J,
        |1 - P.alpha j| ^ (t - u) *
          ‖μ j (u + 2) - μ j (u + 1)‖ := by
  rw [aggregateMeanLag_eq_source_moves, norm_neg]
  calc
    ‖∑ u ∈ Finset.range t, ∑ j : Fin P.J,
        (1 - P.alpha j) ^ (t - u) •
          (μ j (u + 2) - μ j (u + 1))‖ ≤
      ∑ u ∈ Finset.range t, ‖∑ j : Fin P.J,
        (1 - P.alpha j) ^ (t - u) •
          (μ j (u + 2) - μ j (u + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ Finset.range t, ∑ j : Fin P.J,
        ‖(1 - P.alpha j) ^ (t - u) •
          (μ j (u + 2) - μ j (u + 1))‖ := by
            apply Finset.sum_le_sum
            intro u hu
            exact norm_sum_le _ _
    _ = ∑ u ∈ Finset.range t, ∑ j : Fin P.J,
        |1 - P.alpha j| ^ (t - u) *
          ‖μ j (u + 2) - μ j (u + 1)‖ := by
            simp_rw [norm_smul, Real.norm_eq_abs, abs_pow]

theorem aggregateMeanLag_of_alpha_one {d : ℕ}
    (μ : Fin P.J → ℕ → Point d)
    (hα : ∀ j : Fin P.J, P.alpha j = 1) (t : ℕ) :
    aggregateMeanLag P μ t = 0 := by
  unfold aggregateMeanLag
  apply Finset.sum_eq_zero
  intro j hj
  rw [bandMeanComponent_of_alpha_one P j (μ j) (hα j) t]
  simp

theorem aggregateMeanLag_no_bands {d : ℕ}
    (μ : Fin P.J → ℕ → Point d) (hJ : P.J = 0) (t : ℕ) :
    aggregateMeanLag P μ t = 0 := by
  simp [aggregateMeanLag, hJ]

theorem aggregateMeanLag_first_time {d : ℕ}
    (μ : Fin P.J → ℕ → Point d) :
    aggregateMeanLag P μ 0 = 0 := by
  rw [aggregateMeanLag_eq_source_moves]
  simp

end

end HeavyTailedNoise.UpperK1
