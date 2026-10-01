import HeavyTailedNoise.Upper.K1.Algorithm

/-!
Pure finite EMA algebra for the manuscript's high-band mean component. The
coefficients are exactly `P.alpha j` and `1 - P.alpha j` from the single
algorithm update. These definitions do not introduce another oracle or
runtime memory state.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- Initial weight plus all finite EMA source weights totals one, including
the `α = 1`, `b = 0` endpoint. -/
theorem ema_finite_unit_weight (α : ℝ) (t : ℕ) :
    (1 - α) ^ t + ∑ k ∈ Finset.range t, α * (1 - α) ^ k = 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        (1 - α) ^ t * (1 - α) +
            ((∑ k ∈ Finset.range t, α * (1 - α) ^ k) +
              α * (1 - α) ^ t) =
          (1 - α) ^ t + ∑ k ∈ Finset.range t, α * (1 - α) ^ k := by ring
        _ = 1 := ih

variable {q : ℝ} (P : Schedule q)

/-- Algebraic mean component of one band after replacing each observed batch
statistic in the literal EMA update by its pre-batch source mean. -/
def bandMeanComponent {d : ℕ} (j : Fin P.J) (μ : ℕ → Point d) :
    ℕ → Point d
  | 0 => μ 1
  | t + 1 => (1 - P.alpha j) • bandMeanComponent j μ t +
      P.alpha j • μ (t + 1)

@[simp] theorem bandMeanComponent_zero {d : ℕ} (j : Fin P.J)
    (μ : ℕ → Point d) : bandMeanComponent P j μ 0 = μ 1 := rfl

theorem bandMeanComponent_succ {d : ℕ} (j : Fin P.J)
    (μ : ℕ → Point d) (t : ℕ) :
    bandMeanComponent P j μ (t + 1) =
      (1 - P.alpha j) • bandMeanComponent P j μ t +
        P.alpha j • μ (t + 1) := rfl

/-- At `q = 1` the manuscript schedule has `α_j = 1`; the algebraic mean
component is then exactly the current source mean at every positive time. -/
theorem bandMeanComponent_of_alpha_one {d : ℕ} (j : Fin P.J)
    (μ : ℕ → Point d) (hα : P.alpha j = 1) (t : ℕ) :
    bandMeanComponent P j μ (t + 1) = μ (t + 1) := by
  simp [bandMeanComponent, hα]

end

end HeavyTailedNoise.UpperK1
