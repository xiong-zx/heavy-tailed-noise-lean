import HeavyTailedNoise.Model.Basic

/-!
The deterministic count behind the final stage argument. It applies to
completed stages once their positive integer lengths have been related to
the stopped protocol; that stochastic relation is not asserted here.
-/

namespace HeavyTailedNoise

/-- If completing all `T` stages fits within a quarter of `T * n₀`
queries, at least three quarters of the stages have length at most `n₀`.
The integer formulation avoids rounding `T / 4`. -/
theorem many_short_stages_of_budget {T n₀ : ℕ} (hn₀ : 0 < n₀)
    (length : Fin T → ℕ)
    (hbudget : 4 * (∑ j, length j) ≤ T * n₀) :
    3 * T ≤ 4 * (Finset.univ.filter fun j : Fin T => length j ≤ n₀).card := by
  classical
  let short := Finset.univ.filter fun j : Fin T => length j ≤ n₀
  let long := Finset.univ.filter fun j : Fin T => n₀ < length j
  have hcount : short.card + long.card = T := by
    simpa [short, long, not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (p := fun j : Fin T => length j ≤ n₀))
  have hlongcost : long.card * n₀ ≤ ∑ j, length j := by
    calc
      long.card * n₀ = ∑ j ∈ long, n₀ := by simp
      _ ≤ ∑ j ∈ long, length j := by
        apply Finset.sum_le_sum
        intro j hj
        exact (Finset.mem_filter.mp hj).2.le
      _ ≤ ∑ j, length j := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (by simp)
  have hscaled : (4 * long.card) * n₀ ≤ T * n₀ := by
    nlinarith [hlongcost, hbudget]
  have hlong : 4 * long.card ≤ T := le_of_mul_le_mul_right hscaled hn₀
  change 3 * T ≤ 4 * short.card
  omega

end HeavyTailedNoise
