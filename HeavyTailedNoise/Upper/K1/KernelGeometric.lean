import HeavyTailedNoise.Upper.K1.SharedKernel

/-!
Dimension-free scalar estimates for the exact shared-source EMA kernel.
The double-scale coefficient keeps covariance of two bands applied to the
same returned response. These lemmas do not assume band independence.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

theorem geometric_partial_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (T : ℕ) :
    (∑ k ∈ Finset.range T, r ^ k) ≤ (1 - r)⁻¹ := by
  calc
    (∑ k ∈ Finset.range T, r ^ k) ≤ ∑' k : ℕ, r ^ k :=
      (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum
        (Finset.range T) (fun k _ => pow_nonneg hr0 k)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1

/-- For `i ≤ j`, the coefficient in the exact square-sum is at most the
`j`-band EMA weight. The conclusion itself needs no monotonicity hypothesis. -/
theorem shared_cross_coefficient_le {α β : ℝ}
    (hα : 0 < α) (hαle : α ≤ 1) (hβ : 0 ≤ β) :
    α * β / (α + β - α * β) ≤ β := by
  have haux : 0 ≤ β * (1 - α) :=
    mul_nonneg hβ (sub_nonneg.mpr hαle)
  have hd : 0 < α + β - α * β := by nlinarith
  apply (div_le_iff₀ hd).2
  nlinarith

end

end HeavyTailedNoise.UpperK1
