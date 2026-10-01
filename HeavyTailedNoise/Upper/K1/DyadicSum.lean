import HeavyTailedNoise.Upper.K1.KernelGeometric

/-!
A dyadic partial-sum bound for the actual magnitude bands. Together with
`‖D_j(z)‖ ≤ 3τ_{j-1}`, it controls cumulative shell norms without proving
radial collinearity or discarding same-source cross terms.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

theorem sum_pow_two_le_double_last (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (2 : ℝ) ^ i) ≤
      2 * (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]

end

end HeavyTailedNoise.UpperK1
