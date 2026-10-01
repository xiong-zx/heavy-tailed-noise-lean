import HeavyTailedNoise.Upper.K1.PhysicalParameters

/-!
Exact max/ceiling arithmetic for the frozen algorithm's coarse tracker and
response budgets. These identities include the σ=0 endpoint.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

/-- The physical residual scale is exactly accuracy times the manuscript's
normalized noise scale, including σ≤ε and σ=0. -/
theorem paperNu_eq_eps_mul_paperS {σ ε : ℝ} (hε : 0 < ε) :
    paperNu σ ε = ε * paperS σ ε := by
  unfold paperNu paperS
  have hmul : ε * (σ / ε) = σ := by
    field_simp [ne_of_gt hε]
  rw [mul_max_of_nonneg 1 (σ / ε) hε.le, mul_one, hmul, max_comm]

theorem paperS_le_ceil (σ ε : ℝ) :
    paperS σ ε ≤ (Nat.ceil (paperS σ ε) : ℝ) :=
  Nat.le_ceil _

theorem paperS_ceil_lt_add_one (σ ε : ℝ) :
    (Nat.ceil (paperS σ ε) : ℝ) < paperS σ ε + 1 :=
  Nat.ceil_lt_add_one (paperS_pos σ ε).le

theorem paperS_ceil_le_two_mul (σ ε : ℝ) :
    (Nat.ceil (paperS σ ε) : ℝ) ≤ 2 * paperS σ ε := by
  have hceil := paperS_ceil_lt_add_one σ ε
  have hS := one_le_paperS σ ε
  linarith

end

end HeavyTailedNoise.UpperK1
