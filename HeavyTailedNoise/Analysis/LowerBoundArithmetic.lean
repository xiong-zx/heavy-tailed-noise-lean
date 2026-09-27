import Mathlib

/-!
Parameter arithmetic for the frozen strict-K=1 response lower bound. These
facts do not assume the still-open geometric or conditional Haar lemmas.
-/

namespace HeavyTailedNoise

/-- At arguments at least two, flooring loses at most a factor of two. -/
theorem natFloor_ge_half_of_ge_two {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor : (2 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hfloorReal : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hfloor
  have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

/-- The advertised coarse constant survives exact rational arithmetic after
the two floor losses, the dimension ratio, and the quarter-budget count. -/
theorem gatedRate_coefficient_ge_one_e24 :
    (1 / 10 ^ 24 : ℝ) ≤
      ((1 / 40 : ℝ) ^ 2 / (96 * 4300)) *
        ((1 / 4005.25 : ℝ) * (1 / 80 : ℝ) ^ 2 / (32 * 300 ^ 2)) / 4 := by
  norm_num

/-- The manuscript's floor choice of chain length exactly enforces the
function-value budget after rescaling. -/
theorem gatedChainLength_budget (L ε Δ : ℝ)
    (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 ≤ Δ) :
    330240000 * ε ^ 2 *
      (⌊L * Δ / (330240000 * ε ^ 2)⌋₊ : ℝ) ≤ L * Δ := by
  let den : ℝ := 330240000 * ε ^ 2
  have hden : 0 < den := by dsimp [den]; positivity
  have hx : 0 ≤ L * Δ / den := by positivity
  have hfloor :
      (⌊L * Δ / den⌋₊ : ℝ) ≤ L * Δ / den := Nat.floor_le hx
  have hmul := mul_le_mul_of_nonneg_left hfloor hden.le
  have hcancel : den * (L * Δ / den) = L * Δ := by
    field_simp [hden.ne']
  dsimp [den] at hmul hcancel ⊢
  linarith

/-- The manuscript's two floor lower bounds imply its advertised coarse
`10⁻²⁴ A S²` quarter-budget scale. No stochastic premise is hidden here. -/
theorem gated_quarter_budget_ge_one_e24
    (A S : ℝ) (T n₀ : ℕ) (hA : 0 ≤ A)
    (hT : ((1 / 40 : ℝ) ^ 2 / (96 * 4300)) * A ≤ T)
    (hn₀ : ((1 / 4005.25 : ℝ) * (1 / 80 : ℝ) ^ 2 /
      (32 * 300 ^ 2)) * S ^ 2 ≤ n₀) :
    (1 / 10 ^ 24 : ℝ) * A * S ^ 2 ≤ (T : ℝ) * n₀ / 4 := by
  let α : ℝ := (1 / 40 : ℝ) ^ 2 / (96 * 4300)
  let β : ℝ := (1 / 4005.25 : ℝ) * (1 / 80 : ℝ) ^ 2 / (32 * 300 ^ 2)
  have hα : 0 ≤ α := by dsimp [α]; norm_num
  have hβ : 0 ≤ β := by dsimp [β]; norm_num
  have hβS : 0 ≤ β * S ^ 2 := mul_nonneg hβ (sq_nonneg S)
  have hT0 : 0 ≤ (T : ℝ) := Nat.cast_nonneg _
  have hprod : (α * A) * (β * S ^ 2) ≤ (T : ℝ) * n₀ := by
    apply mul_le_mul
    · simpa [α] using hT
    · simpa [β] using hn₀
    · exact hβS
    · exact hT0
  have hconst : (1 / 10 ^ 24 : ℝ) ≤ α * β / 4 := by
    simpa [α, β] using gatedRate_coefficient_ge_one_e24
  have hAsq : 0 ≤ A * S ^ 2 := mul_nonneg hA (sq_nonneg S)
  calc
    (1 / 10 ^ 24 : ℝ) * A * S ^ 2 =
        (1 / 10 ^ 24 : ℝ) * (A * S ^ 2) := by ring
    _ ≤ (α * β / 4) * (A * S ^ 2) :=
      mul_le_mul_of_nonneg_right hconst hAsq
    _ = ((α * A) * (β * S ^ 2)) / 4 := by ring
    _ ≤ ((T : ℝ) * n₀) / 4 :=
      div_le_div_of_nonneg_right hprod (by norm_num)

end HeavyTailedNoise
