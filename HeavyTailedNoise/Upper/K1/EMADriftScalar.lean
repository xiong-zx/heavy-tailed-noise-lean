import HeavyTailedNoise.Upper.K1.RateArithmetic

/-!
Finite-horizon accounting for the genuine EMA retention weights.  The
identity is a telescoping recurrence, so the first lag and the terminal
memory mass are kept exactly; no infinite-series replacement is needed.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- Scalar envelope of the source-mean lag of one band. -/
def emaDriftMass (b : ℝ) (D : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ u ∈ Finset.range t, b ^ (t - u) * D u

theorem emaDriftMass_succ (b : ℝ) (D : ℕ → ℝ) (t : ℕ) :
    emaDriftMass b D (t + 1) =
      b * emaDriftMass b D t + b * D t := by
  have hsum :
      (∑ u ∈ Finset.range t, b ^ ((t + 1) - u) * D u) =
        b * ∑ u ∈ Finset.range t, b ^ (t - u) * D u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hut : u < t := Finset.mem_range.mp hu
    have hindex : (t + 1) - u = (t - u) + 1 := by omega
    rw [hindex, pow_succ]
    ring
  calc
    emaDriftMass b D (t + 1) =
        (∑ u ∈ Finset.range t, b ^ ((t + 1) - u) * D u) +
          b * D t := by
            simp [emaDriftMass, Finset.sum_range_succ]
    _ = b * emaDriftMass b D t + b * D t := by
      rw [hsum]
      rfl

theorem emaDriftMass_nonneg (b : ℝ) (hb : 0 ≤ b)
    (D : ℕ → ℝ) (hD : ∀ u, 0 ≤ D u) (t : ℕ) :
    0 ≤ emaDriftMass b D t := by
  unfold emaDriftMass
  exact Finset.sum_nonneg fun u _ =>
    mul_nonneg (pow_nonneg hb _) (hD u)

/-- Exact finite-horizon telescoping, including the terminal lag mass. -/
theorem emaDriftMass_sum_identity (b : ℝ) (D : ℕ → ℝ) (T : ℕ) :
    (1 - b) * (∑ t ∈ Finset.range T, emaDriftMass b D t) +
      emaDriftMass b D T =
      b * (∑ u ∈ Finset.range T, D u) := by
  induction T with
  | zero => simp [emaDriftMass]
  | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        emaDriftMass_succ]
      linear_combination ih

/-- If the actual retention coefficient satisfies `b ≤ (1-b) * W`,
the average lag is bounded by `W` times the average source motion. -/
theorem emaDriftMass_sum_le
    (b W : ℝ) (D : ℕ → ℝ) (T : ℕ)
    (hb : 0 ≤ b) (hα : 0 < 1 - b)
    (hweight : b ≤ (1 - b) * W)
    (hD : ∀ u, 0 ≤ D u) :
    (∑ t ∈ Finset.range T, emaDriftMass b D t) ≤
      W * (∑ u ∈ Finset.range T, D u) := by
  have hterminal : 0 ≤ emaDriftMass b D T :=
    emaDriftMass_nonneg b hb D hD T
  have hDsum : 0 ≤ ∑ u ∈ Finset.range T, D u :=
    Finset.sum_nonneg fun u _ => hD u
  have hidentity := emaDriftMass_sum_identity b D T
  have hleft : (1 - b) *
      (∑ t ∈ Finset.range T, emaDriftMass b D t) ≤
      b * (∑ u ∈ Finset.range T, D u) := by linarith
  have hright : b * (∑ u ∈ Finset.range T, D u) ≤
      (1 - b) * (W * (∑ u ∈ Finset.range T, D u)) := by
    calc
      b * (∑ u ∈ Finset.range T, D u) ≤
          ((1 - b) * W) * (∑ u ∈ Finset.range T, D u) :=
            mul_le_mul_of_nonneg_right hweight hDsum
      _ = (1 - b) * (W * (∑ u ∈ Finset.range T, D u)) := by ring
  exact (mul_le_mul_iff_of_pos_left hα).mp (hleft.trans hright)

end

end HeavyTailedNoise.UpperK1
