import HeavyTailedNoise.Upper.K1.PhysicalParameters

/-!
Pure exponent identities behind the response-count conversion. These are
independent of the oracle and dimension. The `max`/ceiling inequalities and
the final `C(p,q)` bound remain separate proof obligations.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

/-- Every manuscript high-band EMA coefficient is positive when κ is positive. -/
theorem paperAlpha_pos {p q κ : ℝ} (hκ : 0 < κ) (j : ℕ) :
    0 < paperAlpha p q κ j := by
  unfold paperAlpha
  apply lt_min
  · norm_num
  · have ht : 0 < 12 * (2 : ℝ) ^ j := by positivity
    exact inv_pos.mpr (mul_pos hκ (Real.rpow_pos_of_pos ht _))

theorem paperAlpha_le_one (p q κ : ℝ) (j : ℕ) :
    paperAlpha p q κ j ≤ 1 := by
  exact min_le_left _ _

/-- Initialization: `S² U^(2-p)` becomes `S^(p/(p-1))` when
`U` is at the tail cutoff scale. -/
theorem initial_exponent_identity {p : ℝ} (hp : 1 < p) :
    (2 : ℝ) + (2 - p) / (p - 1) = p / (p - 1) := by
  have hne : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  field_simp [hne]
  ring

/-- Runtime: the positive scale exponent yields exactly `r/q`, including the
critical curve where it equals the unscaled `S²` exponent. -/
theorem runtime_exponent_identity {p q : ℝ} (hp : 1 < p) (hq : 0 < q) :
    (2 : ℝ) + (paperA p - paperSexp p q) / (p - 1) =
      (p / (p - 1)) / q := by
  have hpne : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hqne : q ≠ 0 := ne_of_gt hq
  unfold paperA paperSexp
  field_simp [hpne, hqne]
  ring

/-- The two runtime cases combine into the manuscript's `max{S²,S^(r/q)}`
exponent without an additional logarithmic term on the equality curve. -/
theorem runtime_max_exponent_identity {p q : ℝ} (hp : 1 < p) (hq : 0 < q) :
    (2 : ℝ) + paperEplus p q / (p - 1) =
      max 2 ((p / (p - 1)) / q) := by
  have hd : 0 < p - 1 := sub_pos.mpr hp
  let e := paperA p - paperSexp p q
  have hr : (p / (p - 1)) / q = 2 + e / (p - 1) := by
    simpa only [e] using (runtime_exponent_identity hp hq).symm
  by_cases he : e ≤ 0
  · have hrle : (p / (p - 1)) / q ≤ 2 := by
      rw [hr]
      have hdiv : e / (p - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg he hd.le
      linarith
    calc
      2 + paperEplus p q / (p - 1) = 2 := by
        simp [paperEplus, e, max_eq_right he]
      _ = max 2 ((p / (p - 1)) / q) := (max_eq_left hrle).symm
  · have hep : 0 ≤ e := le_of_not_ge he
    have hrge : (2 : ℝ) ≤ (p / (p - 1)) / q := by
      rw [hr]
      have hdiv : 0 ≤ e / (p - 1) := div_nonneg hep hd.le
      linarith
    calc
      2 + paperEplus p q / (p - 1) = 2 + e / (p - 1) := by
        simp [paperEplus, e, max_eq_left hep]
      _ = (p / (p - 1)) / q := hr.symm
      _ = max 2 ((p / (p - 1)) / q) := (max_eq_right hrge).symm

end

end HeavyTailedNoise.UpperK1
