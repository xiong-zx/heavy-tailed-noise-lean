import HeavyTailedNoise.Upper.K1.KernelMinkowskiVector

/-!
An active dyadic-shell sum without a factor proportional to the number of
bands.  The active indices need only lie below their maximum; equality with
a prefix is unnecessary.  Empty active sets and `J = 0` are included.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- The active high thresholds `12·2^j < x`, before the terminal index `J`. -/
def activeDyadic (J : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range J).filter (fun j => 12 * (2 : ℝ) ^ j < x)

private theorem geometric_prefix_le_last {r : ℝ} (hr : 1 < r) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), r ^ j) ≤ r / (r - 1) * r ^ m := by
  have hden : 0 < r - 1 := by linarith
  have hgeom := geom_sum_mul_of_one_le hr.le (m + 1)
  calc
    (∑ j ∈ Finset.range (m + 1), r ^ j) ≤ r ^ (m + 1) / (r - 1) := by
      apply (le_div_iff₀ hden).2
      linarith [hgeom]
    _ = r / (r - 1) * r ^ m := by
      rw [pow_succ]
      ring

private theorem dyadic_rpow_eq (a : ℝ) (j : ℕ) :
    (12 * (2 : ℝ) ^ j) ^ a = 12 ^ a * ((2 : ℝ) ^ a) ^ j := by
  rw [Real.mul_rpow (by norm_num) (pow_nonneg (by norm_num) _)]
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) a j]

/-- Full prefix controlled by its last dyadic term. -/
theorem dyadic_rpow_prefix_le_last {a : ℝ} (ha : 0 < a) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), (12 * (2 : ℝ) ^ j) ^ a) ≤
      ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
        (12 * (2 : ℝ) ^ m) ^ a := by
  let r : ℝ := (2 : ℝ) ^ a
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) ha
  have h12 : 0 ≤ (12 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) _
  calc
    (∑ j ∈ Finset.range (m + 1), (12 * (2 : ℝ) ^ j) ^ a) =
        (12 : ℝ) ^ a * ∑ j ∈ Finset.range (m + 1), r ^ j := by
          simp_rw [dyadic_rpow_eq]
          rw [Finset.mul_sum]
    _ ≤ (12 : ℝ) ^ a * (r / (r - 1) * r ^ m) :=
      mul_le_mul_of_nonneg_left (geometric_prefix_le_last hr m) h12
    _ = ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
        (12 * (2 : ℝ) ^ m) ^ a := by
          rw [dyadic_rpow_eq]
          dsimp [r]
          ring

/-- The active sum is controlled by the radius, with an explicit empty-set
branch and no `J` factor. -/
theorem activeDyadic_sum_le_radius
    (J : ℕ) {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    (∑ j ∈ activeDyadic J x, (12 * (2 : ℝ) ^ j) ^ a) ≤
      ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) * x ^ a := by
  let S := activeDyadic J x
  have hC : 0 ≤ (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) := by
    have hr := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) ha
    positivity
  by_cases hS : S.Nonempty
  · let m := S.max' hS
    have hmS : m ∈ S := Finset.max'_mem S hS
    have hsubset : S ⊆ Finset.range (m + 1) := by
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' S j hj))
    have hsum : (∑ j ∈ S, (12 * (2 : ℝ) ^ j) ^ a) ≤
        ∑ j ∈ Finset.range (m + 1), (12 * (2 : ℝ) ^ j) ^ a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun j hj hnot => Real.rpow_nonneg (by positivity) _)
    have hmx : 12 * (2 : ℝ) ^ m < x :=
      (Finset.mem_filter.mp hmS).2
    have hpow : (12 * (2 : ℝ) ^ m) ^ a ≤ x ^ a :=
      Real.rpow_le_rpow (by positivity) hmx.le ha.le
    calc
      (∑ j ∈ activeDyadic J x, (12 * (2 : ℝ) ^ j) ^ a) ≤
          ∑ j ∈ Finset.range (m + 1), (12 * (2 : ℝ) ^ j) ^ a := hsum
      _ ≤ ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
          (12 * (2 : ℝ) ^ m) ^ a := dyadic_rpow_prefix_le_last ha m
      _ ≤ ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) * x ^ a :=
        mul_le_mul_of_nonneg_left hpow hC
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [S, hempty, Finset.sum_empty]
    exact mul_nonneg hC (Real.rpow_nonneg hx _)

/-- The same active sum is controlled by the terminal dyadic scale. -/
theorem activeDyadic_sum_le_terminal
    (J : ℕ) {x a : ℝ} (ha : 0 < a) :
    (∑ j ∈ activeDyadic J x, (12 * (2 : ℝ) ^ j) ^ a) ≤
      ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
        (12 * (2 : ℝ) ^ J) ^ a := by
  by_cases hJ : J = 0
  · subst J
    simp [activeDyadic]
    have hr := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) ha
    positivity
  · let m := J - 1
    have hmJ : J = m + 1 := by dsimp [m]; omega
    have hsubset : activeDyadic J x ⊆ Finset.range J := Finset.filter_subset _ _
    have hsum : (∑ j ∈ activeDyadic J x, (12 * (2 : ℝ) ^ j) ^ a) ≤
        ∑ j ∈ Finset.range J, (12 * (2 : ℝ) ^ j) ^ a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun j hj hnot => Real.rpow_nonneg (by positivity) _)
    have hlast : (12 * (2 : ℝ) ^ m) ^ a ≤
        (12 * (2 : ℝ) ^ J) ^ a := by
      apply Real.rpow_le_rpow (by positivity) _ ha.le
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le J 1))
        (by norm_num)
    have hC : 0 ≤ (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) := by
      have hr := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) ha
      positivity
    calc
      (∑ j ∈ activeDyadic J x, (12 * (2 : ℝ) ^ j) ^ a) ≤
          ∑ j ∈ Finset.range J, (12 * (2 : ℝ) ^ j) ^ a := hsum
      _ = ∑ j ∈ Finset.range (m + 1), (12 * (2 : ℝ) ^ j) ^ a := by
        rw [← hmJ]
      _ ≤ ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
          (12 * (2 : ℝ) ^ m) ^ a := dyadic_rpow_prefix_le_last ha m
      _ ≤ ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
          (12 * (2 : ℝ) ^ J) ^ a := mul_le_mul_of_nonneg_left hlast hC

/-- The no-log `min(x,U)^a` form, including `J=0` and no active scales. -/
theorem activeDyadic_sum_le_min
    (J : ℕ) {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    (∑ j ∈ activeDyadic J x, (12 * (2 : ℝ) ^ j) ^ a) ≤
      ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
        (min x (12 * (2 : ℝ) ^ J)) ^ a := by
  rcases le_total x (12 * (2 : ℝ) ^ J) with h | h
  · rw [min_eq_left h]
    exact activeDyadic_sum_le_radius J hx ha
  · rw [min_eq_right h]
    exact activeDyadic_sum_le_terminal J ha

end

end HeavyTailedNoise.UpperK1
