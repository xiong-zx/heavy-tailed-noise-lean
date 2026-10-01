import HeavyTailedNoise.Upper.K1.KernelSquaredBound

/-!
A conditional finite-sum bridge from the already proved same-source
Minkowski bound to the active dyadic-shell sum.  Its two per-shell premises
are stated explicitly; a later theorem must discharge them for the literal
paper schedule.  No band-independence assumption is used.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

private theorem sum_fin_nat_eq_range (J : ℕ) (f : ℕ → ℝ) :
    (∑ j : Fin J, f (j : ℕ)) = ∑ j ∈ Finset.range J, f j := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]

private theorem sum_active_fin_eq (J : ℕ) (x : ℝ) (f : ℕ → ℝ) :
    (∑ j : Fin J,
      if 12 * (2 : ℝ) ^ (j : ℕ) < x then f (j : ℕ) else 0) =
      ∑ j ∈ activeDyadic J x, f j := by
  calc
    (∑ j : Fin J,
      if 12 * (2 : ℝ) ^ (j : ℕ) < x then f (j : ℕ) else 0) =
        ∑ j ∈ Finset.range J,
          if 12 * (2 : ℝ) ^ j < x then f j else 0 :=
            sum_fin_nat_eq_range J
              (fun j => if 12 * (2 : ℝ) ^ j < x then f j else 0)
    _ = ∑ j ∈ activeDyadic J x, f j := by
      simp only [activeDyadic, Finset.sum_filter]

/-- A sufficient shell-level contract for the no-log high-band square sum.
The support and weight hypotheses remain visible until proved for the
manuscript's concrete schedule. -/
theorem kernelPsi_sq_sum_le_dyadic_of_support_and_weight
    {q : ℝ} (P : Schedule q) {d T : ℕ} (z : Point d)
    (ν x a C : ℝ) (hν : 0 ≤ ν) (hx : 0 ≤ x)
    (ha : 0 < a) (hC : 0 ≤ C)
    (hα : ∀ j : Fin P.J, 0 < P.alpha j)
    (hαle : ∀ j : Fin P.J, P.alpha j ≤ 1)
    (hzero : ∀ j : Fin P.J,
      ¬ 12 * (2 : ℝ) ^ (j : ℕ) < x → highBand P j z = 0)
    (hweight : ∀ j : Fin P.J,
      Real.sqrt (P.alpha j) * ‖highBand P j z‖ ≤
        C * ν * (12 * (2 : ℝ) ^ (j : ℕ)) ^ a) :
    (∑ k ∈ Finset.range T, ‖kernelPsi P k z‖ ^ 2) ≤
      (C * ν * ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
        (min x (12 * (2 : ℝ) ^ P.J)) ^ a) ^ 2 := by
  have hCν : 0 ≤ C * ν := mul_nonneg hC hν
  have hsum_shell :
      (∑ j : Fin P.J, Real.sqrt (P.alpha j) * ‖highBand P j z‖) ≤
        C * ν * ∑ j ∈ activeDyadic P.J x,
          (12 * (2 : ℝ) ^ j) ^ a := by
    calc
      (∑ j : Fin P.J, Real.sqrt (P.alpha j) * ‖highBand P j z‖) ≤
          ∑ j : Fin P.J,
            if 12 * (2 : ℝ) ^ (j : ℕ) < x then
              C * ν * (12 * (2 : ℝ) ^ (j : ℕ)) ^ a else 0 := by
                apply Finset.sum_le_sum
                intro j hj
                by_cases hactive : 12 * (2 : ℝ) ^ (j : ℕ) < x
                · simpa only [if_pos hactive] using hweight j
                · simp [hactive, hzero j hactive]
      _ = ∑ j ∈ activeDyadic P.J x,
          C * ν * (12 * (2 : ℝ) ^ j) ^ a :=
            sum_active_fin_eq P.J x
              (fun j => C * ν * (12 * (2 : ℝ) ^ j) ^ a)
      _ = C * ν * ∑ j ∈ activeDyadic P.J x,
          (12 * (2 : ℝ) ^ j) ^ a := by
            rw [Finset.mul_sum]
  have hr : 1 < (2 : ℝ) ^ a :=
    Real.one_lt_rpow (by norm_num) ha
  have hratio : 0 ≤ (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) := by
    positivity
  have hmin : 0 ≤ min x (12 * (2 : ℝ) ^ P.J) :=
    le_min hx (by positivity)
  have hsum_nonneg :
      0 ≤ ∑ j : Fin P.J, Real.sqrt (P.alpha j) * ‖highBand P j z‖ :=
    Finset.sum_nonneg (fun j _ =>
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hright : 0 ≤ C * ν *
      ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
        (min x (12 * (2 : ℝ) ^ P.J)) ^ a :=
    mul_nonneg (mul_nonneg hCν hratio) (Real.rpow_nonneg hmin _)
  have hsum_final :
      (∑ j : Fin P.J, Real.sqrt (P.alpha j) * ‖highBand P j z‖) ≤
        C * ν * ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
          (min x (12 * (2 : ℝ) ^ P.J)) ^ a := by
    calc
      _ ≤ C * ν * ∑ j ∈ activeDyadic P.J x,
          (12 * (2 : ℝ) ^ j) ^ a := hsum_shell
      _ ≤ C * ν *
          (((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
            (min x (12 * (2 : ℝ) ^ P.J)) ^ a) :=
        mul_le_mul_of_nonneg_left
          (activeDyadic_sum_le_min P.J hx ha) hCν
      _ = _ := by ring
  calc
    (∑ k ∈ Finset.range T, ‖kernelPsi P k z‖ ^ 2) ≤
        (∑ j : Fin P.J,
          Real.sqrt (P.alpha j) * ‖highBand P j z‖) ^ 2 :=
            kernelPsi_sq_sum_le_weighted_bands P z hα hαle
    _ ≤ (C * ν * ((2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)) *
          (min x (12 * (2 : ℝ) ^ P.J)) ^ a) ^ 2 :=
            (sq_le_sq₀ hsum_nonneg hright).mpr hsum_final

end

end HeavyTailedNoise.UpperK1
