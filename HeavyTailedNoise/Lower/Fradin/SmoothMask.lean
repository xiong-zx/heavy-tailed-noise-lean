import HeavyTailedNoise.Analysis.GateAlgebra

/-!
The actual suffix mask of Fradin et al., arXiv:2512.18713v2, B.3.
We use the authorized C² quintic selector. Its Lipschitz constant is 15/2,
so the suffix mask has constant 225/4, rather than the source's 36.
No differentiability of the Euclidean norm at zero is required.
-/

namespace HeavyTailedNoise.Fradin

open HeavyTailedNoise
open scoped Topology NNReal

noncomputable section

/-- The selector is zero up to 1/4 and one from 1/2 onward. -/
def selector (t : ℝ) : ℝ := smoothstep (4 * t - 1)

theorem selector_nonneg (t : ℝ) : 0 ≤ selector t := smoothstep_nonneg _

theorem selector_le_one (t : ℝ) : selector t ≤ 1 := smoothstep_le_one _

theorem selector_zero {t : ℝ} (ht : t ≤ 1 / 4) : selector t = 0 := by
  apply smoothstep_zero_of_nonpos
  linarith

theorem selector_one {t : ℝ} (ht : 1 / 2 ≤ t) : selector t = 1 := by
  apply smoothstep_one_of_one_le
  linarith

theorem selector_contDiff : ContDiff ℝ 2 selector := by
  exact contDiff_smoothstep_two.comp (by fun_prop)

theorem selector_monotone : Monotone selector := by
  have hs : Monotone smoothstep := monotone_of_deriv_nonneg differentiable_smoothstep
    (fun t => by
      rw [deriv_smoothstep_formula]
      split_ifs <;> positivity)
  intro s t hst
  exact hs (by linarith : 4 * s - 1 ≤ 4 * t - 1)

theorem smoothstep_lipschitz : LipschitzWith (15 / 8 : ℝ≥0) smoothstep := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_smoothstep
  intro t
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_ofNat] using
    abs_deriv_smoothstep_le t

theorem selector_sub_bound (s t : ℝ) :
    |selector s - selector t| ≤ (15 / 2 : ℝ) * |s - t| := by
  have h := smoothstep_lipschitz.dist_le_mul (4 * s - 1) (4 * t - 1)
  simp only [dist_eq_norm, Real.norm_eq_abs] at h
  have hid : (4 * s - 1) - (4 * t - 1) = 4 * (s - t) := by ring
  rw [hid, abs_mul] at h
  norm_num at h
  change |smoothstep (4 * s - 1) - smoothstep (4 * t - 1)| ≤ _
  nlinarith

theorem selector_lipschitz : LipschitzWith (15 / 2 : ℝ≥0) selector := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_ofNat] using
    selector_sub_bound s t

/-- The original suffix, padded with zero coordinates to keep one space. -/
def suffixSelector {T : ℕ} (i : Fin T) (x : Point T) : Point T :=
  WithLp.toLp 2 (fun k => if i ≤ k then selector |x k| else 0)

/-- B.3's actual smoothed suffix indicator. -/
def mask {T : ℕ} (i : Fin T) (x : Point T) : ℝ :=
  selector (1 - ‖suffixSelector i x‖)

theorem mask_nonneg {T : ℕ} (i : Fin T) (x : Point T) : 0 ≤ mask i x :=
  selector_nonneg _

theorem mask_le_one {T : ℕ} (i : Fin T) (x : Point T) : mask i x ≤ 1 :=
  selector_le_one _

theorem suffixSelector_zero_of_small {T : ℕ} (i : Fin T) (x : Point T)
    (hx : ∀ k, i ≤ k → |x k| ≤ 1 / 4) : suffixSelector i x = 0 := by
  ext k
  change (if i ≤ k then selector |x k| else 0) = 0
  by_cases hk : i ≤ k
  · simp [hk, selector_zero (hx k hk)]
  · simp [hk]

theorem mask_one_of_suffix_small {T : ℕ} (i : Fin T) (x : Point T)
    (hx : ∀ k, i ≤ k → |x k| ≤ 1 / 4) : mask i x = 1 := by
  rw [mask, suffixSelector_zero_of_small i x hx, norm_zero]
  apply selector_one
  norm_num

theorem mask_zero_of_suffix_large {T : ℕ} (i k : Fin T) (x : Point T)
    (hik : i ≤ k) (hx : 1 / 2 ≤ |x k|) : mask i x = 0 := by
  have hcoord := PiLp.norm_apply_le (suffixSelector i x) k
  have heq : (suffixSelector i x) k = 1 := by
    simp [suffixSelector, hik, selector_one hx]
  rw [heq, norm_one] at hcoord
  apply selector_zero
  linarith

theorem suffix_small_of_mask_ne_zero {T : ℕ} (i : Fin T) (x : Point T)
    (hi : mask i x ≠ 0) (k : Fin T) (hik : i ≤ k) : |x k| < 1 / 2 := by
  by_contra h
  exact hi (mask_zero_of_suffix_large i k x hik (le_of_not_gt h))

theorem suffixSelector_sub_bound {T : ℕ} (i : Fin T) (x y : Point T) :
    ‖suffixSelector i x - suffixSelector i y‖ ≤ (15 / 2 : ℝ) * ‖x - y‖ := by
  have hcoord (k : Fin T) :
      |(suffixSelector i x - suffixSelector i y) k| ≤ (15 / 2 : ℝ) * |(x - y) k| := by
    change |(if i ≤ k then selector |x k| else 0) -
      (if i ≤ k then selector |y k| else 0)| ≤ (15 / 2 : ℝ) * |x k - y k|
    by_cases hk : i ≤ k
    · simp only [if_pos hk]
      exact (selector_sub_bound _ _).trans
        (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub _ _) (by norm_num))
    · simp [hk]
  have hsq : ‖suffixSelector i x - suffixSelector i y‖ ^ 2 ≤
      ((15 / 2 : ℝ) * ‖x - y‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hcoord k)
    simpa only [sq_abs, mul_pow] using h
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

theorem mask_sub_bound {T : ℕ} (i : Fin T) (x y : Point T) :
    |mask i x - mask i y| ≤ (225 / 4 : ℝ) * ‖x - y‖ := by
  have h := selector_sub_bound (1 - ‖suffixSelector i x‖) (1 - ‖suffixSelector i y‖)
  have hid : (1 - ‖suffixSelector i x‖) - (1 - ‖suffixSelector i y‖) =
      -(‖suffixSelector i x‖ - ‖suffixSelector i y‖) := by ring
  rw [hid, abs_neg] at h
  exact h.trans (by
    calc
      (15 / 2 : ℝ) * |‖suffixSelector i x‖ - ‖suffixSelector i y‖| ≤
          (15 / 2 : ℝ) * ‖suffixSelector i x - suffixSelector i y‖ :=
        mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (by norm_num)
      _ ≤ (15 / 2 : ℝ) * ((15 / 2 : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (suffixSelector_sub_bound i x y) (by norm_num)
      _ = (225 / 4 : ℝ) * ‖x - y‖ := by ring)

theorem mask_lipschitz {T : ℕ} (i : Fin T) :
    LipschitzWith (225 / 4 : ℝ≥0) (mask i) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_ofNat] using
    mask_sub_bound i x y

theorem continuous_mask {T : ℕ} (i : Fin T) : Continuous (mask i) :=
  (mask_lipschitz i).continuous

end
end HeavyTailedNoise.Fradin
