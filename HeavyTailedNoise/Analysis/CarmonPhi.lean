import HeavyTailedNoise.Model.Basic

/-!
The exact scalar `Φ` in Section 2.1 of the frozen gated Haar-chain construction:
`Φ(t) = sqrt(exp 1) * ∫ s ∈ (-∞, t], exp(-s² / 2) ds`.
All normalization constants are retained. The local `0.792` estimate is proved
by comparison with a polynomial, not by numerical integration.
-/

namespace HeavyTailedNoise

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

/-- The manuscript's improper Gaussian integral, represented as a Lebesgue
set integral on the left half-line. -/
def carmonPhi (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp 1) * ∫ s in Iic t, Real.exp (-s ^ 2 / 2)

lemma integrable_carmonPhi_kernel :
    Integrable (fun s : ℝ => Real.exp (-s ^ 2 / 2)) := by
  have heq : (fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s ^ 2)) =
      (fun s : ℝ => Real.exp (-s ^ 2 / 2)) := by
    funext s
    congr 1
    ring
  rw [← heq]
  exact integrable_exp_neg_mul_sq (by norm_num)

/-- Equality with the manuscript's improper integral: as its finite lower
endpoint tends to minus infinity, the normalized integrals tend to this exact Φ. -/
theorem tendsto_carmonPhi_improper (t : ℝ) :
    Tendsto (fun a : ℝ => Real.sqrt (Real.exp 1) *
      ∫ s in a..t, Real.exp (-s ^ 2 / 2)) atBot (𝓝 (carmonPhi t)) := by
  exact (intervalIntegral_tendsto_integral_Iic t
    integrable_carmonPhi_kernel.integrableOn tendsto_id).const_mul
      (Real.sqrt (Real.exp 1))

theorem carmonPhi_eq_improper_integral (t : ℝ) :
    carmonPhi t = limUnder atBot (fun a : ℝ => Real.sqrt (Real.exp 1) *
      ∫ s in a..t, Real.exp (-s ^ 2 / 2)) :=
  (tendsto_carmonPhi_improper t).limUnder_eq.symm

lemma continuous_carmonPhi_kernel :
    Continuous (fun s : ℝ => Real.exp (-s ^ 2 / 2)) := by fun_prop

/-- Difference identity connecting the exact half-line definition to the
ordinary interval integral used by the fundamental theorem of calculus. -/
theorem carmonPhi_sub (a b : ℝ) :
    carmonPhi b - carmonPhi a =
      Real.sqrt (Real.exp 1) * ∫ s in a..b, Real.exp (-s ^ 2 / 2) := by
  unfold carmonPhi
  rw [← mul_sub, intervalIntegral.integral_Iic_sub_Iic
    integrable_carmonPhi_kernel.integrableOn integrable_carmonPhi_kernel.integrableOn]

theorem hasDerivAt_carmonPhi (t : ℝ) :
    HasDerivAt carmonPhi (Real.sqrt (Real.exp 1) * Real.exp (-t ^ 2 / 2)) t := by
  have heq : carmonPhi = (fun u => carmonPhi 0 +
      Real.sqrt (Real.exp 1) * ∫ s in (0 : ℝ)..u, Real.exp (-s ^ 2 / 2)) := by
    funext u
    rw [← carmonPhi_sub 0 u]
    ring
  rw [heq]
  exact ((intervalIntegral.integral_hasDerivAt_right
    integrable_carmonPhi_kernel.intervalIntegrable
    continuous_carmonPhi_kernel.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_carmonPhi_kernel.continuousAt).const_mul
      (Real.sqrt (Real.exp 1))).const_add (carmonPhi 0)

theorem deriv_carmonPhi (t : ℝ) :
    deriv carmonPhi t = Real.sqrt (Real.exp 1) * Real.exp (-t ^ 2 / 2) :=
  (hasDerivAt_carmonPhi t).deriv

theorem differentiable_carmonPhi : Differentiable ℝ carmonPhi :=
  fun t => (hasDerivAt_carmonPhi t).differentiableAt

theorem contDiff_carmonPhi : ContDiff ℝ ∞ carmonPhi := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨differentiable_carmonPhi, ?_⟩
  have heq : deriv carmonPhi =
      (fun t : ℝ => Real.sqrt (Real.exp 1) * Real.exp (-t ^ 2 / 2)) :=
    funext deriv_carmonPhi
  rw [heq]
  fun_prop

theorem contDiff_carmonPhi_two : ContDiff ℝ 2 carmonPhi :=
  contDiff_carmonPhi.of_le (by norm_num)

theorem deriv_carmonPhi_pos (t : ℝ) : 0 < deriv carmonPhi t := by
  rw [deriv_carmonPhi]
  exact mul_pos (Real.sqrt_pos.mpr (Real.exp_pos 1)) (Real.exp_pos _)

theorem strictMono_carmonPhi : StrictMono carmonPhi :=
  strictMono_of_deriv_pos deriv_carmonPhi_pos

theorem carmonPhi_pos (t : ℝ) : 0 < carmonPhi t := by
  have : NeZero (volume.restrict (Iic t)) := ⟨by
    intro h
    have hh := congrArg (fun μ : Measure ℝ => μ univ) h
    simp at hh⟩
  exact mul_pos (Real.sqrt_pos.mpr (Real.exp_pos 1))
    (integral_exp_pos integrable_carmonPhi_kernel.integrableOn)

theorem hasDerivAt_deriv_carmonPhi (t : ℝ) :
    HasDerivAt (deriv carmonPhi)
      (-t * Real.sqrt (Real.exp 1) * Real.exp (-t ^ 2 / 2)) t := by
  have heq : deriv carmonPhi =
      (fun u : ℝ => Real.sqrt (Real.exp 1) * Real.exp (-u ^ 2 / 2)) :=
    funext deriv_carmonPhi
  rw [heq]
  convert! ((((hasDerivAt_id t).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (Real.exp 1))) using 1 <;> simp [Pi.pow_apply, Pi.neg_apply] <;> ring

theorem second_deriv_carmonPhi (t : ℝ) :
    deriv (deriv carmonPhi) t =
      -t * Real.sqrt (Real.exp 1) * Real.exp (-t ^ 2 / 2) :=
  (hasDerivAt_deriv_carmonPhi t).deriv

lemma carmonPhi_sqrt_exp_one_lt : Real.sqrt (Real.exp 1) < (33 / 20 : ℝ) := by
  have hs := Real.sq_sqrt (Real.exp_pos 1).le
  have hn := Real.sqrt_nonneg (Real.exp 1)
  have he := Real.exp_one_lt_d9
  nlinarith

/-- The alternating quadratic bound needed only at nonnegative arguments. -/
lemma carmonPhi_exp_neg_le_quadratic {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  let r : ℝ → ℝ := fun v => 1 - v + v ^ 2 / 2 - Real.exp (-v)
  have hr (v : ℝ) : HasDerivAt r (-1 + v + Real.exp (-v)) v := by
    dsimp [r]
    convert! (((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id v)).add
      (((hasDerivAt_id v).pow 2).div_const 2)).sub
        ((hasDerivAt_id v).neg.exp) using 1 <;> simp [Pi.pow_apply, Pi.neg_apply] <;> ring
  have hm : Monotone r := by
    apply monotone_of_deriv_nonneg (fun v => (hr v).differentiableAt)
    intro v
    rw [(hr v).deriv]
    linarith [Real.add_one_le_exp (-v)]
  have h := hm hu
  dsimp [r] at h
  simp only [neg_zero, Real.exp_zero, zero_pow, zero_div, sub_zero, add_zero,
    sub_self] at h
  linarith

lemma carmonPhi_kernel_le_polynomial (s : ℝ) :
    Real.exp (-s ^ 2 / 2) ≤ 1 - s ^ 2 / 2 + s ^ 4 / 8 := by
  have h := carmonPhi_exp_neg_le_quadratic (u := s ^ 2 / 2) (by positivity)
  convert h using 1 <;> ring

lemma carmonPhi_polynomial_integral (a b : ℝ) :
    (∫ s in a..b, (1 - s ^ 2 / 2 + s ^ 4 / 8 : ℝ)) =
      (b - b ^ 3 / 6 + b ^ 5 / 40) - (a - a ^ 3 / 6 + a ^ 5 / 40) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    convert! ((hasDerivAt_id s).sub (((hasDerivAt_id s).pow 3).div_const 6)).add
      (((hasDerivAt_id s).pow 5).div_const 40) using 1 <;>
        simp [Pi.pow_apply, Pi.neg_apply] <;> ring
  · exact (show Continuous (fun s : ℝ => 1 - s ^ 2 / 2 + s ^ 4 / 8) by
      fun_prop).intervalIntegrable _ _

lemma carmonPhi_half_integral_bound :
    (∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.exp (-s ^ 2 / 2)) ≤ 1843 / 3840 := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 2)
    integrable_carmonPhi_kernel.intervalIntegrable
    (show IntervalIntegrable (fun s : ℝ => 1 - s ^ 2 / 2 + s ^ 4 / 8)
      volume 0 (1 / 2) from (by fun_prop : Continuous _).intervalIntegrable _ _)
    (fun s _ => carmonPhi_kernel_le_polynomial s)
  rw [carmonPhi_polynomial_integral] at h
  norm_num at h ⊢
  exact h

lemma carmonPhi_neg_half_integral_bound :
    (∫ s in (-1 / 2 : ℝ)..(0 : ℝ), Real.exp (-s ^ 2 / 2)) ≤ 1843 / 3840 := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (-1 / 2 : ℝ) ≤ 0)
    integrable_carmonPhi_kernel.intervalIntegrable
    (show IntervalIntegrable (fun s : ℝ => 1 - s ^ 2 / 2 + s ^ 4 / 8)
      volume (-1 / 2) 0 from (by fun_prop : Continuous _).intervalIntegrable _ _)
    (fun s _ => carmonPhi_kernel_le_polynomial s)
  rw [carmonPhi_polynomial_integral] at h
  norm_num at h ⊢
  exact h

theorem carmonPhi_half_increment_lt : carmonPhi (1 / 2) - carmonPhi 0 < (99 / 125 : ℝ) := by
  rw [carmonPhi_sub]
  calc
    _ ≤ Real.sqrt (Real.exp 1) * (1843 / 3840 : ℝ) :=
      mul_le_mul_of_nonneg_left carmonPhi_half_integral_bound (Real.sqrt_nonneg _)
    _ < (33 / 20 : ℝ) * (1843 / 3840) :=
      mul_lt_mul_of_pos_right carmonPhi_sqrt_exp_one_lt (by norm_num)
    _ < 99 / 125 := by norm_num

theorem carmonPhi_neg_half_increment_lt :
    carmonPhi 0 - carmonPhi (-1 / 2) < (99 / 125 : ℝ) := by
  rw [carmonPhi_sub]
  calc
    _ ≤ Real.sqrt (Real.exp 1) * (1843 / 3840 : ℝ) :=
      mul_le_mul_of_nonneg_left carmonPhi_neg_half_integral_bound (Real.sqrt_nonneg _)
    _ < (33 / 20 : ℝ) * (1843 / 3840) :=
      mul_lt_mul_of_pos_right carmonPhi_sqrt_exp_one_lt (by norm_num)
    _ < 99 / 125 := by norm_num

/-- The manuscript's `0.792` bound, uniformly on the closed half-unit window. -/
theorem carmonPhi_local_increment_abs_lt {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |carmonPhi t - carmonPhi 0| < (99 / 125 : ℝ) := by
  obtain ⟨hleft, hright⟩ := abs_le.mp ht
  apply abs_lt.mpr
  constructor
  · have h := strictMono_carmonPhi.monotone hleft
    have hb := carmonPhi_neg_half_increment_lt
    linarith
  · have h := strictMono_carmonPhi.monotone hright
    have hb := carmonPhi_half_increment_lt
    linarith

/-- The two exact brackets in `q_k` are positive for `κ = 1`. This discharges
the Φ positivity premise used by `GateSupport.chainGateTerm_zero_iff`. -/
theorem carmonPhi_correction_brackets_pos {t : ℝ} (ht : |t| < 1 / 2) :
    0 < carmonPhi t - carmonPhi 0 + 1 ∧
      0 < carmonPhi 0 - carmonPhi (-t) + 1 := by
  have h := abs_lt.mp (carmonPhi_local_increment_abs_lt ht.le)
  have hn := abs_lt.mp (carmonPhi_local_increment_abs_lt
    (t := -t) (by simpa using ht.le))
  constructor <;> linarith

end

theorem abs_deriv_carmonPhi_le (t : ℝ) : |deriv carmonPhi t| ≤ (33 / 20 : ℝ) := by
  rw [abs_of_pos (deriv_carmonPhi_pos t), deriv_carmonPhi]
  have he : Real.exp (-t ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  calc
    _ ≤ Real.sqrt (Real.exp 1) * 1 :=
      mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
    _ ≤ 33 / 20 := by simpa using carmonPhi_sqrt_exp_one_lt.le

theorem abs_second_deriv_carmonPhi_le_one (t : ℝ) :
    |deriv (deriv carmonPhi) t| ≤ 1 := by
  rw [second_deriv_carmonPhi]
  have he : (Real.exp (-t ^ 2 / 2)) ^ 2 = Real.exp (-t ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsq : (-t * Real.sqrt (Real.exp 1) * Real.exp (-t ^ 2 / 2)) ^ 2 =
      Real.exp 1 * (t ^ 2 * Real.exp (-t ^ 2)) := by
    calc
      _ = t ^ 2 * (Real.sqrt (Real.exp 1)) ^ 2 * (Real.exp (-t ^ 2 / 2)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Real.exp_pos 1).le, he]; ring
  apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [sq_abs, hsq]
  calc
    _ ≤ Real.exp 1 * Real.exp (-1) :=
      mul_le_mul_of_nonneg_left (Real.mul_exp_neg_le_exp_neg_one (t ^ 2)) (Real.exp_pos 1).le
    _ = (1 : ℝ) ^ 2 := by rw [Real.exp_neg]; field_simp [(Real.exp_pos 1).ne']


end HeavyTailedNoise
