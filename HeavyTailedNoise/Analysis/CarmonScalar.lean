import Mathlib

/-!
Scalar functions for the Carmon chain in the frozen gated Haar construction.
The threshold is exactly `1/2`; no surrogate transition function is used.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace HeavyTailedNoise

/-- The Carmon cutoff before the affine change of variables. -/
def carmonPsiBase (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else Real.exp (1 - u⁻¹ ^ 2)

/-- `Ψ(t)=0` for `t≤1/2`, and `exp(1-(2t-1)⁻²)` otherwise. -/
def carmonPsi (t : ℝ) : ℝ := carmonPsiBase (2 * t - 1)

lemma carmonPsiBase_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    carmonPsiBase u = 0 := by simp [carmonPsiBase, hu]

lemma carmonPsiBase_eq_exp_of_pos {u : ℝ} (hu : 0 < u) :
    carmonPsiBase u = Real.exp (1 - u⁻¹ ^ 2) := by
  simp [carmonPsiBase, not_le.mpr hu]

lemma carmonPsiBase_nonneg (u : ℝ) : 0 ≤ carmonPsiBase u := by
  rcases le_or_gt u 0 with hu | hu
  · simp [carmonPsiBase_zero_of_nonpos hu]
  · exact le_of_lt (by rw [carmonPsiBase_eq_exp_of_pos hu]; exact Real.exp_pos _)

lemma carmonPsiBase_pos_of_pos {u : ℝ} (hu : 0 < u) :
    0 < carmonPsiBase u := by
  rw [carmonPsiBase_eq_exp_of_pos hu]
  exact Real.exp_pos _

lemma carmonPsi_zero_of_le {t : ℝ} (ht : t ≤ 1 / 2) :
    carmonPsi t = 0 := by
  unfold carmonPsi
  apply carmonPsiBase_zero_of_nonpos
  linarith

lemma carmonPsi_eq_exp_of_gt {t : ℝ} (ht : 1 / 2 < t) :
    carmonPsi t = Real.exp (1 - (2 * t - 1)⁻¹ ^ 2) := by
  unfold carmonPsi
  apply carmonPsiBase_eq_exp_of_pos
  linarith

lemma carmonPsi_nonneg (t : ℝ) : 0 ≤ carmonPsi t :=
  carmonPsiBase_nonneg _

lemma carmonPsi_pos_of_gt {t : ℝ} (ht : 1 / 2 < t) :
    0 < carmonPsi t := by
  unfold carmonPsi
  apply carmonPsiBase_pos_of_pos
  linarith

lemma carmonPsi_one : carmonPsi 1 = 1 := by
  rw [carmonPsi_eq_exp_of_gt (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num

/-- Strictly below the threshold, `Ψ` is identically zero on an open neighborhood. -/
lemma carmonPsi_eventuallyEq_zero_of_lt {t : ℝ} (ht : t < 1 / 2) :
    carmonPsi =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact carmonPsi_zero_of_le hs.le

lemma carmonPsi_deriv_zero_of_lt {t : ℝ} (ht : t < 1 / 2) :
    deriv carmonPsi t = 0 := by
  have h := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    (carmonPsi_eventuallyEq_zero_of_lt ht)
  exact h.deriv

lemma carmonPsi_second_deriv_zero_of_lt {t : ℝ} (ht : t < 1 / 2) :
    deriv (deriv carmonPsi) t = 0 := by
  have heq : deriv carmonPsi =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact carmonPsi_deriv_zero_of_lt hs
  have h := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq
  exact h.deriv

/-- Gaussian rapid decay after inversion: every inverse power is dominated by
`exp (-u⁻²)` as `u ↓ 0`. This is the analytic input for threshold flatness. -/
lemma carmonPsiBase_flat_limit (n : ℕ) :
    Tendsto (fun u : ℝ => u⁻¹ ^ n * Real.exp (-(u⁻¹) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have htop : Tendsto
      (fun v : ℝ => |v| ^ (n : ℝ) * Real.exp (-(1 : ℝ) * v ^ 2))
      atTop (𝓝 (0 : ℝ)) :=
    (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := (1 : ℝ))
      one_pos (n : ℝ)).mono_left (atTop_le_cocompact (α := ℝ))
  have h := htop.comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu_pos : 0 < u := hu
  simp [Function.comp_apply, abs_of_pos (inv_pos.mpr hu_pos),
    Real.rpow_natCast]

/-- The first derivative exists at the joining point. The right secant slope
is an inverse first power times the Gaussian flat factor. -/
lemma hasDerivAt_carmonPsiBase_zero :
    HasDerivAt carmonPsiBase 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have heq : (fun u : ℝ => slope carmonPsiBase 0 u)
        =ᶠ[𝓝[<] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      change u < 0 at hu
      rw [slope_def_field, carmonPsiBase_zero_of_nonpos hu.le,
        carmonPsiBase_zero_of_nonpos le_rfl]
      simp
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  · have heq : (fun u : ℝ => slope carmonPsiBase 0 u)
        =ᶠ[𝓝[>] (0 : ℝ)]
          (fun u => Real.exp 1 *
            (u⁻¹ ^ 1 * Real.exp (-(u⁻¹) ^ 2))) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      change 0 < u at hu
      rw [slope_def_field, carmonPsiBase_eq_exp_of_pos hu,
        carmonPsiBase_zero_of_nonpos le_rfl]
      rw [show 1 - u⁻¹ ^ 2 = 1 + (-(u⁻¹) ^ 2) by ring,
        Real.exp_add]
      simp only [sub_zero, div_eq_mul_inv, pow_one]
      ring
    apply (tendsto_congr' heq).2
    simpa using (carmonPsiBase_flat_limit 1).const_mul (Real.exp 1)

/-- The explicit derivative of the cutoff before the affine change of variables. -/
def carmonPsiBaseFirst (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else 2 * u⁻¹ ^ 3 * Real.exp (1 - u⁻¹ ^ 2)

lemma hasDerivAt_carmonPsiBase_of_pos {u : ℝ} (hu : 0 < u) :
    HasDerivAt carmonPsiBase (carmonPsiBaseFirst u) u := by
  have hcore : HasDerivAt (fun v : ℝ => 1 - v⁻¹ ^ 2) (2 * u⁻¹ ^ 3) u := by
    have h := ((hasDerivAt_inv hu.ne').pow 2).const_sub (1 : ℝ)
    convert h using 1
    norm_num [inv_pow] <;> ring
  have hlocal : carmonPsiBase =ᶠ[𝓝 u]
      (fun v : ℝ => Real.exp (1 - v⁻¹ ^ 2)) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact carmonPsiBase_eq_exp_of_pos hv
  convert (hcore.exp).congr_of_eventuallyEq hlocal using 1
  unfold carmonPsiBaseFirst
  simp [not_le.mpr hu]
  ring

lemma hasDerivAt_carmonPsiBase_of_neg {u : ℝ} (hu : u < 0) :
    HasDerivAt carmonPsiBase (carmonPsiBaseFirst u) u := by
  have hlocal : carmonPsiBase =ᶠ[𝓝 u] (fun _ : ℝ => 0) := by
    filter_upwards [Iio_mem_nhds hu] with v hv
    exact carmonPsiBase_zero_of_nonpos hv.le
  convert (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hlocal using 1
  simp [carmonPsiBaseFirst, hu.le]

lemma hasDerivAt_carmonPsiBase (u : ℝ) :
    HasDerivAt carmonPsiBase (carmonPsiBaseFirst u) u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · exact hasDerivAt_carmonPsiBase_of_neg hu
  · simpa [carmonPsiBaseFirst] using hasDerivAt_carmonPsiBase_zero
  · exact hasDerivAt_carmonPsiBase_of_pos hu

lemma deriv_carmonPsiBase (u : ℝ) :
    deriv carmonPsiBase u = carmonPsiBaseFirst u :=
  (hasDerivAt_carmonPsiBase u).deriv

lemma carmonPsiBaseFirst_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    carmonPsiBaseFirst u = 0 := by simp [carmonPsiBaseFirst, hu]

lemma carmonPsiBaseFirst_eq_of_pos {u : ℝ} (hu : 0 < u) :
    carmonPsiBaseFirst u = 2 * u⁻¹ ^ 3 * Real.exp (1 - u⁻¹ ^ 2) := by
  simp [carmonPsiBaseFirst, not_le.mpr hu]

/-- The second derivative exists at the joining point; its right secant
slope is controlled by the already proved inverse fourth-power limit. -/
lemma hasDerivAt_carmonPsiBaseFirst_zero :
    HasDerivAt carmonPsiBaseFirst 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have heq : (fun u : ℝ => slope carmonPsiBaseFirst 0 u)
        =ᶠ[𝓝[<] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      change u < 0 at hu
      rw [slope_def_field, carmonPsiBaseFirst_zero_of_nonpos hu.le,
        carmonPsiBaseFirst_zero_of_nonpos le_rfl]
      simp
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  · have heq : (fun u : ℝ => slope carmonPsiBaseFirst 0 u)
        =ᶠ[𝓝[>] (0 : ℝ)]
          (fun u => (2 * Real.exp 1) *
            (u⁻¹ ^ 4 * Real.exp (-(u⁻¹) ^ 2))) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      change 0 < u at hu
      rw [slope_def_field, carmonPsiBaseFirst_eq_of_pos hu,
        carmonPsiBaseFirst_zero_of_nonpos le_rfl]
      rw [show 1 - u⁻¹ ^ 2 = 1 + (-(u⁻¹) ^ 2) by ring,
        Real.exp_add]
      simp only [sub_zero, div_eq_mul_inv]
      ring
    apply (tendsto_congr' heq).2
    simpa using (carmonPsiBase_flat_limit 4).const_mul (2 * Real.exp 1)

lemma second_deriv_carmonPsiBase_zero :
    deriv (deriv carmonPsiBase) 0 = 0 := by
  have hfun : deriv carmonPsiBase = carmonPsiBaseFirst := by
    funext u
    exact deriv_carmonPsiBase u
  rw [hfun]
  exact hasDerivAt_carmonPsiBaseFirst_zero.deriv

/-- The explicit second derivative of the cutoff before rescaling. -/
def carmonPsiBaseSecond (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else
    (4 * u⁻¹ ^ 6 - 6 * u⁻¹ ^ 4) * Real.exp (1 - u⁻¹ ^ 2)

lemma carmonPsiBaseSecond_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    carmonPsiBaseSecond u = 0 := by simp [carmonPsiBaseSecond, hu]

lemma carmonPsiBaseSecond_eq_of_pos {u : ℝ} (hu : 0 < u) :
    carmonPsiBaseSecond u =
      (4 * u⁻¹ ^ 6 - 6 * u⁻¹ ^ 4) * Real.exp (1 - u⁻¹ ^ 2) := by
  simp [carmonPsiBaseSecond, not_le.mpr hu]

lemma hasDerivAt_carmonPsiBaseFirst_of_pos {u : ℝ} (hu : 0 < u) :
    HasDerivAt carmonPsiBaseFirst (carmonPsiBaseSecond u) u := by
  have hlocal : carmonPsiBaseFirst =ᶠ[𝓝 u]
      (fun v : ℝ => 2 * v⁻¹ ^ 3 * carmonPsiBase v) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    rw [carmonPsiBaseFirst_eq_of_pos hv, carmonPsiBase_eq_exp_of_pos hv]
  have h := (((hasDerivAt_inv hu.ne').pow 3).const_mul 2).mul
    (hasDerivAt_carmonPsiBase_of_pos hu)
  convert h.congr_of_eventuallyEq hlocal using 1
  rw [carmonPsiBaseSecond_eq_of_pos hu, carmonPsiBase_eq_exp_of_pos hu,
    carmonPsiBaseFirst_eq_of_pos hu]
  norm_num [inv_pow] <;> ring

lemma hasDerivAt_carmonPsiBaseFirst_of_neg {u : ℝ} (hu : u < 0) :
    HasDerivAt carmonPsiBaseFirst (carmonPsiBaseSecond u) u := by
  have hlocal : carmonPsiBaseFirst =ᶠ[𝓝 u] (fun _ : ℝ => 0) := by
    filter_upwards [Iio_mem_nhds hu] with v hv
    exact carmonPsiBaseFirst_zero_of_nonpos hv.le
  convert (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hlocal using 1
  simp [carmonPsiBaseSecond, hu.le]

lemma hasDerivAt_carmonPsiBaseFirst (u : ℝ) :
    HasDerivAt carmonPsiBaseFirst (carmonPsiBaseSecond u) u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · exact hasDerivAt_carmonPsiBaseFirst_of_neg hu
  · simpa [carmonPsiBaseSecond] using hasDerivAt_carmonPsiBaseFirst_zero
  · exact hasDerivAt_carmonPsiBaseFirst_of_pos hu

lemma deriv_carmonPsiBaseFirst (u : ℝ) :
    deriv carmonPsiBaseFirst u = carmonPsiBaseSecond u :=
  (hasDerivAt_carmonPsiBaseFirst u).deriv

lemma second_deriv_carmonPsiBase (u : ℝ) :
    deriv (deriv carmonPsiBase) u = carmonPsiBaseSecond u := by
  have hfun : deriv carmonPsiBase = carmonPsiBaseFirst := by
    funext v
    exact deriv_carmonPsiBase v
  rw [hfun]
  exact deriv_carmonPsiBaseFirst u

lemma continuousAt_carmonPsiBaseSecond_zero :
    ContinuousAt carmonPsiBaseSecond 0 := by
  have hleft : Tendsto carmonPsiBaseSecond (𝓝[<] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have heq : carmonPsiBaseSecond =ᶠ[𝓝[<] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      change u < 0 at hu
      exact carmonPsiBaseSecond_zero_of_nonpos hu.le
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  have hright : Tendsto carmonPsiBaseSecond (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have heq : carmonPsiBaseSecond =ᶠ[𝓝[>] (0 : ℝ)]
        (fun u => (4 * Real.exp 1) *
          (u⁻¹ ^ 6 * Real.exp (-(u⁻¹) ^ 2)) -
          (6 * Real.exp 1) *
          (u⁻¹ ^ 4 * Real.exp (-(u⁻¹) ^ 2))) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      change 0 < u at hu
      rw [carmonPsiBaseSecond_eq_of_pos hu,
        show 1 - u⁻¹ ^ 2 = 1 + (-(u⁻¹) ^ 2) by ring,
        Real.exp_add]
      ring
    apply (tendsto_congr' heq).2
    simpa using ((carmonPsiBase_flat_limit 6).const_mul (4 * Real.exp 1)).sub
      ((carmonPsiBase_flat_limit 4).const_mul (6 * Real.exp 1))
  apply continuousAt_iff_continuous_left'_right'.mpr
  constructor
  · simpa [ContinuousWithinAt, carmonPsiBaseSecond_zero_of_nonpos le_rfl] using hleft
  · simpa [ContinuousWithinAt, carmonPsiBaseSecond_zero_of_nonpos le_rfl] using hright

theorem continuous_carmonPsiBaseSecond : Continuous carmonPsiBaseSecond := by
  apply continuous_iff_continuousAt.mpr
  intro u
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have hlocal : carmonPsiBaseSecond =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      exact carmonPsiBaseSecond_zero_of_nonpos hv.le
    exact continuousAt_const.congr_of_eventuallyEq hlocal
  · exact continuousAt_carmonPsiBaseSecond_zero
  · have hlocal : carmonPsiBaseSecond =ᶠ[𝓝 u]
        (fun v : ℝ =>
          (4 * v⁻¹ ^ 6 - 6 * v⁻¹ ^ 4) * Real.exp (1 - v⁻¹ ^ 2)) := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact carmonPsiBaseSecond_eq_of_pos hv
    have hcont : ContinuousAt (fun v : ℝ =>
        (4 * v⁻¹ ^ 6 - 6 * v⁻¹ ^ 4) * Real.exp (1 - v⁻¹ ^ 2)) u := by
      fun_prop (disch := simp [hu.ne'])
    exact hcont.congr_of_eventuallyEq hlocal

theorem contDiff_carmonPsiBase_two : ContDiff ℝ 2 carmonPsiBase := by
  have hF : Differentiable ℝ carmonPsiBase :=
    fun u => (hasDerivAt_carmonPsiBase u).differentiableAt
  have hD₁ : Differentiable ℝ carmonPsiBaseFirst :=
    fun u => (hasDerivAt_carmonPsiBaseFirst u).differentiableAt
  have hFderiv : deriv carmonPsiBase = carmonPsiBaseFirst := by
    funext u
    exact deriv_carmonPsiBase u
  have hsecond : deriv (deriv carmonPsiBase) = carmonPsiBaseSecond := by
    funext u
    exact second_deriv_carmonPsiBase u
  have htwo : iteratedDeriv 2 carmonPsiBase = deriv (deriv carmonPsiBase) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro m hm
    have hmNat : m ≤ 2 := by exact_mod_cast hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simpa [iteratedDeriv_zero] using hF.continuous
    · simpa [iteratedDeriv_one, hFderiv] using hD₁.continuous
    · simpa [htwo, hsecond] using continuous_carmonPsiBaseSecond
  · intro m hm
    have hmNat : m < 2 := by exact_mod_cast hm
    have hcases : m = 0 ∨ m = 1 := by omega
    rcases hcases with rfl | rfl
    · simpa [iteratedDeriv_zero] using hF
    · simpa [iteratedDeriv_one, hFderiv] using hD₁

theorem contDiff_carmonPsi_two : ContDiff ℝ 2 carmonPsi := by
  unfold carmonPsi
  exact contDiff_carmonPsiBase_two.comp (by fun_prop)

lemma hasDerivAt_carmonPsi (t : ℝ) :
    HasDerivAt carmonPsi (2 * carmonPsiBaseFirst (2 * t - 1)) t := by
  have hlin : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using (hasDerivAt_const_mul (x := t) (2 : ℝ)).sub_const 1
  have h := (hasDerivAt_carmonPsiBase (2 * t - 1)).comp t hlin
  unfold carmonPsi
  convert h using 1 <;> (try simp [Function.comp_def]) <;> ring

lemma deriv_carmonPsi (t : ℝ) :
    deriv carmonPsi t = 2 * carmonPsiBaseFirst (2 * t - 1) :=
  (hasDerivAt_carmonPsi t).deriv

lemma second_deriv_carmonPsi (t : ℝ) :
    deriv (deriv carmonPsi) t = 4 * carmonPsiBaseSecond (2 * t - 1) := by
  have hfun : deriv carmonPsi =
      (fun s : ℝ => 2 * carmonPsiBaseFirst (2 * s - 1)) := by
    funext s
    exact deriv_carmonPsi s
  rw [hfun]
  have hlin : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using (hasDerivAt_const_mul (x := t) (2 : ℝ)).sub_const 1
  have h := ((hasDerivAt_carmonPsiBaseFirst (2 * t - 1)).comp t hlin).const_mul 2
  have h' : HasDerivAt (fun s : ℝ => 2 * carmonPsiBaseFirst (2 * s - 1))
      (2 * (carmonPsiBaseSecond (2 * t - 1) * 2)) t := by
    simpa only [Function.comp_def] using h
  convert h'.deriv using 1 <;> ring

lemma carmonPsi_half : carmonPsi (1 / 2) = 0 := by
  exact carmonPsi_zero_of_le le_rfl

lemma deriv_carmonPsi_half : deriv carmonPsi (1 / 2) = 0 := by
  rw [deriv_carmonPsi]
  norm_num [carmonPsiBaseFirst]

lemma second_deriv_carmonPsi_half : deriv (deriv carmonPsi) (1 / 2) = 0 := by
  rw [second_deriv_carmonPsi]
  norm_num [carmonPsiBaseSecond]

theorem deriv_carmonPsi_zero_of_le {t : ℝ} (ht : t ≤ 1 / 2) : deriv carmonPsi t = 0 := by
  rw [deriv_carmonPsi, carmonPsiBaseFirst_zero_of_nonpos (by linarith)]
  simp

theorem second_deriv_carmonPsi_zero_of_le {t : ℝ} (ht : t ≤ 1 / 2) :
    deriv (deriv carmonPsi) t = 0 := by
  rw [second_deriv_carmonPsi, carmonPsiBaseSecond_zero_of_nonpos (by linarith)]
  simp


end HeavyTailedNoise
