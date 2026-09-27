import HeavyTailedNoise.Model.Basic

/-!
Algebra at the gated frontier. The exact cancellation is the deterministic
identity used when the next coordinate lies in the flat selector region and
the residual gate is fully open. It does not by itself establish prefix
locality of the full objective.
-/

namespace HeavyTailedNoise

open scoped Topology
open Filter

noncomputable section

/-- The polynomial used in each gate selector on its transition interval. -/
def smoothstepPolynomial (t : ℝ) : ℝ :=
  t ^ 3 * (6 * t ^ 2 - 15 * t + 10)

/-- The manuscript's quintic step, constant outside `[0, 1]`. -/
def smoothstep (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else smoothstepPolynomial t

theorem smoothstep_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : smoothstep t = 0 := by
  simp [smoothstep, ht]

theorem smoothstep_one_of_one_le {t : ℝ} (ht : 1 ≤ t) : smoothstep t = 1 := by
  have hpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  simp [smoothstep, not_le.mpr hpos, ht]

theorem smoothstepPolynomial_sub_one (t : ℝ) :
    smoothstepPolynomial t - 1 = (t - 1) ^ 3 * (6 * t ^ 2 + 3 * t + 1) := by
  unfold smoothstepPolynomial
  ring

theorem smoothstepPolynomial_zero : smoothstepPolynomial 0 = 0 := by
  norm_num [smoothstepPolynomial]

theorem smoothstepPolynomial_one : smoothstepPolynomial 1 = 1 := by
  norm_num [smoothstepPolynomial]

theorem continuous_smoothstepPolynomial : Continuous smoothstepPolynomial := by
  unfold smoothstepPolynomial
  fun_prop

theorem continuous_smoothstep : Continuous smoothstep := by
  have hinner : Continuous (fun t : ℝ =>
      if 1 ≤ t then (1 : ℝ) else smoothstepPolynomial t) := by
    apply Continuous.if
    · intro t ht
      change t ∈ frontier (Set.Ici 1) at ht
      have h : t = 1 := by simpa only [frontier_Ici,
        Set.mem_singleton_iff] using ht
      subst t
      exact smoothstepPolynomial_one.symm
    · exact continuous_const
    · exact continuous_smoothstepPolynomial
  unfold smoothstep
  apply Continuous.if
  · intro t ht
    change t ∈ frontier (Set.Iic 0) at ht
    have h : t = 0 := by simpa only [frontier_Iic,
      Set.mem_singleton_iff] using ht
    subst t
    norm_num [smoothstepPolynomial]
  · exact continuous_const
  · exact hinner

theorem hasDerivAt_smoothstep_zero : HasDerivAt smoothstep 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have heq : (fun t : ℝ => slope smoothstep 0 t) =ᶠ[𝓝[<] (0 : ℝ)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [slope_def_field, smoothstep_zero_of_nonpos ht.le,
        smoothstep_zero_of_nonpos le_rfl]
      simp
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  · have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds
    have heq : (fun t : ℝ => slope smoothstep 0 t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t => t ^ 2 * (6 * t ^ 2 - 15 * t + 10)) := by
      filter_upwards [self_mem_nhdsWithin, hlt] with t ht0 ht1
      change 0 < t at ht0
      have hs : smoothstep t = smoothstepPolynomial t := by
        simp [smoothstep, not_le.mpr ht0, not_le.mpr ht1]
      rw [slope_def_field, hs, smoothstep_zero_of_nonpos le_rfl]
      unfold smoothstepPolynomial
      field_simp [ne_of_gt ht0]
      ring
    have hc : ContinuousAt (fun t : ℝ =>
        t ^ 2 * (6 * t ^ 2 - 15 * t + 10)) 0 := by fun_prop
    have hlim : Tendsto (fun t : ℝ =>
        t ^ 2 * (6 * t ^ 2 - 15 * t + 10)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact (tendsto_congr' heq).2 hlim

theorem deriv_smoothstep_zero : deriv smoothstep 0 = 0 :=
  hasDerivAt_smoothstep_zero.deriv

theorem hasDerivAt_smoothstep_one : HasDerivAt smoothstep 0 1 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have hgt : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds
    have heq : (fun t : ℝ => slope smoothstep 1 t) =ᶠ[𝓝[<] (1 : ℝ)]
        (fun t => (t - 1) ^ 2 * (6 * t ^ 2 + 3 * t + 1)) := by
      filter_upwards [self_mem_nhdsWithin, hgt] with t ht1 ht0
      change t < 1 at ht1
      have hs : smoothstep t = smoothstepPolynomial t := by
        simp [smoothstep, not_le.mpr ht0, not_le.mpr ht1]
      rw [slope_def_field, hs, smoothstep_one_of_one_le le_rfl,
        smoothstepPolynomial_sub_one]
      field_simp [sub_ne_zero.mpr (ne_of_lt ht1)]
    have hc : ContinuousAt (fun t : ℝ =>
        (t - 1) ^ 2 * (6 * t ^ 2 + 3 * t + 1)) 1 := by fun_prop
    have hlim : Tendsto (fun t : ℝ =>
        (t - 1) ^ 2 * (6 * t ^ 2 + 3 * t + 1)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact (tendsto_congr' heq).2 hlim
  · have heq : (fun t : ℝ => slope smoothstep 1 t) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [slope_def_field, smoothstep_one_of_one_le ht.le,
        smoothstep_one_of_one_le le_rfl]
      simp
    exact (tendsto_congr' heq).2 tendsto_const_nhds

theorem deriv_smoothstep_one : deriv smoothstep 1 = 0 :=
  hasDerivAt_smoothstep_one.deriv

theorem hasDerivAt_smoothstepPolynomial (x : ℝ) :
    HasDerivAt smoothstepPolynomial (30 * x ^ 2 * (x - 1) ^ 2) x := by
  have hfun : smoothstepPolynomial =
      (fun t : ℝ => 6 * t ^ 5 - 15 * t ^ 4 + 10 * t ^ 3) := by
    funext t
    unfold smoothstepPolynomial
    ring
  have h := ((((hasDerivAt_id x).pow 5).const_mul 6).sub
    (((hasDerivAt_id x).pow 4).const_mul 15)).add
    (((hasDerivAt_id x).pow 3).const_mul 10)
  rw [hfun]
  convert h using 1
  · funext t
    dsimp
  · norm_num <;> ring

theorem hasDerivAt_smoothstep_of_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt smoothstep 0 x := by
  have hlocal : smoothstep =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with t ht
    exact smoothstep_zero_of_nonpos ht.le
  exact (hasDerivAt_const (c := (0 : ℝ)) (x := x)).congr_of_eventuallyEq hlocal

theorem hasDerivAt_smoothstep_of_one_lt {x : ℝ} (hx : 1 < x) :
    HasDerivAt smoothstep 0 x := by
  have hlocal : smoothstep =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    exact smoothstep_one_of_one_le ht.le
  exact (hasDerivAt_const (c := (1 : ℝ)) (x := x)).congr_of_eventuallyEq hlocal

theorem hasDerivAt_smoothstep_of_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt smoothstep (30 * x ^ 2 * (x - 1) ^ 2) x := by
  have hlocal : smoothstep =ᶠ[𝓝 x] smoothstepPolynomial := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Set.Ioo (0 : ℝ) 1 from
      ⟨hx0, hx1⟩)] with t ht
    simp [smoothstep, not_le.mpr ht.1, not_le.mpr ht.2]
  exact (hasDerivAt_smoothstepPolynomial x).congr_of_eventuallyEq hlocal

theorem deriv_smoothstep_formula (x : ℝ) :
    deriv smoothstep x =
      if x ≤ 0 then 0 else if 1 ≤ x then 0 else 30 * x ^ 2 * (x - 1) ^ 2 := by
  by_cases hx0 : x ≤ 0
  · rw [if_pos hx0]
    rcases lt_or_eq_of_le hx0 with hneg | hzero
    · exact (hasDerivAt_smoothstep_of_neg hneg).deriv
    · subst x
      exact deriv_smoothstep_zero
  · rw [if_neg hx0]
    by_cases hx1 : 1 ≤ x
    · rw [if_pos hx1]
      rcases lt_or_eq_of_le hx1 with hgt | hone
      · exact (hasDerivAt_smoothstep_of_one_lt hgt).deriv
      · subst x
        exact deriv_smoothstep_one
    · rw [if_neg hx1]
      exact (hasDerivAt_smoothstep_of_Ioo (lt_of_not_ge hx0)
        (lt_of_not_ge hx1)).deriv

theorem hasDerivAt_deriv_smoothstep_zero :
    HasDerivAt (deriv smoothstep) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have heq : (fun t : ℝ => slope (deriv smoothstep) 0 t) =ᶠ[𝓝[<] (0 : ℝ)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change t < 0 at ht
      rw [slope_def_field, deriv_smoothstep_formula t, deriv_smoothstep_zero]
      simp [ht.le]
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  · have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds
    have heq : (fun t : ℝ => slope (deriv smoothstep) 0 t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t => 30 * t * (t - 1) ^ 2) := by
      filter_upwards [self_mem_nhdsWithin, hlt] with t ht0 ht1
      change 0 < t at ht0
      rw [slope_def_field, deriv_smoothstep_formula t, deriv_smoothstep_zero]
      simp only [if_neg (not_le.mpr ht0), if_neg (not_le.mpr ht1)]
      field_simp [ne_of_gt ht0]
      ring
    have hc : ContinuousAt (fun t : ℝ => 30 * t * (t - 1) ^ 2) 0 := by fun_prop
    have hlim : Tendsto (fun t : ℝ => 30 * t * (t - 1) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact (tendsto_congr' heq).2 hlim

theorem second_deriv_smoothstep_zero : deriv (deriv smoothstep) 0 = 0 :=
  hasDerivAt_deriv_smoothstep_zero.deriv

theorem hasDerivAt_deriv_smoothstep_one :
    HasDerivAt (deriv smoothstep) 0 1 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have hgt : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds
    have heq : (fun t : ℝ => slope (deriv smoothstep) 1 t) =ᶠ[𝓝[<] (1 : ℝ)]
        (fun t => 30 * t ^ 2 * (t - 1)) := by
      filter_upwards [self_mem_nhdsWithin, hgt] with t ht1 ht0
      change t < 1 at ht1
      rw [slope_def_field, deriv_smoothstep_formula t, deriv_smoothstep_one]
      simp only [if_neg (not_le.mpr ht0), if_neg (not_le.mpr ht1)]
      field_simp [sub_ne_zero.mpr (ne_of_lt ht1)]
      ring
    have hc : ContinuousAt (fun t : ℝ => 30 * t ^ 2 * (t - 1)) 1 := by fun_prop
    have hlim : Tendsto (fun t : ℝ => 30 * t ^ 2 * (t - 1))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact (tendsto_congr' heq).2 hlim
  · have heq : (fun t : ℝ => slope (deriv smoothstep) 1 t) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 1 < t at ht
      rw [slope_def_field, deriv_smoothstep_formula t, deriv_smoothstep_one]
      simp [ht.le]
    exact (tendsto_congr' heq).2 tendsto_const_nhds

theorem second_deriv_smoothstep_one : deriv (deriv smoothstep) 1 = 0 :=
  hasDerivAt_deriv_smoothstep_one.deriv

theorem continuous_deriv_smoothstep : Continuous (deriv smoothstep) := by
  have hfun : deriv smoothstep = (fun t : ℝ =>
      if t ≤ 0 then 0 else if 1 ≤ t then 0 else 30 * t ^ 2 * (t - 1) ^ 2) := by
    funext t
    exact deriv_smoothstep_formula t
  rw [hfun]
  have hpoly : Continuous (fun t : ℝ => 30 * t ^ 2 * (t - 1) ^ 2) := by fun_prop
  have hinner : Continuous (fun t : ℝ =>
      if 1 ≤ t then (0 : ℝ) else 30 * t ^ 2 * (t - 1) ^ 2) := by
    apply Continuous.if
    · intro t ht
      change t ∈ frontier (Set.Ici 1) at ht
      have h : t = 1 := by simpa only [frontier_Ici,
        Set.mem_singleton_iff] using ht
      subst t
      norm_num
    · exact continuous_const
    · exact hpoly
  apply Continuous.if
  · intro t ht
    change t ∈ frontier (Set.Iic 0) at ht
    have h : t = 0 := by simpa only [frontier_Iic,
      Set.mem_singleton_iff] using ht
    subst t
    norm_num
  · exact continuous_const
  · exact hinner

theorem hasDerivAt_smoothstepFirstPolynomial (x : ℝ) :
    HasDerivAt (fun t : ℝ => 30 * t ^ 2 * (t - 1) ^ 2)
      (60 * x * (x - 1) * (2 * x - 1)) x := by
  have hfun : (fun t : ℝ => 30 * t ^ 2 * (t - 1) ^ 2) =
      (fun t : ℝ => 30 * t ^ 4 - 60 * t ^ 3 + 30 * t ^ 2) := by
    funext t
    ring
  have h := ((((hasDerivAt_id x).pow 4).const_mul 30).sub
    (((hasDerivAt_id x).pow 3).const_mul 60)).add
    (((hasDerivAt_id x).pow 2).const_mul 30)
  rw [hfun]
  convert h using 1
  · funext t
    dsimp
  · norm_num <;> ring

theorem hasDerivAt_deriv_smoothstep_of_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt (deriv smoothstep) 0 x := by
  have hlocal : deriv smoothstep =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with t ht
    change t < 0 at ht
    rw [deriv_smoothstep_formula t]
    simp [ht.le]
  exact (hasDerivAt_const (c := (0 : ℝ)) (x := x)).congr_of_eventuallyEq hlocal

theorem hasDerivAt_deriv_smoothstep_of_one_lt {x : ℝ} (hx : 1 < x) :
    HasDerivAt (deriv smoothstep) 0 x := by
  have hlocal : deriv smoothstep =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
    change 1 < t at ht
    have ht0 : ¬ t ≤ 0 := not_le.mpr (lt_trans zero_lt_one ht)
    rw [deriv_smoothstep_formula t]
    simp [ht0, ht.le]
  exact (hasDerivAt_const (c := (0 : ℝ)) (x := x)).congr_of_eventuallyEq hlocal

theorem hasDerivAt_deriv_smoothstep_of_Ioo {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (deriv smoothstep) (60 * x * (x - 1) * (2 * x - 1)) x := by
  have hlocal : deriv smoothstep =ᶠ[𝓝 x]
      (fun t : ℝ => 30 * t ^ 2 * (t - 1) ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Set.Ioo (0 : ℝ) 1 from
      ⟨hx0, hx1⟩)] with t ht
    rw [deriv_smoothstep_formula t]
    simp [not_le.mpr ht.1, not_le.mpr ht.2]
  exact (hasDerivAt_smoothstepFirstPolynomial x).congr_of_eventuallyEq hlocal

theorem second_deriv_smoothstep_formula (x : ℝ) :
    deriv (deriv smoothstep) x =
      if x ≤ 0 then 0 else if 1 ≤ x then 0 else
        60 * x * (x - 1) * (2 * x - 1) := by
  by_cases hx0 : x ≤ 0
  · rw [if_pos hx0]
    rcases lt_or_eq_of_le hx0 with hneg | hzero
    · exact (hasDerivAt_deriv_smoothstep_of_neg hneg).deriv
    · subst x
      exact second_deriv_smoothstep_zero
  · rw [if_neg hx0]
    by_cases hx1 : 1 ≤ x
    · rw [if_pos hx1]
      rcases lt_or_eq_of_le hx1 with hgt | hone
      · exact (hasDerivAt_deriv_smoothstep_of_one_lt hgt).deriv
      · subst x
        exact second_deriv_smoothstep_one
    · rw [if_neg hx1]
      exact (hasDerivAt_deriv_smoothstep_of_Ioo (lt_of_not_ge hx0)
        (lt_of_not_ge hx1)).deriv

theorem continuous_second_deriv_smoothstep :
    Continuous (deriv (deriv smoothstep)) := by
  have hfun : deriv (deriv smoothstep) = (fun t : ℝ =>
      if t ≤ 0 then 0 else if 1 ≤ t then 0 else
        60 * t * (t - 1) * (2 * t - 1)) := by
    funext t
    exact second_deriv_smoothstep_formula t
  rw [hfun]
  have hpoly : Continuous (fun t : ℝ =>
      60 * t * (t - 1) * (2 * t - 1)) := by fun_prop
  have hinner : Continuous (fun t : ℝ =>
      if 1 ≤ t then (0 : ℝ) else 60 * t * (t - 1) * (2 * t - 1)) := by
    apply Continuous.if
    · intro t ht
      change t ∈ frontier (Set.Ici 1) at ht
      have h : t = 1 := by simpa only [frontier_Ici,
        Set.mem_singleton_iff] using ht
      subst t
      norm_num
    · exact continuous_const
    · exact hpoly
  apply Continuous.if
  · intro t ht
    change t ∈ frontier (Set.Iic 0) at ht
    have h : t = 0 := by simpa only [frontier_Iic,
      Set.mem_singleton_iff] using ht
    subst t
    norm_num
  · exact continuous_const
  · exact hinner

theorem differentiable_smoothstep : Differentiable ℝ smoothstep := by
  intro x
  by_cases hx0 : x ≤ 0
  · rcases lt_or_eq_of_le hx0 with hneg | hzero
    · exact (hasDerivAt_smoothstep_of_neg hneg).differentiableAt
    · subst x
      exact hasDerivAt_smoothstep_zero.differentiableAt
  · by_cases hx1 : 1 ≤ x
    · rcases lt_or_eq_of_le hx1 with hgt | hone
      · exact (hasDerivAt_smoothstep_of_one_lt hgt).differentiableAt
      · subst x
        exact hasDerivAt_smoothstep_one.differentiableAt
    · exact (hasDerivAt_smoothstep_of_Ioo (lt_of_not_ge hx0)
        (lt_of_not_ge hx1)).differentiableAt

theorem differentiable_deriv_smoothstep :
    Differentiable ℝ (deriv smoothstep) := by
  intro x
  by_cases hx0 : x ≤ 0
  · rcases lt_or_eq_of_le hx0 with hneg | hzero
    · exact (hasDerivAt_deriv_smoothstep_of_neg hneg).differentiableAt
    · subst x
      exact hasDerivAt_deriv_smoothstep_zero.differentiableAt
  · by_cases hx1 : 1 ≤ x
    · rcases lt_or_eq_of_le hx1 with hgt | hone
      · exact (hasDerivAt_deriv_smoothstep_of_one_lt hgt).differentiableAt
      · subst x
        exact hasDerivAt_deriv_smoothstep_one.differentiableAt
    · exact (hasDerivAt_deriv_smoothstep_of_Ioo (lt_of_not_ge hx0)
        (lt_of_not_ge hx1)).differentiableAt

theorem contDiff_smoothstep_two : ContDiff ℝ 2 smoothstep := by
  have htwo : iteratedDeriv 2 smoothstep = deriv (deriv smoothstep) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro m hm
    have hmNat : m ≤ 2 := by exact_mod_cast hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simpa [iteratedDeriv_zero] using continuous_smoothstep
    · simpa [iteratedDeriv_one] using continuous_deriv_smoothstep
    · simpa [htwo] using continuous_second_deriv_smoothstep
  · intro m hm
    have hmNat : m < 2 := by exact_mod_cast hm
    have hcases : m = 0 ∨ m = 1 := by omega
    rcases hcases with rfl | rfl
    · simpa [iteratedDeriv_zero] using differentiable_smoothstep
    · simpa [iteratedDeriv_one] using differentiable_deriv_smoothstep

/-- A rescaled selector is identically zero whenever its input is strictly
below the lower threshold, including on a neighborhood of that input. -/
def stepWindow (a w z : ℝ) : ℝ := smoothstep ((|z| - a) / w)

theorem stepWindow_zero_of_abs_lt {a w z : ℝ} (hw : 0 < w) (hz : |z| < a) :
    stepWindow a w z = 0 := by
  apply smoothstep_zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz.le) hw.le

theorem stepWindow_eventually_zero {a w z : ℝ} (hw : 0 < w) (hz : |z| < a) :
    (fun v : ℝ => stepWindow a w v) =ᶠ[nhds z] (fun _ => 0) := by
  have hopen : IsOpen {v : ℝ | |v| < a} := isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds hz] with v hv
  exact stepWindow_zero_of_abs_lt hw hv

/-- The unmodified signed Carmon link between neighboring coordinates. -/
def chainLink (ψ φ : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ψ (-a) * φ (-b) - ψ a * φ b

/-- The correction attached to the same link. -/
def frontierCorrection (ψ φ ω : ℝ → ℝ) (κ a b : ℝ) : ℝ :=
  (ψ a * (φ b - φ 0 + κ) + ψ (-a) * (φ 0 - φ (-b) + κ)) * (1 - ω b)

/-- When the selector is flat zero and the residual gate is fully open,
the next-coordinate dependence cancels exactly. -/
theorem gated_frontier_cancellation
    (ψ φ ω χ : ℝ → ℝ) (κ a b s : ℝ)
    (hω : ω b = 0) (hχ : χ s = 0) :
    chainLink ψ φ a b + (1 - χ s) * frontierCorrection ψ φ ω κ a b =
      ψ a * (κ - φ 0) + ψ (-a) * (φ 0 + κ) := by
  simp only [chainLink, frontierCorrection, hω, hχ]
  ring

/-- Agreement on an open neighborhood, rather than equality at a single
point, is sufficient to transfer equality to gradients. -/
theorem gradients_eq_of_eqOn_open {d : ℕ} {f g : Point d → ℝ}
    {gradf gradg : Point d} {x : Point d} {s : Set (Point d)}
    (hs : IsOpen s) (hx : x ∈ s) (hfg : Set.EqOn f g s)
    (hf : HasGradientAt f gradf x) (hg : HasGradientAt g gradg x) :
    gradf = gradg := by
  have hlocal : g =ᶠ[nhds x] f := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact (hfg hy).symm
  exact (hf.congr_of_eventuallyEq hlocal).unique hg

end

theorem smoothstep_lt_one_of_lt {t : ℝ} (ht : t < 1) : smoothstep t < 1 := by
  by_cases ht0 : t ≤ 0
  · rw [smoothstep_zero_of_nonpos ht0]
    norm_num
  · have htpos : 0 < t := lt_of_not_ge ht0
    have hcube : (t - 1) ^ 3 < 0 := by
      have h := mul_neg_of_pos_of_neg
        (sq_pos_of_ne_zero (sub_ne_zero.mpr ht.ne)) (sub_neg.mpr ht)
      nlinarith
    have hpoly : 0 < 6 * t ^ 2 + 3 * t + 1 := by positivity
    have h := mul_neg_of_neg_of_pos hcube hpoly
    rw [← smoothstepPolynomial_sub_one] at h
    simpa [smoothstep, ht0, not_le.mpr ht] using (sub_neg.mp h)

theorem smoothstep_nonneg (t : ℝ) : 0 ≤ smoothstep t := by
  by_cases h0 : t ≤ 0
  · simp [smoothstep_zero_of_nonpos h0]
  · by_cases h1 : 1 ≤ t
    · simp [smoothstep_one_of_one_le h1]
    · have ht : 0 ≤ t := (lt_of_not_ge h0).le
      have hp : 0 ≤ 6 * t ^ 2 - 15 * t + 10 := by
        nlinarith [sq_nonneg (t - 5 / 4)]
      simpa [smoothstep, h0, h1, smoothstepPolynomial] using
        mul_nonneg (pow_nonneg ht 3) hp

theorem smoothstep_le_one (t : ℝ) : smoothstep t ≤ 1 := by
  by_cases ht : t < 1
  · exact (smoothstep_lt_one_of_lt ht).le
  · simp [smoothstep_one_of_one_le (le_of_not_gt ht)]

/-- Exact `ω₆`, including the original disjoint transition window. -/
theorem abs_deriv_smoothstep_le (t : ℝ) : |deriv smoothstep t| ≤ (15 / 8 : ℝ) := by
  rw [deriv_smoothstep_formula]
  split_ifs with h0 h1
  · norm_num
  · norm_num
  · have ht0 : 0 ≤ t := (lt_of_not_ge h0).le
    have ht1 : t ≤ 1 := (lt_of_not_ge h1).le
    have hx : 0 ≤ t * (1 - t) := mul_nonneg ht0 (sub_nonneg.mpr ht1)
    have hxle : t * (1 - t) ≤ (1 / 4 : ℝ) := by
      nlinarith [sq_nonneg (t - 1 / 2)]
    have hs := (sq_le_sq₀ hx (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hxle
    rw [abs_of_nonneg (by positivity : 0 ≤ 30 * t ^ 2 * (t - 1) ^ 2)]
    nlinarith


end HeavyTailedNoise
