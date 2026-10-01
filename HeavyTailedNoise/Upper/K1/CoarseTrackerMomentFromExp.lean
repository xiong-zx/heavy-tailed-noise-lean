import HeavyTailedNoise.Upper.K1.CoarseTrackerShiftedLyapunov
import Mathlib.Analysis.MeanInequalitiesPow

/-!
Scalar step from the shifted exponential tracker bound to every moment
order `0 ≤ p ≤ 2`.  Applying it only to the positive excursion beyond
`ρ₁+b+C` retains the heavy-tailed initial `p`-moment separately.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped NNReal

noncomputable section

/-- The polynomial cost of a nonnegative excursion is controlled by its
exponential weight with an absolute constant for all `0 ≤ p ≤ 2`. -/
theorem rpow_le_five_exp_of_nonneg {p z : ℝ}
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2) (hz : 0 ≤ z) :
    z ^ p ≤ 5 * Real.exp z := by
  have hExp : 0 ≤ Real.exp z := (Real.exp_pos z).le
  by_cases hsmall : z ≤ 1
  · have hpow : z ^ p ≤ 1 := Real.rpow_le_one hz hsmall hp0
    have hone : 1 ≤ Real.exp z := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hz
    nlinarith
  · have hlarge : 1 ≤ z := by linarith
    have hpow : z ^ p ≤ z ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlarge hp2
    have hhalf : z / 2 ≤ Real.exp (z / 2) := by
      linarith [Real.add_one_le_exp (z / 2)]
    have hhalf0 : 0 ≤ z / 2 := by positivity
    have hsq : (z / 2) ^ 2 ≤ Real.exp (z / 2) ^ 2 :=
      pow_le_pow_left₀ hhalf0 hhalf 2
    have hexpSq : Real.exp (z / 2) ^ 2 = Real.exp z := by
      calc
        Real.exp (z / 2) ^ 2 =
            Real.exp (z / 2) * Real.exp (z / 2) := by ring
        _ = Real.exp (z / 2 + z / 2) := (Real.exp_add _ _).symm
        _ = Real.exp z := by congr 1; ring
    have hsquare : z ^ 2 ≤ 4 * Real.exp z := by
      rw [hexpSq] at hsq
      nlinarith
    have hpowNat : z ^ p ≤ z ^ 2 := by
      simpa only [Real.rpow_two] using hpow
    calc
      z ^ p ≤ z ^ 2 := hpowNat
      _ ≤ 4 * Real.exp z := hsquare
      _ ≤ 5 * Real.exp z := by nlinarith [Real.exp_pos z]

/-- A shifted exponential integral controls the positive excursion's
`p`-moment at the correct scale `lam^{-p}`.  The variable `X` may be negative. -/
theorem positivePart_rpow_integrable_and_integral_le_of_exp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X)
    (p lam K : ℝ) (hp0 : 0 < p) (hp2 : p ≤ 2)
    (hlam : 0 < lam)
    (hExpInt : Integrable (fun ω => Real.exp (lam * X ω)) μ)
    (hExp : (∫ ω, Real.exp (lam * X ω) ∂μ) ≤ K) :
    Integrable (fun ω => (max (X ω) 0) ^ p) μ ∧
      lam ^ p * (∫ ω, (max (X ω) 0) ^ p ∂μ) ≤ 5 * K := by
  let Y : Ω → ℝ := fun ω => (max (X ω) 0) ^ p
  have hYMeas : Measurable Y := by
    dsimp [Y]
    fun_prop
  have hdom (ω : Ω) : lam ^ p * Y ω ≤ 5 * Real.exp (lam * X ω) := by
    by_cases hω : 0 ≤ X ω
    · have hz : 0 ≤ lam * X ω := mul_nonneg hlam.le hω
      have hscalar := rpow_le_five_exp_of_nonneg hp0.le hp2 hz
      rw [Real.mul_rpow hlam.le hω] at hscalar
      simpa only [Y, max_eq_left hω] using hscalar
    · have hneg : X ω < 0 := lt_of_not_ge hω
      have hzero : Y ω = 0 := by
        simp [Y, max_eq_right hneg.le, Real.zero_rpow (ne_of_gt hp0)]
      rw [hzero, mul_zero]
      positivity
  have hYnonneg (ω : Ω) : 0 ≤ Y ω :=
    Real.rpow_nonneg (le_max_right _ _) _
  have hYInt : Integrable Y μ := by
    have hbound (ω : Ω) : ‖Y ω‖ ≤
        (5 * lam ^ (-p)) * Real.exp (lam * X ω) := by
      have hlampow : 0 < lam ^ p := Real.rpow_pos_of_pos hlam _
      have hscale : lam ^ p * Y ω ≤ 5 * Real.exp (lam * X ω) := hdom ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hYnonneg ω)]
      have hinv : lam ^ (-p) = (lam ^ p)⁻¹ := by
        rw [← Real.rpow_neg hlam.le]
      calc
        Y ω = (lam ^ p)⁻¹ * (lam ^ p * Y ω) := by
          field_simp [ne_of_gt hlampow]
        _ ≤ (lam ^ p)⁻¹ * (5 * Real.exp (lam * X ω)) :=
          mul_le_mul_of_nonneg_left hscale (inv_nonneg.mpr hlampow.le)
        _ = (5 * lam ^ (-p)) * Real.exp (lam * X ω) := by
          rw [hinv]
          ring
    exact Integrable.mono' (hExpInt.const_mul (5 * lam ^ (-p)))
      hYMeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hleft :
      (∫ ω, lam ^ p * Y ω ∂μ) ≤
        ∫ ω, 5 * Real.exp (lam * X ω) ∂μ := by
    exact integral_mono (hYInt.const_mul _) (hExpInt.const_mul 5) hdom
  rw [integral_const_mul, integral_const_mul] at hleft
  exact ⟨hYInt,
    hleft.trans (mul_le_mul_of_nonneg_left hExp (by norm_num))⟩

/-- A two-term `p`-power bound with a numerical coefficient uniform over
`1 ≤ p ≤ 2`. -/
theorem add_rpow_le_two_sum {p a b : ℝ}
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ p ≤ 2 * (a ^ p + b ^ p) := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have hbase := NNReal.rpow_add_le_mul_rpow_add_rpow a b hp1
  have hcoef : (2 : ℝ≥0) ^ (p - 1) ≤ 2 := by
    have hexp : p - 1 ≤ 1 := by linarith
    simpa only [NNReal.rpow_one] using
      (NNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ≥0) ≤ 2) hexp)
  exact_mod_cast hbase.trans
    (mul_le_mul_of_nonneg_right hcoef (by positivity))

/-- Separate a nonnegative initial error, deterministic overshoot, and
positive shifted excursion without losing the physical scale. -/
theorem tracker_rpow_le_initial_overshoot_excursion
    {p initial current overshoot : ℝ}
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hinit : 0 ≤ initial) (hcurrent : 0 ≤ current)
    (hover : 0 ≤ overshoot) :
    current ^ p ≤
      4 * (initial ^ p + overshoot ^ p +
        (max (current - initial - overshoot) 0) ^ p) := by
  let y := max (current - initial - overshoot) 0
  have hy : 0 ≤ y := le_max_right _ _
  have hpoint : current ≤ (initial + overshoot) + y := by
    dsimp [y]
    linarith [le_max_left (current - initial - overshoot) 0]
  have hmono : current ^ p ≤ ((initial + overshoot) + y) ^ p :=
    Real.rpow_le_rpow hcurrent hpoint (by linarith : 0 ≤ p)
  have hfirst := add_rpow_le_two_sum hp1 hp2 (add_nonneg hinit hover) hy
  have hsecond := add_rpow_le_two_sum hp1 hp2 hinit hover
  have hYp : 0 ≤ y ^ p := Real.rpow_nonneg hy _
  calc
    current ^ p ≤ ((initial + overshoot) + y) ^ p := hmono
    _ ≤ 2 * ((initial + overshoot) ^ p + y ^ p) := hfirst
    _ ≤ 2 * (2 * (initial ^ p + overshoot ^ p) + y ^ p) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hsecond le_rfl) (by norm_num)
    _ ≤ 4 * (initial ^ p + overshoot ^ p + y ^ p) := by
      nlinarith [hYp, Real.rpow_nonneg hinit p,
        Real.rpow_nonneg hover p]

/-- Combining a heavy-tailed initial `p`-moment with the shifted exponential
bound gives a uniform `p`-moment of the tracker.  Multiplication by `lam^p`
keeps the scale explicit and avoids any implicit division convention. -/
theorem tracker_p_moment_from_shifted_exp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (initial current : Ω → ℝ)
    (hinitial : Measurable initial) (hcurrent : Measurable current)
    (p overshoot lam M₀ K : ℝ)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hover : 0 ≤ overshoot)
    (hlam : 0 < lam)
    (hinitial_nonneg : ∀ ω, 0 ≤ initial ω)
    (hcurrent_nonneg : ∀ ω, 0 ≤ current ω)
    (hinitial_int : Integrable (fun ω => initial ω ^ p) μ)
    (hinitial_bound : (∫ ω, initial ω ^ p ∂μ) ≤ M₀)
    (hExpInt : Integrable
      (fun ω => Real.exp
        (lam * (current ω - initial ω - overshoot))) μ)
    (hExpBound :
      (∫ ω, Real.exp
        (lam * (current ω - initial ω - overshoot)) ∂μ) ≤ K) :
    Integrable (fun ω => current ω ^ p) μ ∧
      lam ^ p * (∫ ω, current ω ^ p ∂μ) ≤
        4 * (lam ^ p * M₀ + lam ^ p * overshoot ^ p + 5 * K) := by
  let X : Ω → ℝ := fun ω => current ω - initial ω - overshoot
  let Y : Ω → ℝ := fun ω => (max (X ω) 0) ^ p
  have hX : Measurable X :=
    (hcurrent.sub hinitial).sub measurable_const
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp1
  have hY := positivePart_rpow_integrable_and_integral_le_of_exp
    μ X hX p lam K hp0 hp2 hlam hExpInt hExpBound
  have hYInt : Integrable Y μ := hY.1
  have hYBound : lam ^ p * (∫ ω, Y ω ∂μ) ≤ 5 * K := hY.2
  have hcurrentPowMeas : Measurable (fun ω => current ω ^ p) := by
    fun_prop
  have hcurrentPowNonneg (ω : Ω) : 0 ≤ current ω ^ p :=
    Real.rpow_nonneg (hcurrent_nonneg ω) _
  have hsumInt : Integrable
      (fun ω => initial ω ^ p + overshoot ^ p + Y ω) μ :=
    (hinitial_int.add (integrable_const _)).add hYInt
  have hsumBound (ω : Ω) : current ω ^ p ≤
      4 * (initial ω ^ p + overshoot ^ p + Y ω) :=
    tracker_rpow_le_initial_overshoot_excursion hp1 hp2
      (hinitial_nonneg ω) (hcurrent_nonneg ω) hover
  have hcurrentInt : Integrable (fun ω => current ω ^ p) μ :=
    Integrable.mono_nonneg (hsumInt.const_mul 4)
      hcurrentPowMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hcurrentPowNonneg)
      (Filter.Eventually.of_forall hsumBound)
  have hIntegral : (∫ ω, current ω ^ p ∂μ) ≤
      4 * ((∫ ω, initial ω ^ p ∂μ) + overshoot ^ p +
        (∫ ω, Y ω ∂μ)) := by
    have h := integral_mono hcurrentInt (hsumInt.const_mul 4) hsumBound
    have hsumEq :
        (∫ ω, initial ω ^ p + overshoot ^ p + Y ω ∂μ) =
        (∫ ω, initial ω ^ p ∂μ) + overshoot ^ p +
          (∫ ω, Y ω ∂μ) := by
      calc
        (∫ ω, initial ω ^ p + overshoot ^ p + Y ω ∂μ) =
            (∫ ω, initial ω ^ p + overshoot ^ p ∂μ) +
              (∫ ω, Y ω ∂μ) :=
          integral_add (hinitial_int.add (integrable_const _)) hYInt
        _ = ((∫ ω, initial ω ^ p ∂μ) + overshoot ^ p) +
              (∫ ω, Y ω ∂μ) := by
          congr 1
          calc
            (∫ ω, initial ω ^ p + overshoot ^ p ∂μ) =
                (∫ ω, initial ω ^ p ∂μ) +
                  (∫ _ω, overshoot ^ p ∂μ) :=
              integral_add hinitial_int (integrable_const _)
            _ = (∫ ω, initial ω ^ p ∂μ) + overshoot ^ p := by simp
    rw [integral_const_mul, hsumEq] at h
    exact h
  have hlamp : 0 ≤ lam ^ p := (Real.rpow_pos_of_pos hlam p).le
  have hinitScaled := mul_le_mul_of_nonneg_left hinitial_bound hlamp
  refine ⟨hcurrentInt, ?_⟩
  calc
    lam ^ p * (∫ ω, current ω ^ p ∂μ) ≤
        lam ^ p * (4 * ((∫ ω, initial ω ^ p ∂μ) +
          overshoot ^ p + (∫ ω, Y ω ∂μ))) :=
      mul_le_mul_of_nonneg_left hIntegral hlamp
    _ = 4 * (lam ^ p * (∫ ω, initial ω ^ p ∂μ) +
          lam ^ p * overshoot ^ p + lam ^ p * (∫ ω, Y ω ∂μ)) := by ring
    _ ≤ 4 * (lam ^ p * M₀ + lam ^ p * overshoot ^ p + 5 * K) := by
      nlinarith [hinitScaled, hYBound]

end

end HeavyTailedNoise.UpperK1
