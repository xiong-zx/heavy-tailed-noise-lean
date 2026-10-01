import HeavyTailedNoise.Analysis.Smoothness
import HeavyTailedNoise.Upper.K1.Algorithm

/-!
Deterministic descent facts for the manuscript's normalized runtime update.
The only direction is `UpperK1.direction` from the algorithm module. Oracle
probability enters solely through the previously proved population-gradient
Lipschitz bound; no estimator moment hypothesis is assumed here.
-/

namespace HeavyTailedNoise

open Metric
open scoped InnerProductSpace BigOperators

noncomputable section

/-- A globally Lipschitz gradient gives a quadratic value remainder. The
constant `L` (rather than `L/2`) is enough for the normalized descent budget. -/
theorem Objective.value_le_linear_add_sq {d : ℕ} {Δ L : ℝ}
    (O : Objective d Δ) (hL : 0 ≤ L)
    (hgrad : ∀ u v, ‖O.grad u - O.grad v‖ ≤ L * ‖u - v‖)
    (x y : Point d) :
    O.value y ≤ O.value x + ⟪O.grad x, y - x⟫_ℝ + L * ‖y - x‖ ^ 2 := by
  let s : Set (Point d) := closedBall x ‖y - x‖
  have hx : x ∈ s := mem_closedBall_self (norm_nonneg _)
  have hy : y ∈ s := by
    change y ∈ closedBall x ‖y - x‖
    exact mem_closedBall_iff_norm.mpr le_rfl
  have hderiv (z : Point d) (_hz : z ∈ s) :
      HasFDerivWithinAt O.value
        (InnerProductSpace.toDual ℝ (Point d) (O.grad z)) s z :=
    (O.hasGradientAt z).hasFDerivAt.hasFDerivWithinAt
  have hbound (z : Point d) (hz : z ∈ s) :
      ‖InnerProductSpace.toDual ℝ (Point d) (O.grad z) -
        InnerProductSpace.toDual ℝ (Point d) (O.grad x)‖ ≤
          L * ‖y - x‖ := by
    have hnorm : ‖InnerProductSpace.toDual ℝ (Point d) (O.grad z) -
        InnerProductSpace.toDual ℝ (Point d) (O.grad x)‖ =
        ‖O.grad z - O.grad x‖ := by
      rw [← map_sub]
      exact (InnerProductSpace.toDual ℝ (Point d)).norm_map _
    rw [hnorm]
    exact (hgrad z x).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hz) hL)
  have hrem := (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := O.value)
    (f' := fun z => InnerProductSpace.toDual ℝ (Point d) (O.grad z))
    (φ := InnerProductSpace.toDual ℝ (Point d) (O.grad x))
    (C := L * ‖y - x‖) hderiv hbound hx hy
  have habs : |O.value y - O.value x - ⟪O.grad x, y - x⟫_ℝ| ≤
      L * ‖y - x‖ ^ 2 := by
    simpa only [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs,
      pow_two, mul_assoc] using hrem
  linarith [le_abs_self (O.value y - O.value x - ⟪O.grad x, y - x⟫_ℝ)]

/-- The q-WAS bridge supplies the Lipschitz constant required above. -/
theorem Admissible.value_le_linear_add_sq
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x y : Point d) :
    I.objective.value y ≤ I.objective.value x +
      ⟪I.objective.grad x, y - x⟫_ℝ + Lbar * ‖y - x‖ ^ 2 :=
  I.objective.value_le_linear_add_sq I.Lbar_pos.le I.grad_lipschitz x y

/-- A normalized estimate loses at most twice its estimation error in the
descent-direction inner product, including when the estimate is zero. -/
theorem UpperK1.norm_le_inner_direction_add_error {d : ℕ}
    (g hhat : Point d) :
    ‖g‖ ≤ ⟪g, UpperK1.direction hhat⟫_ℝ + 2 * ‖hhat - g‖ := by
  by_cases hz : hhat = 0
  · subst hhat
    simp only [UpperK1.direction_zero, inner_zero_right, zero_sub, norm_neg]
    nlinarith [norm_nonneg g]
  have hn : ‖hhat‖ ≠ 0 := (norm_ne_zero_iff).mpr hz
  have hdir : ‖UpperK1.direction hhat‖ = 1 := by
    have hpos : 0 ≤ ‖hhat‖⁻¹ := inv_nonneg.mpr (norm_nonneg hhat)
    rw [UpperK1.direction, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hpos, inv_mul_cancel₀ hn]
  have hself : ⟪hhat, UpperK1.direction hhat⟫_ℝ = ‖hhat‖ := by
    rw [UpperK1.direction, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hn]
    ring
  have hinner := real_inner_le_norm (hhat - g) (UpperK1.direction hhat)
  rw [hdir, mul_one] at hinner
  have htriangle : ‖g‖ ≤ ‖hhat‖ + ‖hhat - g‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub' g hhat
  have hsplit : ⟪g, UpperK1.direction hhat⟫_ℝ =
      ‖hhat‖ - ⟪hhat - g, UpperK1.direction hhat⟫_ℝ := by
    rw [inner_sub_left, hself]
    ring
  rw [hsplit]
  linarith

/-- One runtime update, using exactly the algorithm's total direction map. -/
theorem Admissible.normalized_step_descent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    {h : ℝ} (hh : 0 ≤ h) (x hhat : Point d) :
    I.objective.value (x - h • UpperK1.direction hhat) ≤
      I.objective.value x - h * ‖I.objective.grad x‖ +
        2 * h * ‖hhat - I.objective.grad x‖ + Lbar * h ^ 2 := by
  let u := UpperK1.direction hhat
  have hu : ‖u‖ ≤ 1 := UpperK1.direction_norm_le_one hhat
  have hstepnorm : ‖(x - h • u) - x‖ ≤ h := by
    have heq : (x - h • u) - x = -(h • u) := by abel
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu hh
  have hstepsq : ‖(x - h • u) - x‖ ^ 2 ≤ h ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hh).mpr hstepnorm
  have hlin : ⟪I.objective.grad x, (x - h • u) - x⟫_ℝ =
      -h * ⟪I.objective.grad x, u⟫_ℝ := by
    have heq : (x - h • u) - x = -(h • u) := by abel
    rw [heq, inner_neg_right, real_inner_smul_right]
    ring
  have hdir := UpperK1.norm_le_inner_direction_add_error
    (I.objective.grad x) hhat
  have hsmooth := I.value_le_linear_add_sq x (x - h • u)
  change ‖I.objective.grad x‖ ≤
    ⟪I.objective.grad x, u⟫_ℝ +
      2 * ‖hhat - I.objective.grad x‖ at hdir
  rw [hlin] at hsmooth
  have hquad := mul_le_mul_of_nonneg_left hstepsq I.Lbar_pos.le
  change I.objective.value (x - h • u) ≤
    I.objective.value x - h * ‖I.objective.grad x‖ +
      2 * h * ‖hhat - I.objective.grad x‖ + Lbar * h ^ 2
  nlinarith [mul_le_mul_of_nonneg_left hdir hh]

/-- Deterministic telescope for any realized sequence of runtime estimates.
Expectation over a random selected index may be applied after this bound. -/
theorem Admissible.normalized_descent_sum
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    {h : ℝ} (hh : 0 ≤ h) (T : ℕ)
    (x hhat : ℕ → Point d)
    (hstep : ∀ t, x (t + 1) = x t - h • UpperK1.direction (hhat t)) :
    h * ∑ t ∈ Finset.range T, ‖I.objective.grad (x t)‖ ≤
      I.objective.value (x 0) - I.objective.value (x T) +
        2 * h * ∑ t ∈ Finset.range T, ‖hhat t - I.objective.grad (x t)‖ +
          (T : ℝ) * Lbar * h ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hlocal := I.normalized_step_descent hh (x T) (hhat T)
      rw [← hstep T] at hlocal
      simp only [Finset.sum_range_succ, Nat.cast_succ] at *
      nlinarith

/-- When the initial point is zero, the objective's declared gap replaces the
telescoping value difference. -/
theorem Admissible.normalized_descent_sum_gap
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    {h : ℝ} (hh : 0 ≤ h) (T : ℕ)
    (x hhat : ℕ → Point d)
    (hstep : ∀ t, x (t + 1) = x t - h • UpperK1.direction (hhat t))
    (hx0 : x 0 = 0) :
    h * ∑ t ∈ Finset.range T, ‖I.objective.grad (x t)‖ ≤
      Δ + 2 * h * ∑ t ∈ Finset.range T,
        ‖hhat t - I.objective.grad (x t)‖ + (T : ℝ) * Lbar * h ^ 2 := by
  have hsum := I.normalized_descent_sum hh T x hhat hstep
  rw [hx0] at hsum
  have hgap := I.objective.gap (x T)
  linarith

end

end HeavyTailedNoise
