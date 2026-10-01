import HeavyTailedNoise.Upper.K1.KernelPhysicalHighBound
import HeavyTailedNoise.Upper.K1.KernelTerminalPower

/-!
The physical high-band finite-lag kernel bound converted to a residual
`p`-power. Below the first high threshold, the high kernel is exactly zero;
the off-critical power comparison is applied only above that threshold.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- A high-band pointwise `p`-moment kernel bound with all same-response band
correlations retained. The scale exponent is displayed as a nonnegative max;
it equals the manuscript's `paperEplus p q`. -/
theorem paperSchedule_kernelPsi_sq_sum_le_residual_p
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hq : 1 ≤ q)
    (hε : 0 < ε) (hch : 0 < ch) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    {d T : ℕ} (z : Point d) :
    (∑ k ∈ Finset.range T,
      ‖kernelPsi (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
        hε hch hCb hCI) k z‖ ^ 2) ≤
      ((3 / Real.sqrt κ) * paperNu σ ε *
        ((2 : ℝ) ^ (1 - paperSexp p q / 2) /
          ((2 : ℝ) ^ (1 - paperSexp p q / 2) - 1))) ^ 2 *
        (‖z‖ / paperNu σ ε) ^ p *
        (12 * (2 : ℝ) ^ paperJ p σ ε Ctail) ^
          (max (2 * (1 - paperSexp p q / 2) - p) 0) := by
  let ν : ℝ := paperNu σ ε
  let x : ℝ := ‖z‖ / ν
  let U : ℝ := 12 * (2 : ℝ) ^ paperJ p σ ε Ctail
  let a : ℝ := 1 - paperSexp p q / 2
  let R : ℝ := (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1)
  let K : ℝ := (3 / Real.sqrt κ) * ν * R
  have hν : 0 < ν := paperNu_pos hε
  have hx : 0 ≤ x := div_nonneg (norm_nonneg _) hν.le
  have hU : 1 ≤ U := by
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ paperJ p σ ε Ctail := by
      simpa only [pow_zero] using
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le _))
    dsimp [U]
    nlinarith
  have ha : 0 < a := paperHighDyadicExponent_pos hp hp2 hq
  have hR : 0 ≤ R := by
    have hr : 1 < (2 : ℝ) ^ a :=
      Real.one_lt_rpow (by norm_num) ha
    dsimp [R]
    positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  by_cases hsmall : x ≤ 12
  · have hzero (k : ℕ) :
        kernelPsi (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
          hε hch hCb hCI) k z = 0 :=
      paperSchedule_kernelPsi_zero_of_small_residual
        p q Δ σ Lbar ε Ctail ch κ Cb CI
        hε hch hCb hCI z hsmall k
    have hsumzero : (∑ k ∈ Finset.range T,
        ‖kernelPsi (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
          hε hch hCb hCI) k z‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hzero k]
      simp
    rw [hsumzero]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg K) (Real.rpow_nonneg hx _))
      (Real.rpow_nonneg (by positivity : 0 ≤ U) _)
  · have hx1 : 1 ≤ x := by linarith
    have hmin : 0 ≤ min x U := le_min hx (by linarith)
    have hpowEq : ((min x U) ^ a) ^ 2 = (min x U) ^ (2 * a) := by
      have h := (Real.rpow_mul_natCast hmin a 2).symm
      have he : a * (2 : ℝ) = 2 * a := by ring
      exact h.trans (congrArg (fun r : ℝ => (min x U) ^ r) he)
    have hpow : (min x U) ^ (2 * a) ≤
        x ^ p * U ^ (max (2 * a - p) 0) :=
      terminal_min_power_le_p hx1 hU (by linarith : 0 ≤ p)
        (by linarith [ha] : 0 ≤ 2 * a)
    have hhigh := paperSchedule_kernelPsi_sq_sum_le_dyadic (T := T)
      p q Δ σ Lbar ε Ctail ch κ Cb CI
      hp hp2 hq hε hch hκ hCb hCI z
    calc
      (∑ k ∈ Finset.range T,
        ‖kernelPsi (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
          hε hch hCb hCI) k z‖ ^ 2) ≤
          (K * (min x U) ^ a) ^ 2 := by
            simpa only [K, R, a, x, U, ν] using hhigh
      _ = K ^ 2 * ((min x U) ^ a) ^ 2 := by ring
      _ ≤ K ^ 2 * (x ^ p * U ^ (max (2 * a - p) 0)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg K)
        rwa [hpowEq]
      _ = K ^ 2 * x ^ p * U ^ (max (2 * a - p) 0) := by ring
      _ = _ := rfl

end

end HeavyTailedNoise.UpperK1
