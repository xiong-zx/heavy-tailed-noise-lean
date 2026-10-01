import HeavyTailedNoise.Upper.K1.KernelSquaredDyadicBridge
import HeavyTailedNoise.Upper.K1.KernelPhysicalSqrtWeight

/-!
The literal shared-batch high-band kernel bound.  This module discharges both
the support and square-root weight premises of the earlier conditional
dyadic bridge for the manuscript's actual schedule.  No independence among
bands of one returned response is assumed.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- For every finite `q ≥ 1`, the exponent of the Minkowski dyadic sum is
strictly positive. This includes `q = 1`, `p = 2`, and the critical curve. -/
theorem paperHighDyadicExponent_pos {p q : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hq : 1 ≤ q) :
    0 < 1 - paperSexp p q / 2 := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hdiv : 0 < 1 / q := one_div_pos.mpr hq0
  have hfactor : 1 - 1 / q < 1 := by linarith
  have hsltp : paperSexp p q < p := by
    unfold paperSexp
    simpa only [mul_one] using (mul_lt_mul_of_pos_left hfactor hp0)
  linarith

/-- The physical high-band finite-lag bound, with no unproved shell-support
or EMA-weight premise. The explicit constant is conservative; its dependence
on `κ` and the finite-q dyadic exponent is displayed. -/
theorem paperSchedule_kernelPsi_sq_sum_le_dyadic
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
          ((2 : ℝ) ^ (1 - paperSexp p q / 2) - 1)) *
        (min (‖z‖ / paperNu σ ε)
          (12 * (2 : ℝ) ^ paperJ p σ ε Ctail)) ^
          (1 - paperSexp p q / 2)) ^ 2 := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  let ν : ℝ := paperNu σ ε
  let x : ℝ := ‖z‖ / ν
  let a : ℝ := 1 - paperSexp p q / 2
  let C : ℝ := 3 / Real.sqrt κ
  have hν : 0 ≤ ν := (paperNu_pos hε).le
  have hx : 0 ≤ x := div_nonneg (norm_nonneg _) hν
  have ha : 0 < a := paperHighDyadicExponent_pos hp hp2 hq
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hα (j : Fin P.J) : 0 < P.alpha j := by
    change 0 < paperAlpha p q κ j.val
    exact paperAlpha_pos hκ j.val
  have hαle (j : Fin P.J) : P.alpha j ≤ 1 := by
    change paperAlpha p q κ j.val ≤ 1
    exact paperAlpha_le_one p q κ j.val
  have hzero (j : Fin P.J)
      (hj : ¬ 12 * (2 : ℝ) ^ (j : ℕ) < x) :
      highBand P j z = 0 := by
    exact paperSchedule_highBand_zero_of_inactive
      p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI z j hj
  have hweight (j : Fin P.J) :
      Real.sqrt (P.alpha j) * ‖highBand P j z‖ ≤
        C * ν * (12 * (2 : ℝ) ^ (j : ℕ)) ^ a := by
    have h := paperSchedule_sqrtAlpha_mul_highBand_norm_le
      p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hκ hCb hCI z j
    convert h using 1 <;> ring
  have hbridge := kernelPsi_sq_sum_le_dyadic_of_support_and_weight
    (T := T) P z ν x a C hν hx ha hC hα hαle hzero hweight
  simpa only [P, ν, x, a, C, paperSchedule] using hbridge

end

end HeavyTailedNoise.UpperK1
