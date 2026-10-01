import HeavyTailedNoise.Upper.K1.KernelPhysicalHighBound

/-!
The small-residual support and terminal power conversion needed after the
physical high-band square sum.  The power comparison is used only above the
first threshold; below it every actual high band is exactly zero.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- The truncated high-band power is bounded by the residual `p` power once
the residual exceeds the first dyadic threshold. -/
theorem terminal_min_power_le_p
    {x U p v : ℝ} (hx : 1 ≤ x) (hU : 1 ≤ U)
    (hp : 0 ≤ p) (hv : 0 ≤ v) :
    (min x U) ^ v ≤ x ^ p * U ^ (max (v - p) 0) := by
  let e : ℝ := v - p
  have heq : p + e = v := by dsimp [e]; ring
  rcases le_total x U with hxu | hux
  · rw [min_eq_left hxu]
    by_cases he : 0 ≤ e
    · have hxe : x ^ e ≤ U ^ e := Real.rpow_le_rpow (by linarith) hxu he
      have hmul : x ^ p * x ^ e ≤ x ^ p * U ^ e :=
        mul_le_mul_of_nonneg_left hxe (Real.rpow_nonneg (by linarith) _)
      have hpow : x ^ v = x ^ p * x ^ e := by
        rw [← heq]
        exact Real.rpow_add (by linarith) p e
      simpa [e, max_eq_left he, hpow] using hmul
    · have he0 : e ≤ 0 := le_of_not_ge he
      have hvp : v ≤ p := by dsimp [e] at he0; linarith
      have hpow : x ^ v ≤ x ^ p :=
        Real.rpow_le_rpow_of_exponent_le hx hvp
      simpa [e, max_eq_right he0] using hpow
  · rw [min_eq_right hux]
    by_cases he : 0 ≤ e
    · have hUp : U ^ p ≤ x ^ p := Real.rpow_le_rpow (by linarith) hux hp
      have hmul : U ^ e * U ^ p ≤ U ^ e * x ^ p :=
        mul_le_mul_of_nonneg_left hUp (Real.rpow_nonneg (by linarith) _)
      have hpow : U ^ v = U ^ e * U ^ p := by
        rw [← heq]
        simpa only [mul_comm] using (Real.rpow_add (by linarith : 0 < U) p e)
      simpa [e, max_eq_left he, hpow, mul_comm, mul_left_comm, mul_assoc] using hmul
    · have he0 : e ≤ 0 := le_of_not_ge he
      have hvp : v ≤ p := by dsimp [e] at he0; linarith
      have hpow1 : U ^ v ≤ U ^ p :=
        Real.rpow_le_rpow_of_exponent_le hU hvp
      have hpow2 : U ^ p ≤ x ^ p := Real.rpow_le_rpow (by linarith) hux hp
      simpa [e, max_eq_right he0] using hpow1.trans hpow2

/-- When the residual radius is at most the first high threshold, every
literal high-band vector is zero, including an empty band family. -/
theorem paperSchedule_kernelPsi_zero_of_small_residual
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} (z : Point d)
    (hz : ‖z‖ / paperNu σ ε ≤ 12) (k : ℕ) :
    kernelPsi (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI) k z = 0 := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  have hzero (j : Fin P.J) : highBand P j z = 0 := by
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (j : ℕ) := by
      simpa only [pow_zero] using
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le _))
    have hinactive : ¬ 12 * (2 : ℝ) ^ (j : ℕ) <
        ‖z‖ / paperNu σ ε := by nlinarith [hpow, hz]
    exact paperSchedule_highBand_zero_of_inactive
      p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI z j hinactive
  change kernelPsi P k z = 0
  simp [kernelPsi, hzero]

end

end HeavyTailedNoise.UpperK1
