import HeavyTailedNoise.Upper.K1.KernelPhiResidualMoment
import HeavyTailedNoise.Upper.K1.CutoffBounds

/-!
The whole shared-source kernel's finite-lag square has a dimensionless
coefficient depending only on `p`, `q`, and `κ`.  The exponent is the literal
batch exponent `paperEplus`; the low lag is absorbed because `U ≥ 1`.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- The noise scale equals the accuracy times the dimensionless noise ratio,
including `σ = 0`. -/
theorem paperNu_eq_epsilon_mul_paperS
    {σ ε : ℝ} (hε : 0 < ε) :
    paperNu σ ε = ε * paperS σ ε := by
  by_cases hσε : σ ≤ ε
  · have hdiv : σ / ε ≤ 1 :=
      (div_le_iff₀ hε).mpr (by nlinarith)
    simp [paperNu, paperS, max_eq_right hσε, max_eq_left hdiv]
  · have hεσ : ε ≤ σ := le_of_lt (lt_of_not_ge hσε)
    have hdiv : 1 ≤ σ / ε :=
      (le_div_iff₀ hε).mpr (by nlinarith)
    simp [paperNu, paperS, max_eq_left hεσ, max_eq_right hdiv]
      <;> field_simp [ne_of_gt hε]

def physicalKernelNoiseConstant (p q κ : ℝ) : ℝ :=
  2 * (24 : ℝ) ^ (2 - p) +
    2 * ((3 / Real.sqrt κ) *
      ((2 : ℝ) ^ (1 - paperSexp p q / 2) /
        ((2 : ℝ) ^ (1 - paperSexp p q / 2) - 1))) ^ 2

/-- Physical finite-lag kernel coefficient, with the low/high covariance
handled inside the complete `kernelPhi` norm. -/
theorem paperSchedule_kernelPhi_sq_sum_le_physical
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hq : 1 ≤ q)
    (hε : 0 < ε) (hch : 0 < ch) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    {d T : ℕ} (z : Point d) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    (∑ k ∈ Finset.range T, ‖kernelPhi P k z‖ ^ 2) ≤
      physicalKernelNoiseConstant p q κ *
        (paperNu σ ε) ^ (2 - p) *
        (paperU p σ ε Ctail) ^ (paperEplus p q) * ‖z‖ ^ p := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  let ν := paperNu σ ε
  let U := paperU p σ ε Ctail
  let e := paperEplus p q
  let a := 2 - p
  let R := (2 : ℝ) ^ (1 - paperSexp p q / 2) /
    ((2 : ℝ) ^ (1 - paperSexp p q / 2) - 1)
  let K := (3 / Real.sqrt κ) *
    ((2 : ℝ) ^ (1 - paperSexp p q / 2) /
      ((2 : ℝ) ^ (1 - paperSexp p q / 2) - 1))
  have hν : 0 < ν := paperNu_pos hε
  have hU : 1 ≤ U := by
    change 1 ≤ paperU p σ ε Ctail
    rw [paperU_eq_dyadic hε]
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ paperJ p σ ε Ctail := by
      simpa only [pow_zero] using
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (Nat.zero_le _))
    nlinarith
  have he : 0 ≤ e := paperEplus_nonneg p q
  have hUe : 1 ≤ U ^ e := Real.one_le_rpow hU he
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    have hhigh := paperHighDyadicExponent_pos hp hp2 hq
    have hpow : 1 < (2 : ℝ) ^ (1 - paperSexp p q / 2) :=
      Real.one_lt_rpow (by norm_num) hhigh
    positivity
  have hτ : 2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ = 24 * ν := by
    change 2 * paperTau σ ε 0 = 24 * paperNu σ ε
    simp [paperTau, ν]
    ring
  have heq : max (2 * (1 - paperSexp p q / 2) - p) 0 = e := by
    dsimp [e, paperEplus, paperA]
    congr 1
    ring
  have hlow : (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩) ^ a =
      (24 : ℝ) ^ a * ν ^ a := by
    rw [hτ, Real.mul_rpow (by norm_num) hν.le]
  have hνpow : ν ^ a = ν ^ 2 / ν ^ p := by
    simpa only [a, Real.rpow_two] using
      (Real.rpow_sub hν (2 : ℝ) p)
  have hhigh : (K * ν) ^ 2 * (‖z‖ / ν) ^ p =
      K ^ 2 * ν ^ a * ‖z‖ ^ p := by
    rw [Real.div_rpow (norm_nonneg _) hν.le, hνpow]
    have hνp : ν ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hν _)
    field_simp [hνp] <;> ring
  have hbase := paperSchedule_kernelPhi_sq_sum_le_residual_p
    p q Δ σ Lbar ε Ctail ch κ Cb CI
    hp hp2 hq hε hch hκ hCb hCI (T := T) z
  change (∑ k ∈ Finset.range T, ‖kernelPhi P k z‖ ^ 2) ≤
      2 * (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩) ^ a * ‖z‖ ^ p +
      2 * ((3 / Real.sqrt κ) * ν * R) ^ 2 * (‖z‖ / ν) ^ p *
        (12 * (2 : ℝ) ^ paperJ p σ ε Ctail) ^
          (max (2 * (1 - paperSexp p q / 2) - p) 0) at hbase
  have hKorder : ((3 / Real.sqrt κ) * ν * R) ^ 2 = (K * ν) ^ 2 := by
    dsimp [K, R]
    ring
  rw [hKorder] at hbase
  have hhigh2 :
      2 * (K * ν) ^ 2 * (‖z‖ / ν) ^ p * U ^ e =
      2 * K ^ 2 * ν ^ a * ‖z‖ ^ p * U ^ e := by
    calc
      _ = 2 * ((K * ν) ^ 2 * (‖z‖ / ν) ^ p) * U ^ e := by ring
      _ = _ := by rw [hhigh]; ring
  rw [hlow, heq, ← paperU_eq_dyadic hε, hhigh2] at hbase
  have hlowNonneg :
      0 ≤ 2 * (24 : ℝ) ^ a * ν ^ a * ‖z‖ ^ p := by
    positivity
  have hlowGrow :
      2 * (24 : ℝ) ^ a * ν ^ a * ‖z‖ ^ p ≤
      (2 * (24 : ℝ) ^ a * ν ^ a * ‖z‖ ^ p) * U ^ e :=
    calc
      _ = (2 * (24 : ℝ) ^ a * ν ^ a * ‖z‖ ^ p) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hUe hlowNonneg
  change (∑ k ∈ Finset.range T, ‖kernelPhi P k z‖ ^ 2) ≤
      physicalKernelNoiseConstant p q κ * ν ^ a * U ^ e * ‖z‖ ^ p
  have hbound := add_le_add hlowGrow (le_refl
    (2 * K ^ 2 * ν ^ a * ‖z‖ ^ p * U ^ e))
  calc
    _ ≤ 2 * (24 : ℝ) ^ a * ν ^ a * ‖z‖ ^ p +
          2 * K ^ 2 * ν ^ a * ‖z‖ ^ p * U ^ e := by
            convert hbase using 1 <;> ring
    _ ≤ (2 * (24 : ℝ) ^ a * ν ^ a * ‖z‖ ^ p) * U ^ e +
          2 * K ^ 2 * ν ^ a * ‖z‖ ^ p * U ^ e := hbound
    _ = _ := by dsimp [physicalKernelNoiseConstant, K, a]; ring

end

end HeavyTailedNoise.UpperK1
