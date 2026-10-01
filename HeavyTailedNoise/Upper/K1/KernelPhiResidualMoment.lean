import HeavyTailedNoise.Upper.K1.KernelHighResidualMoment
import HeavyTailedNoise.Upper.K1.KernelLowMoment

/-!
The complete same-source `Φ_k` kernel combines the lag-zero low band and all
high bands before squaring. The factor two below bounds their cross term; it
does not assert independence among transforms of one oracle response.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- Pointwise complete-kernel squared-lag bound from the original residual
`p` moment, with the physical low and high coefficients left visible. -/
theorem paperSchedule_kernelPhi_sq_sum_le_residual_p
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hq : 1 ≤ q)
    (hε : 0 < ε) (hch : 0 < ch) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    {d T : ℕ} (z : Point d) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    (∑ k ∈ Finset.range T, ‖kernelPhi P k z‖ ^ 2) ≤
      2 * (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩) ^ (2 - p) * ‖z‖ ^ p +
      2 * ((3 / Real.sqrt κ) * paperNu σ ε *
        ((2 : ℝ) ^ (1 - paperSexp p q / 2) /
          ((2 : ℝ) ^ (1 - paperSexp p q / 2) - 1))) ^ 2 *
        (‖z‖ / paperNu σ ε) ^ p *
        (12 * (2 : ℝ) ^ paperJ p σ ε Ctail) ^
          (max (2 * (1 - paperSexp p q / 2) - p) 0) := by
  dsimp
  let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
  have hlow := lowBand_sq_le_residual_p P hp hp2 z
  have hhigh := paperSchedule_kernelPsi_sq_sum_le_residual_p (T := T)
    p q Δ σ Lbar ε Ctail ch κ Cb CI
    hp hp2 hq hε hch hκ hCb hCI z
  have hphi := kernelPhi_sq_sum_le_low_add_high P T z
  dsimp [P] at hlow hphi
  nlinarith

end

end HeavyTailedNoise.UpperK1
