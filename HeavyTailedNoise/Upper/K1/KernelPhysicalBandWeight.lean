import HeavyTailedNoise.Upper.K1.KernelShellSupport
import HeavyTailedNoise.Upper.K1.RateArithmetic

/-!
The literal manuscript schedule supplies the support and coarse-size premises
needed by the conditional dyadic kernel bridge.  The square-root EMA weight
estimate is kept separate from these exact geometry facts.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

/-- The literal `min` rate is no larger than its high-band inverse branch. -/
theorem paperAlpha_le_inverse_branch (p q κ : ℝ) (j : ℕ) :
    paperAlpha p q κ j ≤
      (κ * (12 * (2 : ℝ) ^ j) ^ paperSexp p q)⁻¹ := by
  unfold paperAlpha
  exact min_le_right _ _

/-- The lower threshold of actual band `j+1` is `ν·12·2^j`. -/
theorem paperSchedule_tau_low_eq_nu_dyadic
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    (j : Fin (paperJ p σ ε Ctail)) :
    (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI).tau j.castSucc =
      paperNu σ ε * (12 * (2 : ℝ) ^ (j : ℕ)) := by
  change paperTau σ ε j.val = paperNu σ ε * (12 * (2 : ℝ) ^ j.val)
  unfold paperTau
  ring

/-- An inactive literal high band contributes the zero vector. The comparison
uses only the same pre-batch center's residual norm and the actual dyadic
threshold; it is deterministic. -/
theorem paperSchedule_highBand_zero_of_inactive
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} (z : Point d) (j : Fin (paperJ p σ ε Ctail))
    (hinactive : ¬ 12 * (2 : ℝ) ^ (j : ℕ) <
      ‖z‖ / paperNu σ ε) :
    highBand (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI) j z = 0 := by
  let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  have hν : 0 < paperNu σ ε := paperNu_pos hε
  have hdouble : P.tau j.succ = 2 * P.tau j.castSucc :=
    paperSchedule_tau_double p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI j
  have hmono : P.tau j.castSucc ≤ P.tau j.succ := by
    rw [hdouble]
    have hlow := P.tau_pos j.castSucc
    linarith
  have hnorm : ‖z‖ ≤ paperNu σ ε * (12 * (2 : ℝ) ^ (j : ℕ)) :=
    by simpa only [mul_comm] using
      (div_le_iff₀ hν).mp (le_of_not_gt hinactive)
  change highBand P j z = 0
  apply highBand_zero_of_norm_le P j z hmono
  change ‖z‖ ≤ paperTau σ ε j.val
  unfold paperTau
  nlinarith [hnorm]

/-- The conservative shell norm bound for the literal doubled threshold. -/
theorem paperSchedule_highBand_norm_le_three_nu_dyadic
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} (z : Point d) (j : Fin (paperJ p σ ε Ctail)) :
    ‖highBand (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI) j z‖ ≤
      3 * paperNu σ ε * (12 * (2 : ℝ) ^ (j : ℕ)) := by
  let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  have hdouble : P.tau j.succ = 2 * P.tau j.castSucc :=
    paperSchedule_tau_double p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI j
  have hbound := highBand_norm_le_three_low P j z hdouble
  change ‖highBand P j z‖ ≤ 3 * paperTau σ ε j.val at hbound
  change ‖highBand P j z‖ ≤
    3 * paperNu σ ε * (12 * (2 : ℝ) ^ (j : ℕ))
  unfold paperTau at hbound
  nlinarith [hbound]

end

end HeavyTailedNoise.UpperK1
