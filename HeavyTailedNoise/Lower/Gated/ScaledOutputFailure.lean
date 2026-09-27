import HeavyTailedNoise.Lower.Gated.ScaledAlgorithmCoupling
import HeavyTailedNoise.Lower.Gated.IdealOutputBarrier

/-!
An actual low-gradient output of the legal scaled Gaussian instance forces
ideal stage completion or a prefix accident somewhere up to the output.
The normalized algorithm uses exactly the original fixed response budget.
-/

namespace HeavyTailedNoise

noncomputable section

theorem hardGaussian_smallOutput_implies_completion_or_horizon_accident
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hd : 0 < d) (hT : 0 < T) (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    {p q L ε Δ σ : ℝ} (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (hbudget : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ)
    (A : RandomAlgorithm d N Private) (r : Private) (ξ : Fin N → Point d)
    (hg : ‖(hardGaussianAdmissible hd hT U hU hp hq hL hε hΔ hσ hbudget).objective.grad
      (A.output r (runTranscript
        (hardGaussianAdmissible hd hT U hU hp hq hL hε hΔ hσ hbudget).oracle
        A r N ξ))‖ < 2 * ε) :
    let B := rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A
    let a := σ / ((80 * ε) * Real.sqrt d)
    idealCompleted hT U B r ξ a ∨
      ∃ t ≤ N, idealPrefixAccidentAt hT U B r ξ a t := by
  classical
  dsimp only
  let B := rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A
  let a := σ / ((80 * ε) * Real.sqrt d)
  by_cases hacc : ∃ t ≤ N, idealPrefixAccidentAt hT U B r ξ a t
  · exact Or.inr hacc
  have hno : ∀ t < N, ¬ idealPrefixAccidentAt hT U B r ξ a t := by
    intro t ht ha
    exact hacc ⟨t, ht.le, ha⟩
  let x := A.output r (runTranscript
    (hardGaussianAdmissible hd hT U hU hp hq hL hε hΔ hσ hbudget).oracle
    A r N ξ)
  have hout := hardGaussian_normalizedOutput_eq_ideal hd hT U hU hp hq
    hL hε hΔ hσ hbudget A r ξ hno
  change ‖gradient (scaledHardPotential L ε U) x‖ < 2 * ε at hg
  have hformula := gradient_scaledHardPotential_eq hT U hL hε x
  rw [hformula, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 80 * ε)] at hg
  have hsmall : ‖gradient (hardPotential U)
      ((hardScaleLambda L ε)⁻¹ • x)‖ < (1 / 40 : ℝ) := by
    nlinarith [norm_nonneg (gradient (hardPotential U)
      ((hardScaleLambda L ε)⁻¹ • x))]
  rw [hout] at hsmall
  obtain hc | ha := idealOutput_small_gradient_implies_completion_or_accident
    hT U hU B r ξ a hsmall
  · exact Or.inl hc
  · exact False.elim (hacc ⟨N, le_rfl, ha⟩)

end

end HeavyTailedNoise
