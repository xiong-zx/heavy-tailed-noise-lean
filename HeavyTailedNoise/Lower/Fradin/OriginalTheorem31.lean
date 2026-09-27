import HeavyTailedNoise.Lower.Fradin.Theorem31
import HeavyTailedNoise.Lower.Fradin.Representation

/-! Public Theorem 3.1 entry on the original response-only algorithm domain.
The source's batched gradient expression is normalized to the first queried
slot; no extra observation or query history is supplied to these algorithms. -/

namespace HeavyTailedNoise.Fradin
open scoped ENNReal
noncomputable section
set_option autoImplicit false
universe v

theorem original_theorem31_lower_bound {K : ℕ} (hK : 0 < K)
    {p q L Δ σ ε : ℝ} (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q ∧ q ≤ 2)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hsmall : ε ≤ epsilonFraction * Real.sqrt (L*Δ)) :
    ENNReal.ofReal (publicRateCoefficient p *
      ((σ/ε)^tailExponent p + L*Δ/ε^2 +
        (L*Δ/ε^2)*(σ/ε)^(tailExponent p/q))) ≤
      observedSourceRoundComplexity.{0, v} K hK p q Δ σ L ε := by
  rw [observedSourceRoundComplexity_eq]
  exact theorem31_lower_bound hK hp hq hL hΔ hε hσ hsmall

theorem original_theorem31_constants :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ p : ℝ, (1 < p ∧ p ≤ 2) →
      ∃ cₚ : ℝ, 0 < cₚ ∧
        ∀ (K : ℕ) (hK : 0 < K) (q L Δ σ ε : ℝ),
          (1 ≤ q ∧ q ≤ 2) → 0 < L → 0 < Δ → 0 < ε → 0 ≤ σ →
          ε ≤ c₁ * Real.sqrt (L*Δ) →
          ENNReal.ofReal (cₚ*((σ/ε)^tailExponent p + L*Δ/ε^2 +
            (L*Δ/ε^2)*(σ/ε)^(tailExponent p/q))) ≤
            observedSourceRoundComplexity.{0, v} K hK p q Δ σ L ε := by
  refine ⟨epsilonFraction, epsilonFraction_pos, ?_⟩
  intro p hp
  refine ⟨publicRateCoefficient p, publicRateCoefficient_pos p, ?_⟩
  intro K hK q L Δ σ ε hq hL hΔ hε hσ hsmall
  exact original_theorem31_lower_bound hK hp hq hL hΔ hε hσ hsmall

end
end HeavyTailedNoise.Fradin
