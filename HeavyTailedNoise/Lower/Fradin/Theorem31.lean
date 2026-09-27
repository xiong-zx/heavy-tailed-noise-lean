import HeavyTailedNoise.Lower.Fradin.ActualRisk
import HeavyTailedNoise.Lower.Fradin.PhysicalRateBounds

/-! Fradin v2 Theorem 3.1, with an explicit conservative coefficient.
The source protocol and natural pre-response round complexity are preserved.
This theorem has no oracle, progress, or probability premise. -/

namespace HeavyTailedNoise.Fradin
open scoped ENNReal
noncomputable section
set_option autoImplicit false
universe v

theorem theorem31_lower_bound {K : ℕ} (hK : 0 < K)
    {p q L Δ σ ε : ℝ} (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q ∧ q ≤ 2)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hsmall : ε ≤ epsilonFraction * Real.sqrt (L*Δ)) :
    ENNReal.ofReal (publicRateCoefficient p *
      ((σ/ε)^tailExponent p + L*Δ/ε^2 +
        (L*Δ/ε^2)*(σ/ε)^(tailExponent p/q))) ≤
      sourceRoundComplexity.{0, v} K hK p q Δ σ L ε := by
  let A := L*Δ/ε^2
  let S := σ/ε
  let θ := revealParameter 92 S (tailExponent p)
    (by norm_num) (tailExponent_pos hp.1)
  let Z := A * (θ : ℝ)^((q-1)/q) / (48*oracleSmoothnessBudget)
  let R := sourceRoundComplexity.{0, v} K hK p q Δ σ L ε
  have hA : chainPublicThreshold ≤ A := publicA_ge_threshold hL hΔ hε hsmall
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hS : 0 ≤ S := div_nonneg hσ hε.le
  have hθ : 0 < (θ : ℝ) := revealRate_pos (by norm_num : (0 : ℝ) < 92)
  have hTfloor : chainLength L Δ ε θ q = ⌊Z⌋₊ := by
    unfold chainLength
    rw [chain_floor_argument_eq hL hε hθ]
  have hnoiseWork : ENNReal.ofReal (noiseRateCoefficient p*S^tailExponent p) ≤ R := by
    have hn := noiseFamily_sourceRoundComplexity_lower_bound.{v}
      hK hp hq.1 hL hΔ hε hσ (noise_gap_of_public_accuracy hL hΔ hε hsmall)
    apply (ENNReal.ofReal_le_ofReal (noiseRateCoefficient_work_bound hS hp.1)).trans
    exact hn
  have hchainWork (hZ : 2 ≤ Z) :
      ENNReal.ofReal (chainRateCoefficient p*(A+A*S^(tailExponent p/q))) ≤ R := by
    have hb := large_chain_rate_bound hA0 hS hp.1 hq.1 hZ
    have hT : 0 < chainLength L Δ ε θ q := by
      rw [hTfloor]
      exact hb.1
    have hs := physicalChain_sourceRoundComplexity_lower_bound.{v}
      hK hp hq.1 hL hΔ hε hσ hT
    have hr : chainRateCoefficient p*(A+A*S^(tailExponent p/q)) ≤
        (chainLength L Δ ε θ q : ℝ)/(4*(θ : ℝ)) := by
      rw [hTfloor]
      exact hb.2
    exact (ENNReal.ofReal_le_ofReal hr).trans hs
  by_cases hR : R = ⊤
  · change ENNReal.ofReal _ ≤ R
    rw [hR]
    exact le_top
  · apply (ENNReal.ofReal_le_iff_le_toReal hR).2
    change publicRateCoefficient p*(S^tailExponent p+A+A*S^(tailExponent p/q)) ≤ R.toReal
    unfold publicRateCoefficient
    apply combined_rate_of_chain_or_noise (Z := Z) hA0 (Real.rpow_nonneg hS _)
      (Real.rpow_nonneg hS _) (noiseRateCoefficient_pos p) (chainRateCoefficient_pos p)
      (by norm_num [smallChainMultiplier, oracleSmoothnessBudget])
    · exact (ENNReal.ofReal_le_iff_le_toReal hR).1 hnoiseWork
    · intro hz
      exact (ENNReal.ofReal_le_iff_le_toReal hR).1 (hchainWork hz)
    · intro hz
      exact small_chain_rate_bound hA hS hp.1 hq.1 hz

/-- Explicit quantifiers: one accuracy threshold and one positive coefficient
for each p work for all q in [1,2], all batch sizes and all physical parameters. -/
theorem theorem31_constants :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ p : ℝ, (1 < p ∧ p ≤ 2) →
      ∃ cₚ : ℝ, 0 < cₚ ∧
        ∀ (K : ℕ) (hK : 0 < K) (q L Δ σ ε : ℝ),
          (1 ≤ q ∧ q ≤ 2) → 0 < L → 0 < Δ → 0 < ε → 0 ≤ σ →
          ε ≤ c₁ * Real.sqrt (L*Δ) →
          ENNReal.ofReal (cₚ*((σ/ε)^tailExponent p + L*Δ/ε^2 +
            (L*Δ/ε^2)*(σ/ε)^(tailExponent p/q))) ≤
            sourceRoundComplexity.{0, v} K hK p q Δ σ L ε := by
  refine ⟨epsilonFraction, epsilonFraction_pos, ?_⟩
  intro p hp
  refine ⟨publicRateCoefficient p, publicRateCoefficient_pos p, ?_⟩
  intro K hK q L Δ σ ε hq hL hΔ hε hσ hsmall
  exact theorem31_lower_bound hK hp hq hL hΔ hε hσ hsmall

end
end HeavyTailedNoise.Fradin
