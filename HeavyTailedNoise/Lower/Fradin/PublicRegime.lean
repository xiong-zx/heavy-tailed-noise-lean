import HeavyTailedNoise.Lower.Fradin.Parameters

/-! A single rational accuracy threshold supplies the deterministic gap
condition and the chain-floor regime used by the final parameter split. -/

namespace HeavyTailedNoise.Fradin
noncomputable section
set_option autoImplicit false

def epsilonFraction : ℝ := 1/1024

def chainPublicThreshold : ℝ := 96*oracleSmoothnessBudget

theorem epsilonFraction_pos : 0 < epsilonFraction := by norm_num [epsilonFraction]

theorem publicA_ge_threshold {L Δ ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsmall : ε ≤ epsilonFraction * Real.sqrt (L*Δ)) :
    chainPublicThreshold ≤ L*Δ/ε^2 := by
  have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ L*Δ)
  have hsqrt0 := Real.sqrt_nonneg (L*Δ)
  have hmul : 1024*ε ≤ Real.sqrt (L*Δ) := by
    dsimp [epsilonFraction] at hsmall
    linarith
  have hsq : (1024*ε)^2 ≤ L*Δ := by
    have h := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1024*ε) hsqrt0).2 hmul
    nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  norm_num [chainPublicThreshold, oracleSmoothnessBudget]
  nlinarith [sq_nonneg ε]

theorem noise_gap_of_public_accuracy {L Δ ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsmall : ε ≤ epsilonFraction * Real.sqrt (L*Δ)) :
    8*ε^2 ≤ L*Δ := by
  have h := (le_div_iff₀ (sq_pos_of_pos hε)).1
    (publicA_ge_threshold hL hΔ hε hsmall)
  norm_num [chainPublicThreshold, oracleSmoothnessBudget] at h
  nlinarith [sq_nonneg ε]

end
end HeavyTailedNoise.Fradin
