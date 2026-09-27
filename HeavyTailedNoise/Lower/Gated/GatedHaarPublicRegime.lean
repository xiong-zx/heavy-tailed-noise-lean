import HeavyTailedNoise.Lower.Gated.GatedHaarMinimaxComplexity

/-!
Absolute public thresholds for the manuscript's gated Haar minimax theorem.
This file only checks natural-floor and exact real arithmetic, then invokes
the already proved finite-q strict-K=1 complexity theorem. The constants
precede all physical parameters and all algorithms.
-/

namespace HeavyTailedNoise

noncomputable section

set_option autoImplicit false

universe u

def gatedPublicChainThreshold : ℝ := 64 * 330240000

def gatedPublicNoiseThreshold : ℝ := 10 ^ 7

/-- The exact threshold makes the manuscript's natural chain floor at least
64, including equality at the public boundary. -/
theorem gatedChainLength_ge64_of_public_threshold
    {A : ℝ} (hA : gatedPublicChainThreshold ≤ A) :
    64 ≤ gatedChainLength A := by
  unfold gatedChainLength
  apply Nat.le_floor
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 330240000)).2
  simpa [gatedPublicChainThreshold] using hA

/-- The public noise threshold satisfies the entry point's exact rational
large-noise inequality; monotonicity extends it to every larger `S`. -/
theorem gatedLargeNoise_of_public_threshold
    {S : ℝ} (hS : gatedPublicNoiseThreshold ≤ S) :
    2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / (16 * 300 ^ 2)) := by
  have hdiv : gatedPublicNoiseThreshold / 80 ≤ S / 80 :=
    div_le_div_of_nonneg_right hS (by norm_num)
  have hsq : (gatedPublicNoiseThreshold / 80) ^ 2 ≤ (S / 80) ^ 2 :=
    pow_le_pow_left₀ (by norm_num [gatedPublicNoiseThreshold]) hdiv 2
  calc
    2 ≤ ((1 / 4005.25 : ℝ) * (gatedPublicNoiseThreshold / 80) ^ 2 /
        (16 * 300 ^ 2)) := by norm_num [gatedPublicNoiseThreshold]
    _ ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / (16 * 300 ^ 2)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by norm_num)

/-- Concrete absolute thresholds replace the expanded chain/noise conditions
without any additional oracle, probability, or algorithm assumption. -/
theorem gatedHaar_minimax_complexity_lower_bound_of_public_thresholds
    {p q L Δ ε σ : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hA : gatedPublicChainThreshold ≤ L * Δ / ε ^ 2)
    (hS : gatedPublicNoiseThreshold ≤ σ / ε) :
    ENNReal.ofReal (gatedPublicRateConstant * (L * Δ / ε ^ 2) * (σ / ε) ^ 2) <
      (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal) := by
  have hS1 : 1 ≤ σ / ε :=
    (by norm_num [gatedPublicNoiseThreshold] : (1 : ℝ) ≤ gatedPublicNoiseThreshold).trans hS
  have hσε : ε ≤ σ := by
    simpa only [one_mul] using (le_div_iff₀ hε).1 hS1
  exact gatedHaar_minimax_complexity_lower_bound.{u}
    hp hq hL hΔ hε hσε
    (gatedChainLength_ge64_of_public_threshold hA)
    (gatedLargeNoise_of_public_threshold hS)

/-- The manuscript's absolute-constant quantifiers: one positive triple works
for every admissible finite `p,q` and all physical parameters in the public
large-`A`, large-`S` regime. Private randomness remains arbitrary in `u`. -/
theorem gatedHaar_minimax_complexity_absolute_constants :
    ∃ cG AG SG : ℝ, 0 < cG ∧ 0 < AG ∧ 0 < SG ∧
      ∀ p q L Δ ε σ : ℝ,
        (1 < p ∧ p ≤ 2) → 1 ≤ q → 0 < L → 0 < Δ → 0 < ε →
        AG ≤ L * Δ / ε ^ 2 → SG ≤ σ / ε →
        ENNReal.ofReal (cG * (L * Δ / ε ^ 2) * (σ / ε) ^ 2) <
          (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal) := by
  refine ⟨gatedPublicRateConstant, gatedPublicChainThreshold, gatedPublicNoiseThreshold,
    by norm_num [gatedPublicRateConstant], by norm_num [gatedPublicChainThreshold],
    by norm_num [gatedPublicNoiseThreshold], ?_⟩
  intro p q L Δ ε σ hp hq hL hΔ hε hA hS
  exact gatedHaar_minimax_complexity_lower_bound_of_public_thresholds.{u}
    hp hq hL hΔ hε hA hS

end

end HeavyTailedNoise

#print axioms HeavyTailedNoise.gatedHaar_minimax_complexity_absolute_constants
