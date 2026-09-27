import HeavyTailedNoise.Lower.Fradin.Parameters
import HeavyTailedNoise.Lower.Gated.GatedHaarPublicRegime

/-!
Truthful composition with the proved gated branch. The arbitrary-algorithm
baseline is an explicit premise: this file does not assert that the physical
Bernoulli chain lift has already been closed.
-/

namespace HeavyTailedNoise.RandomizedLift

open HeavyTailedNoise.Fradin
open scoped ENNReal
noncomputable section
set_option autoImplicit false
universe u

def baselineRate (A B q : ℝ) : ℝ := A + B + A * B ^ (1 / q)

def outsideGatedFactor : ℝ :=
  gatedPublicChainThreshold + gatedPublicNoiseThreshold ^ 2 + 1

def combinedRateConstant (cB : ℝ) : ℝ :=
  min (cB / outsideGatedFactor) gatedPublicRateConstant

theorem outsideGatedFactor_ge_one : 1 ≤ outsideGatedFactor := by
  norm_num [outsideGatedFactor, gatedPublicChainThreshold, gatedPublicNoiseThreshold]

theorem outsideGatedFactor_pos : 0 < outsideGatedFactor :=
  lt_of_lt_of_le zero_lt_one outsideGatedFactor_ge_one

theorem combinedRateConstant_pos {cB : ℝ} (hcB : 0 < cB) :
    0 < combinedRateConstant cB := by
  apply lt_min
  · exact div_pos hcB outsideGatedFactor_pos
  · norm_num [gatedPublicRateConstant]

theorem tailExponent_ge_two {p : ℝ} (hp : 1 < p ∧ p ≤ 2) :
    2 ≤ tailExponent p := by
  unfold tailExponent
  apply (le_div_iff₀ (by linarith : 0 < p - 1)).2
  linarith

theorem max_one_ratio_sq_le_one_add_noise {p t : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (ht : 0 ≤ t) :
    (max 1 t) ^ 2 ≤ 1 + t ^ tailExponent p := by
  by_cases ht1 : t ≤ 1
  · rw [max_eq_left ht1]
    have hB := Real.rpow_nonneg ht (tailExponent p)
    nlinarith
  · have h1t : 1 ≤ t := (lt_of_not_ge ht1).le
    rw [max_eq_right h1t]
    have h := Real.rpow_le_rpow_of_exponent_le h1t (tailExponent_ge_two hp)
    rw [Real.rpow_two] at h
    linarith

theorem baselineRate_nonneg {A B q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ baselineRate A B q := by
  unfold baselineRate
  positivity

theorem baselineRate_ge_A {A B q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A ≤ baselineRate A B q := by
  have ht := mul_nonneg hA (Real.rpow_nonneg hB (1 / q))
  unfold baselineRate
  linarith

theorem baselineRate_ge_B {A B q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    B ≤ baselineRate A B q := by
  have ht := mul_nonneg hA (Real.rpow_nonneg hB (1 / q))
  unfold baselineRate
  linarith

/-- The complement of the gated regime is controlled by the baseline:
small A uses r≥2; bounded noise uses the public SG² factor. -/
theorem max_rate_le_baseline_outside_gated {A t p q : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hp : 1 < p ∧ p ≤ 2)
    (houtside : ¬ (gatedPublicChainThreshold ≤ A ∧ gatedPublicNoiseThreshold ≤ t)) :
    max (baselineRate A (t ^ tailExponent p) q) (A * (max 1 t) ^ 2) ≤
      outsideGatedFactor * baselineRate A (t ^ tailExponent p) q := by
  let B := t ^ tailExponent p
  let X := baselineRate A B q
  have hB : 0 ≤ B := Real.rpow_nonneg ht _
  have hX : 0 ≤ X := baselineRate_nonneg hA hB
  have hAX : A ≤ X := baselineRate_ge_A hA hB
  have hBX : B ≤ X := baselineRate_ge_B hA hB
  have hDX : X ≤ outsideGatedFactor * X := by
    nlinarith [outsideGatedFactor_ge_one]
  have hY : A * (max 1 t) ^ 2 ≤ outsideGatedFactor * X := by
    by_cases hAG : gatedPublicChainThreshold ≤ A
    · have htG : t ≤ gatedPublicNoiseThreshold := by
        exact (lt_of_not_ge (fun htG => houtside ⟨hAG, htG⟩)).le
      have hSG : 1 ≤ gatedPublicNoiseThreshold := by norm_num [gatedPublicNoiseThreshold]
      have hmax : max 1 t ≤ gatedPublicNoiseThreshold := max_le hSG htG
      have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ max 1 t) hmax 2
      calc
        _ ≤ A * gatedPublicNoiseThreshold ^ 2 := mul_le_mul_of_nonneg_left hsq hA
        _ ≤ X * gatedPublicNoiseThreshold ^ 2 := mul_le_mul_of_nonneg_right hAX (sq_nonneg _)
        _ ≤ outsideGatedFactor * X := by
          have hAG0 : 0 ≤ gatedPublicChainThreshold := by norm_num [gatedPublicChainThreshold]
          unfold outsideGatedFactor
          nlinarith
    · have hAGle : A ≤ gatedPublicChainThreshold := (lt_of_not_ge hAG).le
      have hsq := max_one_ratio_sq_le_one_add_noise hp ht
      have hprod : A * B ≤ gatedPublicChainThreshold * X :=
        (mul_le_mul_of_nonneg_right hAGle hB).trans
          (mul_le_mul_of_nonneg_left hBX (by norm_num [gatedPublicChainThreshold]))
      calc
        _ ≤ A * (1 + B) := mul_le_mul_of_nonneg_left hsq hA
        _ ≤ (gatedPublicChainThreshold + 1) * X := by nlinarith
        _ ≤ outsideGatedFactor * X := by
          unfold outsideGatedFactor
          nlinarith [sq_nonneg gatedPublicNoiseThreshold]
  exact max_le hDX hY

/-- Conditional final-rate bridge in the existing literal minimax model.
The baseline premise must be proved for unrestricted shared-model algorithms
before this result can become the public combined lower theorem. -/
theorem combined_minimax_lower_bound_of_baseline
    {p q L Δ ε σ cB : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hcB : 0 < cB)
    (hbaseline : ENNReal.ofReal (cB * baselineRate (L * Δ / ε ^ 2)
        ((σ / ε) ^ tailExponent p) q) <
      (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal)) :
    ENNReal.ofReal (combinedRateConstant cB *
      max (baselineRate (L * Δ / ε ^ 2) ((σ / ε) ^ tailExponent p) q)
        ((L * Δ / ε ^ 2) * (max 1 (σ / ε)) ^ 2)) <
      (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal) := by
  let A := L * Δ / ε ^ 2
  let t := σ / ε
  let X := baselineRate A (t ^ tailExponent p) q
  let Y := A * (max 1 t) ^ 2
  let c := combinedRateConstant cB
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ht : 0 ≤ t := div_nonneg hσ hε.le
  have hX : 0 ≤ X := baselineRate_nonneg hA (Real.rpow_nonneg ht _)
  have hY : 0 ≤ Y := mul_nonneg hA (sq_nonneg _)
  have hc : 0 < c := combinedRateConstant_pos hcB
  have hcD : c ≤ cB / outsideGatedFactor := min_le_left _ _
  have hcG : c ≤ gatedPublicRateConstant := min_le_right _ _
  have hcB' : c ≤ cB := hcD.trans <|
    (div_le_iff₀ outsideGatedFactor_pos).2 (by nlinarith [outsideGatedFactor_ge_one])
  change ENNReal.ofReal (c * max X Y) < _
  by_cases hlarge : gatedPublicChainThreshold ≤ A ∧ gatedPublicNoiseThreshold ≤ t
  · have hG := gatedHaar_minimax_complexity_lower_bound_of_public_thresholds.{u}
      hp hq hL hΔ hε hlarge.1 hlarge.2
    have ht1 : 1 ≤ t := (by norm_num [gatedPublicNoiseThreshold] :
      (1 : ℝ) ≤ gatedPublicNoiseThreshold).trans hlarge.2
    have hYeq : Y = A * t ^ 2 := by dsimp [Y]; rw [max_eq_right ht1]
    rcases le_total X Y with hXY | hYX
    · rw [max_eq_right hXY]
      apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcG hY)).trans_lt
      simpa only [hYeq, mul_assoc] using hG
    · rw [max_eq_left hYX]
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcB' hX)).trans_lt hbaseline
  · have hmax := max_rate_le_baseline_outside_gated (q := q) hA ht hp hlarge
    have hrate : c * max X Y ≤ cB * X := by
      calc
        _ ≤ c * (outsideGatedFactor * X) := mul_le_mul_of_nonneg_left hmax hc.le
        _ = (c * outsideGatedFactor) * X := by ring
        _ ≤ cB * X := mul_le_mul_of_nonneg_right
          ((le_div_iff₀ outsideGatedFactor_pos).1 hcD) hX
    exact (ENNReal.ofReal_le_ofReal hrate).trans_lt hbaseline

end
end HeavyTailedNoise.RandomizedLift
