import HeavyTailedNoise.Lower.Fradin.ScaledChain
import HeavyTailedNoise.Lower.Fradin.NoiseInstance

/-!
The actual physical Carmon instance from public parameters. The reveal rate
uses amplitude budget 92. All moment, increment, and gap budgets are derived;
the only extra family condition is positivity of the public chain length.
-/

namespace HeavyTailedNoise.Fradin

open HeavyTailedNoise
noncomputable section

/-- Rescaling the amplitude in the existing reveal-rate calculation. -/
theorem revealParameter_chain_amplitude {ε σ p : ℝ} (hε : 0 < ε) (hp : 1 < p) :
    revealParameter 8 (σ / ((23 / 2 : ℝ) * ε)) (tailExponent p)
      (by norm_num) (tailExponent_pos hp) =
    revealParameter 92 (σ / ε) (tailExponent p)
      (by norm_num) (tailExponent_pos hp) := by
  apply Subtype.ext
  change revealRate 8 (σ / ((23 / 2 : ℝ) * ε)) (tailExponent p) =
    revealRate 92 (σ / ε) (tailExponent p)
  have hguard : σ / ((23 / 2 : ℝ) * ε) ≤ 8 ↔ σ / ε ≤ 92 := by
    rw [div_le_iff₀ (by positivity : 0 < (23 / 2 : ℝ) * ε), div_le_iff₀ hε]
    constructor <;> intro h <;> nlinarith
  unfold revealRate
  by_cases hs : σ / ε ≤ 92
  · rw [if_pos hs, if_pos (hguard.mpr hs)]
  · rw [if_neg hs, if_neg ((not_congr hguard).mpr hs)]
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring

theorem physicalChain_moment_budget {p q L ε σ : ℝ} (hp : 1 < p)
    (hL : 0 < L) (hε : 0 < ε) (hσ : 0 ≤ σ) :
    let θ := revealParameter 92 (σ / ε) (tailExponent p)
      (by norm_num) (tailExponent_pos hp)
    let α := chainScaleAlpha L ε θ q
    let β := chainScaleBeta L ε θ q
    (α * β) ^ p *
      (2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) ≤ σ ^ p := by
  let θ := revealParameter 92 (σ / ε) (tailExponent p)
    (by norm_num) (tailExponent_pos hp)
  have hθ : 0 < (θ : ℝ) := revealRate_pos (by norm_num : (0 : ℝ) < 92)
  change (chainScaleAlpha L ε θ q * chainScaleBeta L ε θ q) ^ p *
    (2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) ≤ σ ^ p
  rw [chainScaleAlpha_mul_beta hL hε hθ]
  have hnoise := noise_moment_condition_revealParameter (c := 8)
    (ε := (23 / 2 : ℝ) * ε) (σ := σ) (p := p)
    (by norm_num) (by positivity) hσ hp
  dsimp only at hnoise
  rw [revealParameter_chain_amplitude hε hp] at hnoise
  have hamplitude : 4 * ((23 / 2 : ℝ) * ε) = 46 * ε := by ring
  rw [hamplitude] at hnoise
  have hproduct : (2 * ε) ^ p * (23 : ℝ) ^ p = (46 * ε) ^ p := by
    rw [← Real.mul_rpow (by positivity) (by norm_num)]
    congr 1
    ring
  calc
    _ = 2 * ((2 * ε) ^ p * (23 : ℝ) ^ p) *
        (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) := by ring
    _ = 2 * (46 * ε) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) := by rw [hproduct]
    _ ≤ σ ^ p := hnoise

/-- The public q-increment budget is an exact identity, including q=1. -/
theorem chainScale_increment_eq {L ε θ q : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hθ : 0 < θ) (hq : 1 ≤ q) :
    (chainScaleAlpha L ε θ q * chainScaleBeta L ε θ q) ^ q * (6087 : ℝ) ^ q *
      (chainScaleBeta L ε θ q) ^ q / θ ^ (q - 1) = L ^ q := by
  have hβ := chainScaleBeta_pos (q := q) hL hε hθ
  have hq0 : 0 < q := by linarith
  have hscale : (2 * ε) * 6087 * chainScaleBeta L ε θ q =
      L * θ ^ ((q - 1) / q) := by
    unfold chainScaleBeta oracleSmoothnessBudget
    field_simp [hε.ne'] <;> ring
  have hpower : (θ ^ ((q - 1) / q)) ^ q = θ ^ (q - 1) := by
    rw [← Real.rpow_mul hθ.le]
    congr 1
    exact div_mul_cancel₀ _ hq0.ne'
  rw [chainScaleAlpha_mul_beta hL hε hθ]
  calc
    _ = ((2 * ε) * 6087 * chainScaleBeta L ε θ q) ^ q / θ ^ (q - 1) := by
      rw [Real.mul_rpow (x := (2 * ε) * 6087)
        (y := chainScaleBeta L ε θ q) (by positivity) hβ.le,
        Real.mul_rpow (x := 2 * ε) (y := (6087 : ℝ)) (by positivity) (by norm_num)]
    _ = (L * θ ^ ((q - 1) / q)) ^ q / θ ^ (q - 1) := by rw [hscale]
    _ = L ^ q := by
      rw [Real.mul_rpow hL.le (Real.rpow_nonneg hθ.le _), hpower,
        mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hθ (q - 1)).ne']

/-- The legal physical family has no remaining moment or smoothness premise. -/
def physicalChainAdmissible {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hT : 0 < chainLength L Δ ε
      (revealParameter 92 (σ / ε) (tailExponent p)
        (by norm_num) (tailExponent_pos hp.1)) q) :
    let θ := revealParameter 92 (σ / ε) (tailExponent p)
      (by norm_num) (tailExponent_pos hp.1)
    Admissible (chainLength L Δ ε θ q) Bool p q Δ σ L := by
  let θ := revealParameter 92 (σ / ε) (tailExponent p)
    (by norm_num) (tailExponent_pos hp.1)
  let α := chainScaleAlpha L ε θ q
  let β := chainScaleBeta L ε θ q
  let T := chainLength L Δ ε θ q
  have hθ : 0 < (θ : ℝ) := revealRate_pos (by norm_num : (0 : ℝ) < 92)
  exact scaledChainAdmissible T hT p q Δ σ L α β hp hq hΔ hσ hL
    (chainScaleAlpha_pos (q := q) hL hε hθ)
    (chainScaleBeta_pos (q := q) hL hε hθ) θ hθ
    (chainLength_gapBudget hL hε hθ hΔ.le)
    (physicalChain_moment_budget hp.1 hL hε hσ)
    (chainScale_increment_eq hL hε hθ hq).le

end
end HeavyTailedNoise.Fradin
