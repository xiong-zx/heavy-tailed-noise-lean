import HeavyTailedNoise.Analysis.CarmonChainProperties
import HeavyTailedNoise.Lower.Fradin.BernoulliNoise
import HeavyTailedNoise.Lower.Fradin.Parameters

/-!
The one-dimensional noise family for the zero-respecting branch of Fradin v2,
Theorem 3.1. The oracle is an actual two-atom gradient estimator. Its centered
moment retains the factor `1-ρ`, including the noiseless endpoint `ρ=1`.
-/

namespace HeavyTailedNoise.Fradin

open HeavyTailedNoise MeasureTheory
open scoped ENNReal
noncomputable section

def noiseUnit : Point 1 := carmonStandardFrame 1 ⟨0, by omega⟩

theorem norm_noiseUnit : ‖noiseUnit‖ = 1 :=
  (orthonormal_carmonStandardFrame 1).norm_eq_one _

def noiseValue (L ε : ℝ) (x : Point 1) : ℝ :=
  L / 2 * ‖x‖ ^ 2 - 4 * ε * inner ℝ noiseUnit x

def noiseGradient (L ε : ℝ) (x : Point 1) : Point 1 :=
  L • x - (4 * ε) • noiseUnit

def noiseResponse (L ε : ℝ) (ρ : unitInterval) (x : Point 1) (ξ : Bool) : Point 1 :=
  L • x - ((4 * ε) / (ρ : ℝ) * (if ξ then 1 else 0)) • noiseUnit

theorem hasGradientAt_noiseValue (L ε : ℝ) (x : Point 1) :
    HasGradientAt (noiseValue L ε) (noiseGradient L ε x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (L / 2)).sub
    ((innerSL ℝ noiseUnit).hasFDerivAt.const_mul (4 * ε))
  apply h.congr_fderiv
  ext v
  simp [noiseGradient, InnerProductSpace.toDual_apply_apply,
    innerSL_apply_apply, inner_sub_left, real_inner_smul_left]
  ring

theorem contDiff_noiseValue_two (L ε : ℝ) : ContDiff ℝ 2 (noiseValue L ε) := by
  exact (contDiff_const.mul (contDiff_norm_sq ℝ)).sub
    (contDiff_const.mul (innerSL ℝ noiseUnit).contDiff)

theorem continuous_noiseGradient (L ε : ℝ) : Continuous (noiseGradient L ε) := by
  unfold noiseGradient
  fun_prop

@[simp] theorem noiseValue_zero (L ε : ℝ) : noiseValue L ε 0 = 0 := by
  simp [noiseValue]

theorem noiseValue_gap_le {L ε : ℝ} (hL : 0 < L) (hε : 0 ≤ ε) (x : Point 1) :
    noiseValue L ε 0 - noiseValue L ε x ≤ 8 * ε ^ 2 / L := by
  have hi : inner ℝ noiseUnit x ≤ ‖x‖ := by
    simpa only [norm_noiseUnit, one_mul] using real_inner_le_norm noiseUnit x
  have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 4 * ε * L)
  rw [noiseValue_zero]
  unfold noiseValue
  apply (le_div_iff₀ hL).mpr
  nlinarith [sq_nonneg (L * ‖x‖ - 4 * ε)]

theorem norm_noiseGradient_zero {L ε : ℝ} (hε : 0 ≤ ε) :
    ‖noiseGradient L ε 0‖ = 4 * ε := by
  simp [noiseGradient, norm_noiseUnit, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hε]

@[simp] theorem noiseResponse_false (L ε : ℝ) (ρ : unitInterval) (x : Point 1) :
    noiseResponse L ε ρ x false = L • x := by
  simp [noiseResponse]

@[simp] theorem noiseResponse_false_zero (L ε : ℝ) (ρ : unitInterval) :
    noiseResponse L ε ρ 0 false = 0 := by simp

theorem noiseResponse_sub_gradient (L ε : ℝ) (ρ : unitInterval)
    (x : Point 1) (ξ : Bool) :
    noiseResponse L ε ρ x ξ - noiseGradient L ε x =
      noiseFactor ρ ξ • ((-4 * ε) • noiseUnit) := by
  ext i
  simp only [noiseResponse, noiseGradient, noiseFactor, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

theorem noiseResponse_eq_gradient_add (L ε : ℝ) (ρ : unitInterval)
    (x : Point 1) (ξ : Bool) :
    noiseResponse L ε ρ x ξ =
      noiseGradient L ε x + noiseFactor ρ ξ • ((-4 * ε) • noiseUnit) := by
  have h := noiseResponse_sub_gradient L ε ρ x ξ
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

theorem measurable_noiseResponse (L ε : ℝ) (ρ : unitInterval) :
    Measurable (fun z : Point 1 × Bool => noiseResponse L ε ρ z.1 z.2) := by
  unfold noiseResponse
  have hlinear : Measurable (fun z : Point 1 × Bool => L • z.1) :=
    (continuous_fst.const_smul L).measurable
  have hscalar : Measurable (fun z : Point 1 × Bool =>
      (4 * ε) / (ρ : ℝ) * (if z.2 then (1 : ℝ) else 0)) :=
    (measurable_of_countable (fun ξ : Bool =>
      (4 * ε) / (ρ : ℝ) * (if ξ then (1 : ℝ) else 0))).comp measurable_snd
  have hunit : Measurable (fun _ : Point 1 × Bool => noiseUnit) := measurable_const
  exact hlinear.sub (hscalar.smul hunit)

def noiseOracle (L ε : ℝ) (ρ : unitInterval) : GradientOracle 1 Bool where
  law := bernoulliLaw ρ
  law_probability := inferInstance
  response := noiseResponse L ε ρ
  measurable_response := measurable_noiseResponse L ε ρ

theorem integral_noiseResponse (L ε : ℝ) (ρ : unitInterval)
    (hρ : 0 < (ρ : ℝ)) (x : Point 1) :
    (∫ ξ, noiseResponse L ε ρ x ξ ∂bernoulliLaw ρ) = noiseGradient L ε x := by
  simp_rw [noiseResponse_eq_gradient_add]
  rw [integral_add (integrable_const _) (integrable_bernoulliLaw ρ _),
    integral_const, integral_smul_const, integral_noiseFactor ρ hρ,
    zero_smul, add_zero]
  simp

theorem noiseResponse_sub (L ε : ℝ) (ρ : unitInterval)
    (x y : Point 1) (ξ : Bool) :
    noiseResponse L ε ρ x ξ - noiseResponse L ε ρ y ξ = L • (x - y) := by
  simp [noiseResponse, smul_sub]

theorem integral_noise_centered_rpow_le {L ε : ℝ} (hε : 0 ≤ ε)
    (ρ : unitInterval) (hρ : 0 < (ρ : ℝ)) (x : Point 1)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ ξ, ‖noiseResponse L ε ρ x ξ - noiseGradient L ε x‖ ^ p ∂bernoulliLaw ρ) ≤
      2 * (4 * ε) ^ p * (1 - (ρ : ℝ)) / (ρ : ℝ) ^ (p - 1) := by
  have hfun : (fun ξ => ‖noiseResponse L ε ρ x ξ - noiseGradient L ε x‖ ^ p) =
      (fun ξ => (4 * ε) ^ p * |noiseFactor ρ ξ| ^ p) := by
    funext ξ
    rw [noiseResponse_sub_gradient, norm_smul, norm_smul, norm_noiseUnit,
      mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
    have ha : |-4 * ε| = 4 * ε := by
      rw [neg_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 4 * ε)]
    rw [ha, Real.mul_rpow (abs_nonneg _) (by positivity), mul_comm]
  rw [hfun, integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (integral_abs_noiseFactor_rpow_le ρ hρ hp)
    (Real.rpow_nonneg (by positivity : 0 ≤ 4 * ε) p)
  exact h.trans_eq (by ring)

theorem noise_centered_moment_le {L ε : ℝ} (hε : 0 ≤ ε)
    (ρ : unitInterval) (hρ : 0 < (ρ : ℝ)) (x : Point 1)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ξ, ENNReal.ofReal (‖noiseResponse L ε ρ x ξ - noiseGradient L ε x‖ ^ p)
      ∂bernoulliLaw ρ) ≤
      ENNReal.ofReal (2 * (4 * ε) ^ p * (1 - (ρ : ℝ)) / (ρ : ℝ) ^ (p - 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_bernoulliLaw ρ _)
    (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) _))]
  exact ENNReal.ofReal_le_ofReal (integral_noise_centered_rpow_le hε ρ hρ x hp)

theorem noise_same_seed_increment {L ε : ℝ} (hL : 0 ≤ L) (ρ : unitInterval)
    (x y : Point 1) (q : ℝ) :
    (∫⁻ ξ, ENNReal.ofReal (‖noiseResponse L ε ρ x ξ - noiseResponse L ε ρ y ξ‖ ^ q)
      ∂bernoulliLaw ρ) = ENNReal.ofReal ((L * ‖x - y‖) ^ q) := by
  simp_rw [noiseResponse_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]
  simp

theorem noise_centered_moment_at_one {L ε : ℝ} (hε : 0 ≤ ε) (x : Point 1)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ξ, ENNReal.ofReal
      (‖noiseResponse L ε (1 : unitInterval) x ξ - noiseGradient L ε x‖ ^ p)
      ∂bernoulliLaw 1) = 0 := by
  apply le_antisymm _ (by positivity)
  simpa using noise_centered_moment_le hε (1 : unitInterval) (by norm_num) x hp

theorem noise_coarse_moment_condition {ε p σ : ℝ} (hε : 0 ≤ ε)
    (hp : 1 ≤ p) (ρ : unitInterval) (hρ : 0 < (ρ : ℝ))
    (hcoarse : (8 * ε) ^ p / (ρ : ℝ) ^ (p - 1) ≤ σ ^ p) :
    2 * (4 * ε) ^ p * (1 - (ρ : ℝ)) / (ρ : ℝ) ^ (p - 1) ≤ σ ^ p := by
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
  have hc : 2 * (4 * ε) ^ p ≤ (8 * ε) ^ p := by
    calc
      _ ≤ (2 : ℝ) ^ p * (4 * ε) ^ p :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by positivity) _)
      _ = (8 * ε) ^ p := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        congr 1
        ring
  have ht : 1 - (ρ : ℝ) ≤ 1 := by linarith [ρ.property.1]
  have hm : 2 * (4 * ε) ^ p * (1 - (ρ : ℝ)) ≤ (8 * ε) ^ p := by
    exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans (by simpa using hc)
  exact (div_le_div_of_nonneg_right hm (Real.rpow_nonneg hρ.le _)).trans hcoarse

/-- An actual legal instance. The moment premise includes the noiseless endpoint. -/
def noiseInstance {p q L Δ σ ε : ℝ} (ρ : unitInterval)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ) (hρ : 0 < (ρ : ℝ))
    (hgap : 8 * ε ^ 2 ≤ L * Δ)
    (hmoment : 2 * (4 * ε) ^ p * (1 - (ρ : ℝ)) / (ρ : ℝ) ^ (p - 1) ≤ σ ^ p) :
    Admissible 1 Bool p q Δ σ L where
  objective := {
    dimension_pos := by omega
    value := noiseValue L ε
    grad := noiseGradient L ε
    hasGradientAt := hasGradientAt_noiseValue L ε
    continuous_grad := continuous_noiseGradient L ε
    gap := fun x => (noiseValue_gap_le hL hε.le x).trans
      ((div_le_iff₀ hL).mpr (by nlinarith)) }
  oracle := noiseOracle L ε ρ
  p_range := hp
  q_range := hq
  delta_pos := hΔ
  sigma_nonneg := hσ
  Lbar_pos := hL
  integrable_response := fun x => integrable_bernoulliLaw ρ _
  unbiased := integral_noiseResponse L ε ρ hρ
  centered_moment := fun x => (noise_centered_moment_le hε.le ρ hρ x hp.1.le).trans
    (ENNReal.ofReal_le_ofReal hmoment)
  same_seed_increment := fun x y => (noise_same_seed_increment hL.le ρ x y q).le

theorem noise_moment_condition_at_one {ε p σ : ℝ} (hσ : 0 ≤ σ) :
    2 * (4 * ε) ^ p * (1 - ((1 : unitInterval) : ℝ)) /
      ((1 : unitInterval) : ℝ) ^ (p - 1) ≤ σ ^ p := by
  change 2 * (4 * ε) ^ p * (1 - (1 : ℝ)) / (1 : ℝ) ^ (p - 1) ≤ σ ^ p
  simp only [sub_self, mul_zero, zero_div]
  exact Real.rpow_nonneg hσ p

/-- A public reveal rate with any amplitude budget c≥8, including σ=0. -/
theorem noise_moment_condition_revealParameter {c ε σ p : ℝ}
    (hc : 8 ≤ c) (hε : 0 < ε) (hσ : 0 ≤ σ) (hp : 1 < p) :
    let ρ := revealParameter c (σ / ε) (tailExponent p)
      (by linarith : 0 < c) (tailExponent_pos hp)
    2 * (4 * ε) ^ p * (1 - (ρ : ℝ)) / (ρ : ℝ) ^ (p - 1) ≤ σ ^ p := by
  let ρ := revealParameter c (σ / ε) (tailExponent p)
    (by linarith : 0 < c) (tailExponent_pos hp)
  change 2 * (4 * ε) ^ p * (1 - (ρ : ℝ)) / (ρ : ℝ) ^ (p - 1) ≤ σ ^ p
  have hcpos : 0 < c := by linarith
  have hρpos : 0 < (ρ : ℝ) := revealRate_pos hcpos
  by_cases hs : σ / ε ≤ c
  · have hρ : (ρ : ℝ) = 1 := by simp [ρ, revealParameter, revealRate, hs]
    rw [hρ]
    simp [Real.rpow_nonneg hσ p]
  · have hSpos : 0 < σ / ε := hcpos.trans (lt_of_not_ge hs)
    have hσpos : 0 < σ := by
      have h := (lt_div_iff₀ hε).mp hSpos
      simpa using h
    have hpow : (ρ : ℝ) ^ (p - 1) = (c * ε) ^ p / σ ^ p := by
      have hratio : c / (σ / ε) = (c * ε) / σ := by
        field_simp [hε.ne', hσpos.ne'] <;> ring
      have hexp : tailExponent p * (p - 1) = p := by
        unfold tailExponent
        exact div_mul_cancel₀ _ (by linarith : p - 1 ≠ 0)
      change revealRate c (σ / ε) (tailExponent p) ^ (p - 1) = _
      rw [revealRate, if_neg hs,
        ← Real.rpow_mul (div_nonneg hcpos.le hSpos.le), hexp, hratio,
        Real.div_rpow (by positivity) hσpos.le]
    apply noise_coarse_moment_condition hε.le hp.le ρ hρpos
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hρpos (p - 1))).mpr
    rw [hpow, mul_div_cancel₀ _ (Real.rpow_pos_of_pos hσpos p).ne']
    apply Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_right hc hε.le) (by linarith)

def noiseInstance_revealParameter {c p q L Δ σ ε : ℝ}
    (hc : 8 ≤ c) (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L)
    (hΔ : 0 < Δ) (hε : 0 < ε) (hσ : 0 ≤ σ) (hgap : 8 * ε ^ 2 ≤ L * Δ) :
    Admissible 1 Bool p q Δ σ L :=
  noiseInstance (revealParameter c (σ / ε) (tailExponent p)
    (by linarith : 0 < c) (tailExponent_pos hp.1)) hp hq hL hΔ hε hσ
    (revealRate_pos (by linarith : 0 < c)) hgap
    (noise_moment_condition_revealParameter hc hε hσ hp.1)

end
end HeavyTailedNoise.Fradin
