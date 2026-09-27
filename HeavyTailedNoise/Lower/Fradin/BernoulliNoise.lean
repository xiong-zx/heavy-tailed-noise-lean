import HeavyTailedNoise.Model.Basic

/-! Exact two-atom probability and moment calculations for the Fradin oracle. -/

namespace HeavyTailedNoise.Fradin

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- `true` has probability θ; `false` has probability 1-θ. -/
abbrev bernoulliLaw (θ : unitInterval) : Measure Bool :=
  bernoulliMeasure true false θ

/-- The centered multiplicative noise ξ/θ-1. -/
def noiseFactor (θ : unitInterval) (ξ : Bool) : ℝ :=
  (if ξ then 1 else 0) / (θ : ℝ) - 1

theorem integrable_bernoulliLaw (θ : unitInterval) {E : Type*}
    [NormedAddCommGroup E] (f : Bool → E) : Integrable f (bernoulliLaw θ) :=
  ProbabilityTheory.integrable_bernoulliMeasure true false θ f

theorem integral_bernoulliLaw (θ : unitInterval) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : Bool → E) :
    (∫ ξ, f ξ ∂bernoulliLaw θ) = (θ : ℝ) • f true + (1 - θ : ℝ) • f false :=
  ProbabilityTheory.integral_bernoulliMeasure true false θ f

theorem lintegral_bernoulliLaw (θ : unitInterval) (f : Bool → ℝ≥0∞) :
    (∫⁻ ξ, f ξ ∂bernoulliLaw θ) =
      ENNReal.ofReal (θ : ℝ) * f true + ENNReal.ofReal (1 - θ : ℝ) * f false := by
  unfold bernoulliLaw
  rw [bernoulliMeasure_def, lintegral_add_measure]
  simp only [← Measure.coe_nnreal_smul, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]
  rw [ENNReal.coe_nnreal_eq, ENNReal.coe_nnreal_eq]
  rfl

theorem integral_noiseFactor (θ : unitInterval) (hθ : 0 < (θ : ℝ)) :
    (∫ ξ, noiseFactor θ ξ ∂bernoulliLaw θ) = 0 := by
  rw [integral_bernoulliLaw]
  simp only [noiseFactor, Bool.false_eq_true, ↓reduceIte, zero_div, zero_sub,
    smul_eq_mul]
  field_simp [ne_of_gt hθ]
  ring

theorem noiseFactor_true_nonneg (θ : unitInterval) (hθ : 0 < (θ : ℝ)) :
    0 ≤ noiseFactor θ true := by
  dsimp [noiseFactor]
  exact sub_nonneg.mpr ((le_div_iff₀ hθ).mpr (by simpa using θ.property.2))

theorem noiseFactor_true_eq (θ : unitInterval) (hθ : 0 < (θ : ℝ)) :
    noiseFactor θ true = (1 - (θ : ℝ)) / θ := by
  dsimp [noiseFactor]
  field_simp [ne_of_gt hθ]

/-- All real moments are finite because the law has exactly two atoms. -/
theorem integrable_abs_noiseFactor_rpow (θ : unitInterval) (p : ℝ) :
    Integrable (fun ξ => |noiseFactor θ ξ| ^ p) (bernoulliLaw θ) :=
  integrable_bernoulliLaw θ _

/-- The scalar calculation works at p=1 as well as the source's p>1. -/
theorem integral_abs_noiseFactor_rpow_le (θ : unitInterval)
    (hθ : 0 < (θ : ℝ)) {p : ℝ} (hp : 1 ≤ p) :
    (∫ ξ, |noiseFactor θ ξ| ^ p ∂bernoulliLaw θ) ≤
      2 * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) := by
  have hθle : (θ : ℝ) ≤ 1 := θ.property.2
  have hθ0 : 0 ≤ (θ : ℝ) := hθ.le
  have htail : 0 ≤ 1 - (θ : ℝ) := sub_nonneg.mpr hθle
  have hpow : 0 < (θ : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos hθ _
  have hpowle : (θ : ℝ) ^ (p - 1) ≤ 1 :=
    Real.rpow_le_one hθ0 hθle (sub_nonneg.mpr hp)
  have htailpow : (1 - (θ : ℝ)) ^ p ≤ 1 - (θ : ℝ) :=
    Real.rpow_le_self_of_le_one htail (by linarith) hp
  have hident : (θ : ℝ) * ((1 - (θ : ℝ)) / θ) ^ p =
      (1 - (θ : ℝ)) ^ p / (θ : ℝ) ^ (p - 1) := by
    rw [Real.div_rpow htail hθ0, Real.rpow_sub hθ, Real.rpow_one]
    field_simp [ne_of_gt hθ, ne_of_gt (Real.rpow_pos_of_pos hθ p)]
  rw [integral_bernoulliLaw]
  simp only [smul_eq_mul, noiseFactor_true_eq θ hθ,
    abs_of_nonneg (div_nonneg htail hθ0)]
  have hfalse : |noiseFactor θ false| ^ p = 1 := by simp [noiseFactor]
  rw [hfalse, mul_one, hident]
  have hfirst := (div_le_div_of_nonneg_right htailpow hpow.le)
  have hsecond : 1 - (θ : ℝ) ≤ (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) :=
    (le_div_iff₀ hpow).mpr (by nlinarith)
  calc
    _ ≤ (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) +
        (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) := add_le_add hfirst hsecond
    _ = 2 * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) := by ring

end
end HeavyTailedNoise.Fradin
