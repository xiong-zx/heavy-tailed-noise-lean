import HeavyTailedNoise.Model.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
Information estimates used by the finite-dimensional Gaussian lower-bound argument.
The binary result below is an algebraic pinhole step. It does not assert an
unproved identification of this expression with `klDiv` of two measures.
-/

noncomputable section

namespace HeavyTailedNoise

/-- The binary relative-entropy expression, written using binary entropy. -/
def binaryKLScore (p q : ℝ) : ℝ :=
  p * Real.log q⁻¹ + (1 - p) * Real.log (1 - q)⁻¹ - Real.binEntropy p

/-- Binary relative entropy pays at least the success surprisal minus one bit. -/
theorem binaryKLScore_lower {p q : ℝ} (hp : p ≤ 1) (hq₀ : 0 < q)
    (hq₁ : q < 1) :
    p * Real.log q⁻¹ - Real.log 2 ≤ binaryKLScore p q := by
  have hlog : 0 ≤ Real.log (1 - q)⁻¹ := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  have hterm : 0 ≤ (1 - p) * Real.log (1 - q)⁻¹ :=
    mul_nonneg (by linarith) hlog
  have hent : Real.binEntropy p ≤ Real.log 2 := Real.binEntropy_le_log_two
  dsimp [binaryKLScore]
  linarith

/-- Pinhole estimate after a binary KL bound has been established. -/
theorem pinhole_of_binaryKLScore_le {p q I : ℝ} (hp : p ≤ 1)
    (hq₀ : 0 < q) (hq₁ : q < 1)
    (hKL : binaryKLScore p q ≤ I) :
    p ≤ (I + Real.log 2) / Real.log q⁻¹ := by
  have hlog : 0 < Real.log q⁻¹ :=
    Real.log_pos ((one_lt_inv₀ hq₀).2 hq₁)
  have hscore := binaryKLScore_lower hp hq₀ hq₁
  apply (le_div_iff₀ hlog).2
  linarith

/-- Algebraic conversion from covariance `σ₀²/d` to the manuscript's KL scale. -/
theorem gaussian_contrast_scale {d : ℕ} (hd : 0 < d) {σ₀ : ℝ}
    (hσ : 0 < σ₀) (δ : Point d) :
    ‖δ‖ ^ 2 / (2 * (σ₀ ^ 2 / (d : ℝ))) =
      (d : ℝ) * ‖δ‖ ^ 2 / (2 * σ₀ ^ 2) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hσ' : σ₀ ≠ 0 := ne_of_gt hσ
  field_simp

/-- A uniform mean diameter bound controls the scaled squared contrast. -/
theorem gaussian_contrast_le {d : ℕ} {σ₀ C : ℝ}
    (hσ : 0 < σ₀) (hC : 0 ≤ C) {δ : Point d} (hδ : ‖δ‖ ≤ C) :
    (d : ℝ) * ‖δ‖ ^ 2 / (2 * σ₀ ^ 2) ≤
      (d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2) := by
  have hsq : ‖δ‖ ^ 2 ≤ C ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (add_nonneg (norm_nonneg δ) hC)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)

end HeavyTailedNoise
