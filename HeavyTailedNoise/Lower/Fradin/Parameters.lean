import HeavyTailedNoise.Model.Basic

/-! Public first-order scaling. The reveal rate handles zero noise explicitly:
S≤c uses the noiseless rate 1, so no inverse of zero defines an oracle law. -/

namespace HeavyTailedNoise.Fradin
noncomputable section
set_option autoImplicit false

/-- Uniform actual increment budget for the C² selector; its oracle proof is separate. -/
def oracleSmoothnessBudget : ℝ := 6087

def tailExponent (p : ℝ) : ℝ := p / (p-1)

def revealRate (c S r : ℝ) : ℝ := if S ≤ c then 1 else (c/S)^r

theorem tailExponent_pos {p : ℝ} (hp : 1 < p) : 0 < tailExponent p := by
  unfold tailExponent
  exact div_pos (by linarith) (by linarith)

theorem revealRate_pos {c S r : ℝ} (hc : 0 < c) : 0 < revealRate c S r := by
  unfold revealRate
  split_ifs with hS
  · norm_num
  · exact Real.rpow_pos_of_pos (div_pos hc (hc.trans (lt_of_not_ge hS))) r

theorem revealRate_le_one {c S r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    revealRate c S r ≤ 1 := by
  unfold revealRate
  split_ifs with hS
  · exact le_rfl
  · have hSpos : 0 < S := hc.trans (lt_of_not_ge hS)
    apply Real.rpow_le_one (div_nonneg hc.le hSpos.le)
    · exact (div_le_one hSpos).2 (lt_of_not_ge hS).le
    · exact hr.le

theorem revealRate_eq_one {c S r : ℝ} (hS : S ≤ c) : revealRate c S r = 1 := by
  simp [revealRate, hS]

def revealParameter (c S r : ℝ) (hc : 0 < c) (hr : 0 < r) : unitInterval :=
  ⟨revealRate c S r, ⟨(revealRate_pos hc).le, revealRate_le_one hc hr⟩⟩

def chainScaleBeta (L ε θ q : ℝ) : ℝ :=
  L * θ ^ ((q-1)/q) / (2*ε*oracleSmoothnessBudget)

def chainScaleAlpha (L ε θ q : ℝ) : ℝ := 2*ε / chainScaleBeta L ε θ q

def chainLength (L Δ ε θ q : ℝ) : ℕ := ⌊Δ/(12*chainScaleAlpha L ε θ q)⌋₊

theorem chainScaleBeta_pos {L ε θ q : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hθ : 0 < θ) : 0 < chainScaleBeta L ε θ q := by
  unfold chainScaleBeta oracleSmoothnessBudget
  exact div_pos (mul_pos hL (Real.rpow_pos_of_pos hθ _)) (by positivity)

theorem chainScaleAlpha_pos {L ε θ q : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hθ : 0 < θ) : 0 < chainScaleAlpha L ε θ q := by
  unfold chainScaleAlpha
  exact div_pos (by positivity) (chainScaleBeta_pos hL hε hθ)

theorem chainScaleAlpha_mul_beta {L ε θ q : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hθ : 0 < θ) : chainScaleAlpha L ε θ q * chainScaleBeta L ε θ q = 2*ε := by
  unfold chainScaleAlpha
  exact div_mul_cancel₀ _ (chainScaleBeta_pos hL hε hθ).ne'

theorem chainLength_gapBudget {L Δ ε θ q : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hθ : 0 < θ) (hΔ : 0 ≤ Δ) :
    chainScaleAlpha L ε θ q * (12*(chainLength L Δ ε θ q : ℝ)) ≤ Δ := by
  have hα := chainScaleAlpha_pos (q := q) hL hε hθ
  have hden : 0 < 12*chainScaleAlpha L ε θ q := by positivity
  have hf := Nat.floor_le (div_nonneg hΔ hden.le)
  have h := (le_div_iff₀ hden).1 hf
  change (chainLength L Δ ε θ q : ℝ) * (12*chainScaleAlpha L ε θ q) ≤ Δ at h
  nlinarith

end
end HeavyTailedNoise.Fradin
