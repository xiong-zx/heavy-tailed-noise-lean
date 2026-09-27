import HeavyTailedNoise.Analysis.LowerBoundArithmetic

/-!
The frozen manuscript's fixed stage-length cap `n₀`, including its `d-T`
dimension factor and the floor loss. No stopping-time expectation is used.
-/

namespace HeavyTailedNoise

/-- The manuscript's `T=floor(c_*² A/(48 ℓ₁))` after exact constants. -/
noncomputable def gatedChainLength (A : ℝ) : ℕ :=
  ⌊A / 330240000⌋₊

/-- Algebraically the manuscript's `floor ((d-T)t₀²σ₀²/(8d C²))`, with
`t₀²=1/4005.25`, `σ₀=S/80`, and `C=300`. -/
noncomputable def gatedStageLength (d T : ℕ) (S : ℝ) : ℕ :=
  let V : ℝ := (1 / 4005.25) * (S / 80) ^ 2 / 300 ^ 2
  ⌊ (((d - T : ℕ) : ℝ) * V / (8 * d)) ⌋₊

private theorem natFloor_stage_lower
    {D m V : ℝ} (hD : 0 < D) (hm : D / 2 ≤ m)
    (hV : 0 ≤ V) (hlarge : 2 ≤ V / 16) :
    V / 32 ≤ (⌊m * V / (8 * D)⌋₊ : ℝ) := by
  have hden : 0 < 8 * D := by positivity
  have hnum : D / 2 * V ≤ m * V :=
    mul_le_mul_of_nonneg_right hm hV
  have harg : V / 16 ≤ m * V / (8 * D) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hnum]
  have harg2 : 2 ≤ m * V / (8 * D) := hlarge.trans harg
  have hfloor := natFloor_ge_half_of_ge_two harg2
  linarith

/-- The dimension condition `d≥2T` and the manuscript's large-noise
condition imply the exact lower bound used in the final `AS²` constant. -/
theorem gatedStageLength_lower
    {d T : ℕ} {S : ℝ} (hd : 0 < d) (hdim : 2 * T ≤ d)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2))) :
    ((1 / 4005.25 : ℝ) * (1 / 80 : ℝ) ^ 2 /
      (32 * 300 ^ 2)) * S ^ 2 ≤ gatedStageLength d T S := by
  let D : ℝ := d
  let m : ℝ := (d - T : ℕ)
  let V : ℝ := (1 / 4005.25) * (S / 80) ^ 2 / 300 ^ 2
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast hd
  have hTle : T ≤ d := by omega
  have hm : D / 2 ≤ m := by
    have hdimReal : (2 : ℝ) * T ≤ d := by exact_mod_cast hdim
    dsimp [D, m]
    rw [Nat.cast_sub hTle]
    linarith
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlargeV : 2 ≤ V / 16 := by
    dsimp [V]
    convert hlarge using 1 <;> ring
  have h := natFloor_stage_lower hD hm hV hlargeV
  have hnum :
      ((1 / 4005.25 : ℝ) * (1 / 80 : ℝ) ^ 2 /
        (32 * 300 ^ 2)) * S ^ 2 = V / 32 := by
    dsimp [V]
    ring
  rw [hnum]
  change V / 32 ≤ gatedStageLength d T S at h
  exact h

/-- If the chosen chain has at least 64 stages, its floor loses at most a
factor of two relative to the real-valued stage count. -/
theorem gatedChainLength_lower {A : ℝ} (hA : 0 ≤ A)
    (hT64 : 64 ≤ gatedChainLength A) :
    ((1 / 40 : ℝ) ^ 2 / (96 * 4300)) * A ≤ gatedChainLength A := by
  let x : ℝ := A / 330240000
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hfloorle : ((gatedChainLength A : ℕ) : ℝ) ≤ x := by
    simpa [gatedChainLength, x] using Nat.floor_le hx
  have hT64real : (64 : ℝ) ≤ gatedChainLength A := by exact_mod_cast hT64
  have hx2 : 2 ≤ x := by linarith
  have hhalf := natFloor_ge_half_of_ge_two hx2
  have hconstant :
      ((1 / 40 : ℝ) ^ 2 / (96 * 4300)) * A = x / 2 := by
    dsimp [x]
    ring
  rw [hconstant]
  simpa [gatedChainLength, x] using hhalf

/-- The actual dimension- and parameter-chosen stage count has the frozen
coarse `10⁻²⁴ A S²` quarter-budget lower bound. -/
theorem gated_quarter_budget_actual
    {A S : ℝ} {d : ℕ} (hA : 0 ≤ A)
    (hT64 : 64 ≤ gatedChainLength A)
    (hd : 0 < d) (hdim : 2 * gatedChainLength A ≤ d)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2))) :
    (1 / 10 ^ 24 : ℝ) * A * S ^ 2 ≤
      ((gatedChainLength A : ℕ) : ℝ) *
        gatedStageLength d (gatedChainLength A) S / 4 :=
  gated_quarter_budget_ge_one_e24 A S (gatedChainLength A)
    (gatedStageLength d (gatedChainLength A) S) hA
    (gatedChainLength_lower hA hT64)
    (gatedStageLength_lower hd hdim hlarge)

end HeavyTailedNoise
