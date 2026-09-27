import HeavyTailedNoise.Lower.Gated.LowerBoundPinholeParameters

/-!
An explicit dimension selected solely from the public chain length `T`,
response cap `N`, and noise ratio `S`. The floor in the stage length is bounded
above by a function of `S` alone, so the logarithmic dimension requirement is
resolved before any algorithm or private/noise tape is chosen.

This closes the public dimension premises of `LowerBoundPinholeParameters`.
It makes no claim about additional dimension requirements for a future
full-experiment accident estimate.
-/

namespace HeavyTailedNoise

noncomputable section

/-- The stage-length upper bound after dropping the residual-dimension ratio
`(d-T)/d≤1`. It depends only on the public noise ratio. -/
def gatedStageLengthNoiseUpper (S : ℝ) : ℝ :=
  (1 / 4005.25 : ℝ) * (S / 80) ^ 2 / (8 * 300 ^ 2)

/-- The actual stage floor has a dimension-independent real upper bound.
No large-noise or sign condition on `S` is needed for this upper bound. -/
theorem gatedStageLength_upper_noiseOnly
    {d T : ℕ} {S : ℝ} (hd : 0 < d) :
    (gatedStageLength d T S : ℝ) ≤ gatedStageLengthNoiseUpper S := by
  let V : ℝ := (1 / 4005.25) * (S / 80) ^ 2 / 300 ^ 2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hD : ((d - T : ℕ) : ℝ) ≤ d := by
    exact_mod_cast Nat.sub_le d T
  have harg : 0 ≤ ((d - T : ℕ) : ℝ) * V / (8 * d) := by
    positivity
  have hfloor := Nat.floor_le harg
  change (gatedStageLength d T S : ℝ) ≤
    ((d - T : ℕ) : ℝ) * V / (8 * d) at hfloor
  calc
    (gatedStageLength d T S : ℝ) ≤
        ((d - T : ℕ) : ℝ) * V / (8 * d) := hfloor
    _ ≤ V / 8 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * d)).2
      have hmul := mul_le_mul_of_nonneg_right hD hV
      nlinarith
    _ = gatedStageLengthNoiseUpper S := by
      dsimp [V, gatedStageLengthNoiseUpper]
      ring

/-- Under the existing large-noise premise the upper bound is at least four,
so its logarithm has a positive argument. -/
theorem gatedStageLengthNoiseUpper_ge_four {S : ℝ}
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2))) :
    4 ≤ gatedStageLengthNoiseUpper S := by
  have heq : gatedStageLengthNoiseUpper S =
      2 * ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / (16 * 300 ^ 2)) := by
    unfold gatedStageLengthNoiseUpper
    ring
  rw [heq]
  linarith

/-- A public dimension with a conservative response-cap term. No algorithm
type, rule, private law, or realized random tape is an input. -/
def gatedDimensionChoice (T N : ℕ) (S : ℝ) : ℕ :=
  2 * T + N +
    ⌈21400 * (1 + Real.log (2 * gatedStageLengthNoiseUpper S))⌉₊ + 1

theorem gatedDimensionChoice_pos (T N : ℕ) (S : ℝ) :
    0 < gatedDimensionChoice T N S := by
  unfold gatedDimensionChoice
  omega

theorem gatedDimensionChoice_ge_two_chain (T N : ℕ) (S : ℝ) :
    2 * T ≤ gatedDimensionChoice T N S := by
  unfold gatedDimensionChoice
  omega

theorem gatedDimensionChoice_ge_response_cap (T N : ℕ) (S : ℝ) :
    N ≤ gatedDimensionChoice T N S := by
  unfold gatedDimensionChoice
  omega

/-- The public ceiling first controls the logarithm of the pure-noise upper
bound. The extra `T+N+1` in `d-T` is nonnegative slack. -/
theorem gatedDimensionChoice_log_upper (T N : ℕ) (S : ℝ) :
    21400 * (1 + Real.log (2 * gatedStageLengthNoiseUpper S)) ≤
      ((gatedDimensionChoice T N S - T : ℕ) : ℝ) := by
  let c : ℝ := 21400 * (1 + Real.log (2 * gatedStageLengthNoiseUpper S))
  have hnat : ⌈c⌉₊ ≤ gatedDimensionChoice T N S - T := by
    unfold gatedDimensionChoice
    change ⌈c⌉₊ ≤ 2 * T + N + ⌈c⌉₊ + 1 - T
    omega
  exact (Nat.le_ceil c).trans (by exact_mod_cast hnat)

/-- The original logarithmic condition involving the actual dimension-chosen
stage floor follows from its pure-noise upper bound and the public ceiling. -/
theorem gatedDimensionChoice_log_stageLength
    (T N : ℕ) (S : ℝ)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2))) :
    21400 *
      (1 + Real.log (2 * (gatedStageLength (gatedDimensionChoice T N S) T S : ℝ))) ≤
      ((gatedDimensionChoice T N S - T : ℕ) : ℝ) := by
  have hd := gatedDimensionChoice_pos T N S
  have hdim := gatedDimensionChoice_ge_two_chain T N S
  have hn := gatedStageLength_ge_two hd hdim hlarge
  have hnR : (2 : ℝ) ≤ gatedStageLength (gatedDimensionChoice T N S) T S := by
    exact_mod_cast hn
  have hupper := gatedStageLength_upper_noiseOnly
    (T := T) (S := S) hd
  have hlog :
      Real.log (2 * (gatedStageLength (gatedDimensionChoice T N S) T S : ℝ)) ≤
        Real.log (2 * gatedStageLengthNoiseUpper S) :=
    Real.log_le_log (by linarith) (by linarith)
  calc
    21400 *
        (1 + Real.log (2 * (gatedStageLength (gatedDimensionChoice T N S) T S : ℝ))) ≤
        21400 * (1 + Real.log (2 * gatedStageLengthNoiseUpper S)) := by
      linarith
    _ ≤ ((gatedDimensionChoice T N S - T : ℕ) : ℝ) :=
      gatedDimensionChoice_log_upper T N S

/-- One explicit algorithm-independent natural dimension closes all current
public pinhole dimension premises, together with the stage-floor lower bound.
-/
theorem gatedDimensionChoice_pinhole_conditions
    (T N : ℕ) (S : ℝ)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2))) :
    let d := gatedDimensionChoice T N S
    0 < d ∧ 2 * T ≤ d ∧ N ≤ d ∧ 2 ≤ gatedStageLength d T S ∧
      21400 * (1 + Real.log (2 * (gatedStageLength d T S : ℝ))) ≤
        ((d - T : ℕ) : ℝ) := by
  exact ⟨gatedDimensionChoice_pos T N S,
    gatedDimensionChoice_ge_two_chain T N S,
    gatedDimensionChoice_ge_response_cap T N S,
    gatedStageLength_ge_two (gatedDimensionChoice_pos T N S)
      (gatedDimensionChoice_ge_two_chain T N S) hlarge,
    gatedDimensionChoice_log_stageLength T N S hlarge⟩

end

end HeavyTailedNoise
