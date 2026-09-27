import HeavyTailedNoise.Lower.Gated.LowerBoundDimensionChoice

/-!
The final public dimension for both the pinhole and full-horizon accident
estimates. It depends only on `T,N,S`, before any algorithm, private seed, or
response is chosen. The larger dimension's actual stage floor is bounded anew
by the universal noise-only upper bound; no equality with the old floor is used.
-/

namespace HeavyTailedNoise

noncomputable section

/-- Residual dimension sufficient for the sharp cap theorem and accident
allowance `1/10`, with two units of logarithmic slack. -/
def gatedAccidentResidualRequirement (T N : ℕ) : ℝ :=
  2048 * (hardRadius T) ^ 2 * (Real.log (20 * (N + 2 : ℕ) * T) + 2)

/-- Extend the existing public pinhole dimension by the accident requirement.
The final `+T` makes the residual dimension contain the entire added ceiling.
-/
def gatedFullDimensionChoice (T N : ℕ) (S : ℝ) : ℕ :=
  gatedDimensionChoice T N S + ⌈gatedAccidentResidualRequirement T N⌉₊ + T

theorem gatedFullDimensionChoice_ge_base (T N : ℕ) (S : ℝ) :
    gatedDimensionChoice T N S ≤ gatedFullDimensionChoice T N S := by
  unfold gatedFullDimensionChoice
  omega

theorem gatedFullDimensionChoice_basic (T N : ℕ) (S : ℝ) :
    0 < gatedFullDimensionChoice T N S ∧
    2 * T ≤ gatedFullDimensionChoice T N S ∧
    N ≤ gatedFullDimensionChoice T N S := by
  have hge := gatedFullDimensionChoice_ge_base T N S
  exact ⟨(gatedDimensionChoice_pos T N S).trans_le hge,
    (gatedDimensionChoice_ge_two_chain T N S).trans hge,
    (gatedDimensionChoice_ge_response_cap T N S).trans hge⟩

theorem gatedFullDimensionChoice_residual_requirement (T N : ℕ) (S : ℝ) :
    gatedAccidentResidualRequirement T N ≤
      ((gatedFullDimensionChoice T N S - T : ℕ) : ℝ) := by
  have hceil : ⌈gatedAccidentResidualRequirement T N⌉₊ ≤
      gatedFullDimensionChoice T N S - T := by
    unfold gatedFullDimensionChoice
    omega
  exact (Nat.le_ceil (gatedAccidentResidualRequirement T N)).trans
    (by exact_mod_cast hceil)

theorem gatedAccident_log_argument_ge_one
    {T : ℕ} (hT : 0 < T) (N : ℕ) :
    (1 : ℝ) ≤ 20 * (N + 2 : ℕ) * T := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast Nat.succ_le_of_lt hT
  have hn : (2 : ℝ) ≤ (N + 2 : ℕ) := by
    exact_mod_cast (show 2 ≤ N + 2 by omega)
  have hp := mul_le_mul hn ht (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg (N + 2))
  nlinarith

/-- The same public logarithmic margin supplies the extra sharp-cap dimension
condition previously required by the checked accident probability theorem. -/
theorem gatedFullDimensionChoice_accident_dimension
    {T : ℕ} (hT : 0 < T) (N : ℕ) (S : ℝ) :
    4096 * (hardRadius T) ^ 2 ≤
      ((gatedFullDimensionChoice T N S - T : ℕ) : ℝ) := by
  have hlog : 0 ≤ Real.log (20 * (N + 2 : ℕ) * T) :=
    Real.log_nonneg (gatedAccident_log_argument_ge_one hT N)
  calc
    4096 * (hardRadius T) ^ 2 = 2048 * (hardRadius T) ^ 2 * 2 := by ring
    _ ≤ 2048 * (hardRadius T) ^ 2 * (Real.log (20 * (N + 2 : ℕ) * T) + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ ((gatedFullDimensionChoice T N S - T : ℕ) : ℝ) :=
      gatedFullDimensionChoice_residual_requirement T N S

/-- The coefficient in the full-horizon accident theorem is at most `1/10`
for the final public dimension. This lemma assumes no algorithmic premise. -/
theorem gatedFullDimensionChoice_accident_allowance
    {T : ℕ} (hT : 0 < T) (N : ℕ) (S : ℝ) :
    2 * (N + 2 : ℕ) * T *
      Real.exp (-((gatedFullDimensionChoice T N S - T : ℕ) : ℝ) /
        (2048 * (hardRadius T) ^ 2)) ≤ (1 / 10 : ℝ) := by
  let a : ℝ := 20 * (N + 2 : ℕ) * T
  let den : ℝ := 2048 * (hardRadius T) ^ 2
  let D : ℝ := ((gatedFullDimensionChoice T N S - T : ℕ) : ℝ)
  have ha : 0 < a := (by norm_num : (0 : ℝ) < 1).trans_le
    (gatedAccident_log_argument_ge_one hT N)
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < hardRadius T := by unfold hardRadius; positivity
  have hden : 0 < den := by dsimp [den]; positivity
  have hreq : den * (Real.log a + 2) ≤ D :=
    gatedFullDimensionChoice_residual_requirement T N S
  have hquot : Real.log a + 2 ≤ D / den :=
    (le_div_iff₀ hden).2 (by simpa only [mul_comm] using hreq)
  have hexp : Real.exp (-D / den) ≤ a⁻¹ := by
    calc
      Real.exp (-D / den) ≤ Real.exp (-Real.log a) :=
        Real.exp_le_exp.mpr (by
          rw [neg_div]
          exact neg_le_neg (by linarith))
      _ = a⁻¹ := by rw [Real.exp_neg, Real.exp_log ha]
  change 2 * (N + 2 : ℕ) * T * Real.exp (-D / den) ≤ (1 / 10 : ℝ)
  calc
    2 * (N + 2 : ℕ) * T * Real.exp (-D / den) ≤
        2 * (N + 2 : ℕ) * T * a⁻¹ :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (1 / 10 : ℝ) * (a * a⁻¹) := by dsimp [a]; ring
    _ = (1 / 10 : ℝ) := by rw [mul_inv_cancel₀ ha.ne', mul_one]

/-- Recheck the original pinhole logarithm at the *new* stage floor, using
`n₀(dFull,T,S)≤B(S)`. The stage length is not frozen when the dimension grows.
-/
theorem gatedFullDimensionChoice_log_stageLength
    (T N : ℕ) (S : ℝ)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2))) :
    21400 * (1 + Real.log
      (2 * (gatedStageLength (gatedFullDimensionChoice T N S) T S : ℝ))) ≤
        ((gatedFullDimensionChoice T N S - T : ℕ) : ℝ) := by
  obtain ⟨hd, hdim, _⟩ := gatedFullDimensionChoice_basic T N S
  have hn := gatedStageLength_ge_two hd hdim hlarge
  have hnR : (2 : ℝ) ≤ gatedStageLength (gatedFullDimensionChoice T N S) T S := by
    exact_mod_cast hn
  have hupper := gatedStageLength_upper_noiseOnly (T := T) (S := S) hd
  have hlog : Real.log (2 * (gatedStageLength (gatedFullDimensionChoice T N S) T S : ℝ)) ≤
      Real.log (2 * gatedStageLengthNoiseUpper S) :=
    Real.log_le_log (by linarith) (by linarith)
  have hge := gatedFullDimensionChoice_ge_base T N S
  have hres : ((gatedDimensionChoice T N S - T : ℕ) : ℝ) ≤
      ((gatedFullDimensionChoice T N S - T : ℕ) : ℝ) := by
    exact_mod_cast (show gatedDimensionChoice T N S - T ≤
      gatedFullDimensionChoice T N S - T by omega)
  calc
    _ ≤ 21400 * (1 + Real.log (2 * gatedStageLengthNoiseUpper S)) := by linarith
    _ ≤ ((gatedDimensionChoice T N S - T : ℕ) : ℝ) :=
      gatedDimensionChoice_log_upper T N S
    _ ≤ ((gatedFullDimensionChoice T N S - T : ℕ) : ℝ) := hres

/-- A single public dimension now closes the pinhole and accident numerical
premises simultaneously. Its only inputs are the public `T,N,S`. -/
theorem gatedFullDimensionChoice_conditions
    {T : ℕ} (hT : 0 < T) (N : ℕ) (S : ℝ)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2))) :
    let d := gatedFullDimensionChoice T N S
    0 < d ∧ 2 * T ≤ d ∧ N ≤ d ∧ 2 ≤ gatedStageLength d T S ∧
      21400 * (1 + Real.log (2 * (gatedStageLength d T S : ℝ))) ≤ ((d - T : ℕ) : ℝ) ∧
      4096 * (hardRadius T) ^ 2 ≤ ((d - T : ℕ) : ℝ) ∧
      2 * (N + 2 : ℕ) * T * Real.exp (-((d - T : ℕ) : ℝ) /
        (2048 * (hardRadius T) ^ 2)) ≤ (1 / 10 : ℝ) := by
  obtain ⟨hd, hdim, hN⟩ := gatedFullDimensionChoice_basic T N S
  exact ⟨hd, hdim, hN, gatedStageLength_ge_two hd hdim hlarge,
    gatedFullDimensionChoice_log_stageLength T N S hlarge,
    gatedFullDimensionChoice_accident_dimension hT N S,
    gatedFullDimensionChoice_accident_allowance hT N S⟩

end

end HeavyTailedNoise
