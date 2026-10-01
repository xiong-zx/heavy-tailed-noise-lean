import HeavyTailedNoise.Model.Basic

/-!
Radial clipping geometry for the shared-batch upper algorithm. The threshold
is positive in the algorithm; the total definition also has a value at other
thresholds. No moment, smoothness, or oracle assumption is needed here.
-/

namespace HeavyTailedNoise

open scoped InnerProductSpace

noncomputable section

/-- Radial clipping at threshold `τ`. For `0 < τ`, this is
`z * min 1 (τ / ‖z‖)`, with the zero vector sent to zero. -/
def upperClip {d : ℕ} (τ : ℝ) (z : Point d) : Point d :=
  (τ / max τ ‖z‖) • z

/-- Difference of clips at two thresholds; no ordering assumption is needed
for the definition. -/
def upperShell {d : ℕ} (τhi τlo : ℝ) (z : Point d) : Point d :=
  upperClip τhi z - upperClip τlo z

@[simp] theorem upperClip_zero {d : ℕ} (τ : ℝ) :
    upperClip τ (0 : Point d) = 0 := by
  simp [upperClip]

theorem upperClip_eq_self_of_norm_le {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    {z : Point d} (hz : ‖z‖ ≤ τ) : upperClip τ z = z := by
  simp [upperClip, max_eq_left hz, ne_of_gt hτ]

theorem upperClip_eq_scaled_of_gt {d : ℕ} {τ : ℝ} {z : Point d}
    (hz : τ ≤ ‖z‖) : upperClip τ z = (τ / ‖z‖) • z := by
  simp [upperClip, max_eq_right hz]

/-- The literal `min` formula in the manuscript, including `z = 0`. -/
theorem upperClip_eq_min_smul {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (z : Point d) : upperClip τ z = (min 1 (τ / ‖z‖)) • z := by
  by_cases hz0 : z = 0
  · subst z
    simp
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rcases le_total ‖z‖ τ with hz | hz
  · rw [upperClip_eq_self_of_norm_le hτ hz]
    have hdiv : 1 ≤ τ / ‖z‖ :=
      (le_div_iff₀ hnorm).2 (by simpa using hz)
    simp [min_eq_left hdiv]
  · rw [upperClip_eq_scaled_of_gt hz]
    have hdiv : τ / ‖z‖ ≤ 1 :=
      (div_le_iff₀ hnorm).2 (by simpa using hz)
    simp [min_eq_right hdiv]

theorem continuous_upperClip {d : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    Continuous (upperClip (d := d) τ) := by
  have hden : Continuous (fun z : Point d => max τ ‖z‖) :=
    continuous_const.max continuous_norm
  have hne (z : Point d) : max τ ‖z‖ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hτ (le_max_left τ ‖z‖))
  have hscalar : Continuous (fun z : Point d => τ / max τ ‖z‖) :=
    continuous_const.div hden hne
  exact hscalar.smul continuous_id

theorem measurable_upperClip {d : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    Measurable (upperClip (d := d) τ) :=
  (continuous_upperClip hτ).measurable

theorem upperClip_norm_le {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (z : Point d) : ‖upperClip τ z‖ ≤ τ := by
  rcases le_total ‖z‖ τ with hz | hz
  · rw [upperClip_eq_self_of_norm_le hτ hz]
    exact hz
  · rw [upperClip_eq_scaled_of_gt hz, norm_smul, Real.norm_eq_abs]
    have hnorm : 0 < ‖z‖ := lt_of_lt_of_le hτ hz
    rw [abs_of_pos (div_pos hτ hnorm), div_mul_cancel₀ _ (ne_of_gt hnorm)]

private theorem upperClip_scale_mul_norm {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (z : Point d) : τ / max τ ‖z‖ * ‖z‖ = min ‖z‖ τ := by
  rcases le_total ‖z‖ τ with hz | hz
  · simp [max_eq_left hz, min_eq_left hz, div_self (ne_of_gt hτ)]
  · have hnorm : ‖z‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le hτ hz)
    simp [max_eq_right hz, min_eq_right hz, div_mul_cancel₀ _ hnorm]

/-- Radial clipping is the metric projection onto the closed norm ball, hence
nonexpansive. This proof uses only the squared-distance identity and the
scalar `min` inequality, so it also covers a zero input vector. -/
theorem upperClip_norm_sub_le {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (u v : Point d) : ‖upperClip τ u - upperClip τ v‖ ≤ ‖u - v‖ := by
  let a : ℝ := τ / max τ ‖u‖
  let b : ℝ := τ / max τ ‖v‖
  have hdena : 0 < max τ ‖u‖ :=
    lt_of_lt_of_le hτ (le_max_left τ ‖u‖)
  have hdenb : 0 < max τ ‖v‖ :=
    lt_of_lt_of_le hτ (le_max_left τ ‖v‖)
  have ha0 : 0 ≤ a := (div_pos hτ hdena).le
  have hb0 : 0 ≤ b := (div_pos hτ hdenb).le
  have ha1 : a ≤ 1 :=
    (div_le_iff₀ hdena).2 (by simpa using (le_max_left τ ‖u‖))
  have hb1 : b ≤ 1 :=
    (div_le_iff₀ hdenb).2 (by simpa using (le_max_left τ ‖v‖))
  have hab : a * b ≤ 1 := by
    calc
      a * b ≤ a * 1 := mul_le_mul_of_nonneg_left hb1 ha0
      _ = a := mul_one a
      _ ≤ 1 := ha1
  have hmin : |min ‖u‖ τ - min ‖v‖ τ| ≤ |‖u‖ - ‖v‖| := by
    simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (‖u‖ - ‖v‖))]
      using (abs_min_sub_min_le_max ‖u‖ τ ‖v‖ τ)
  have hscalar : |a * ‖u‖ - b * ‖v‖| ≤ |‖u‖ - ‖v‖| := by
    simpa [a, b, upperClip_scale_mul_norm hτ] using hmin
  have hscalarSq : (a * ‖u‖ - b * ‖v‖) ^ 2 ≤ (‖u‖ - ‖v‖) ^ 2 :=
    sq_le_sq.mpr hscalar
  have hinner : 0 ≤ ‖u‖ * ‖v‖ - ⟪u, v⟫_ℝ :=
    sub_nonneg.mpr (real_inner_le_norm u v)
  have hfactor : 0 ≤ 2 * (1 - a * b) := by nlinarith
  have hpositive := mul_nonneg hfactor hinner
  have hsqclip : ‖a • u - b • v‖ ^ 2 =
      (a * ‖u‖) ^ 2 - 2 * a * b * ⟪u, v⟫_ℝ + (b * ‖v‖) ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ha0, abs_of_nonneg hb0,
      real_inner_smul_left, real_inner_smul_right]
    ring
  have hidentity : ‖u - v‖ ^ 2 - ‖a • u - b • v‖ ^ 2 =
      ((‖u‖ - ‖v‖) ^ 2 - (a * ‖u‖ - b * ‖v‖) ^ 2) +
        2 * (1 - a * b) * (‖u‖ * ‖v‖ - ⟪u, v⟫_ℝ) := by
    rw [norm_sub_sq_real, hsqclip]
    ring
  have hsq : ‖a • u - b • v‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
    nlinarith [hscalarSq, hpositive]
  change ‖a • u - b • v‖ ≤ ‖u - v‖
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem continuous_upperShell {d : ℕ} {τhi τlo : ℝ}
    (hhi : 0 < τhi) (hlo : 0 < τlo) :
    Continuous (upperShell (d := d) τhi τlo) := by
  exact (continuous_upperClip hhi).sub (continuous_upperClip hlo)

theorem measurable_upperShell {d : ℕ} {τhi τlo : ℝ}
    (hhi : 0 < τhi) (hlo : 0 < τlo) :
    Measurable (upperShell (d := d) τhi τlo) :=
  (continuous_upperShell hhi hlo).measurable

end

end HeavyTailedNoise
