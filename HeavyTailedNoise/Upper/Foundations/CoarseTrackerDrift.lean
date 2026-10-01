import HeavyTailedNoise.Upper.Foundations.CoarseTracker

/-!
The good-event geometry in the coarse-tracker proof of the current manuscript.
These lemmas concern the actual radial clip of the first response residual;
they do not posit a moment bound for that residual.
-/

namespace HeavyTailedNoise.UpperK1

open scoped InnerProductSpace

noncomputable section

/-- On the good event, the centered first response is far enough from the
coarse center that the clip has exactly its threshold norm. -/
theorem goodEvent_clip_norm_eq {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (e ζ : Point d) (he : 2 * τ ≤ ‖e‖) (hζ : ‖ζ‖ ≤ τ / 2) :
    ‖upperClip τ (ζ - e)‖ = τ := by
  have htriangle : ‖e‖ ≤ ‖ζ - e‖ + ‖ζ‖ := by
    calc
      ‖e‖ = ‖-(ζ - e) + ζ‖ := by congr 1; abel
      _ ≤ ‖-(ζ - e)‖ + ‖ζ‖ := norm_add_le _ _
      _ = ‖ζ - e‖ + ‖ζ‖ := by rw [neg_sub, norm_sub_rev]
  have hlarge : τ ≤ ‖ζ - e‖ := by linarith
  have hmpos : 0 < ‖ζ - e‖ := lt_of_lt_of_le hτ hlarge
  rw [upperClip_eq_scaled_of_gt hlarge, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hτ hmpos), div_mul_cancel₀ _ (ne_of_gt hmpos)]

/-- The large-error, small-source event forces the radial clip to point
inward with the quantitative factor used in the manuscript. -/
theorem goodEvent_clip_inner_le {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (e ζ : Point d) (he : 2 * τ ≤ ‖e‖) (hζ : ‖ζ‖ ≤ τ / 2) :
    ⟪e, upperClip τ (ζ - e)⟫_ℝ ≤
      -(3 / 5 : ℝ) * τ * ‖e‖ := by
  have htriangle : ‖e‖ ≤ ‖ζ - e‖ + ‖ζ‖ := by
    calc
      ‖e‖ = ‖-(ζ - e) + ζ‖ := by congr 1; abel
      _ ≤ ‖-(ζ - e)‖ + ‖ζ‖ := norm_add_le _ _
      _ = ‖ζ - e‖ + ‖ζ‖ := by rw [neg_sub, norm_sub_rev]
  have hlarge : τ ≤ ‖ζ - e‖ := by linarith
  have hmpos : 0 < ‖ζ - e‖ := lt_of_lt_of_le hτ hlarge
  have hρ4η : 4 * ‖ζ‖ ≤ ‖e‖ := by linarith
  have hmle : ‖ζ - e‖ ≤ ‖ζ‖ + ‖e‖ := norm_sub_le _ _
  have hinner0 : ⟪e, ζ - e⟫_ℝ ≤ ‖e‖ * ‖ζ‖ - ‖e‖ ^ 2 := by
    calc
      _ = ⟪e, ζ⟫_ℝ - ‖e‖ ^ 2 := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
      _ ≤ _ := sub_le_sub_right (real_inner_le_norm e ζ) _
  have hmul1 : 0 ≤ ‖e‖ * (‖e‖ - 4 * ‖ζ‖) :=
    mul_nonneg (norm_nonneg e) (sub_nonneg.mpr hρ4η)
  have hmul2 : 0 ≤ ‖e‖ * (‖e‖ + ‖ζ‖ - ‖ζ - e‖) :=
    mul_nonneg (norm_nonneg e) (sub_nonneg.mpr (by linarith))
  have hinner1 : ⟪e, ζ - e⟫_ℝ ≤
      -(3 / 5 : ℝ) * ‖e‖ * ‖ζ - e‖ := by
    nlinarith [hinner0, hmul1, hmul2]
  have hfactor : 0 ≤ τ / ‖ζ - e‖ := (div_pos hτ hmpos).le
  calc
    ⟪e, upperClip τ (ζ - e)⟫_ℝ =
        τ / ‖ζ - e‖ * ⟪e, ζ - e⟫_ℝ := by
          rw [upperClip_eq_scaled_of_gt hlarge, real_inner_smul_right]
    _ ≤ τ / ‖ζ - e‖ *
        (-(3 / 5 : ℝ) * ‖e‖ * ‖ζ - e‖) :=
          mul_le_mul_of_nonneg_left hinner1 hfactor
    _ = (τ / ‖ζ - e‖ * ‖ζ - e‖) * (-(3 / 5 : ℝ) * ‖e‖) := by ring
    _ = τ * (-(3 / 5 : ℝ) * ‖e‖) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hmpos)]
    _ = -(3 / 5 : ℝ) * τ * ‖e‖ := by ring

/-- One clipped correction contracts the tracker norm by at least half its
scaled threshold on the good event. -/
theorem goodEvent_center_contract {d : ℕ} {τ β : ℝ}
    (hτ : 0 < τ) (hβ : 0 ≤ β) (hβle : β ≤ 1 / 4)
    (e ζ : Point d) (he : 2 * τ ≤ ‖e‖) (hζ : ‖ζ‖ ≤ τ / 2) :
    ‖e + β • upperClip τ (ζ - e)‖ ≤ ‖e‖ - β * τ / 2 := by
  let c := upperClip τ (ζ - e)
  have hc : ‖c‖ = τ := goodEvent_clip_norm_eq hτ e ζ he hζ
  have hinner : ⟪e, c⟫_ℝ ≤ -(3 / 5 : ℝ) * τ * ‖e‖ :=
    goodEvent_clip_inner_le hτ e ζ he hζ
  have hβτ : β * τ ≤ ‖e‖ / 8 := by
    have h := mul_le_mul_of_nonneg_right hβle hτ.le
    nlinarith
  have hβτ0 : 0 ≤ β * τ := mul_nonneg hβ hτ.le
  have hsquare : (β * τ) ^ 2 ≤ (β * τ) * (‖e‖ / 8) := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hβτ hβτ0
  have hinnerβ : β * ⟪e, c⟫_ℝ ≤
      β * (-(3 / 5 : ℝ) * τ * ‖e‖) :=
    mul_le_mul_of_nonneg_left hinner hβ
  have hnormsq : ‖e + β • c‖ ^ 2 =
      ‖e‖ ^ 2 + 2 * β * ⟪e, c⟫_ℝ + (β * τ) ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hβ, hc]
    ring
  have htarget : 0 ≤ ‖e‖ - β * τ / 2 := by nlinarith
  have hsq : ‖e + β • c‖ ^ 2 ≤ (‖e‖ - β * τ / 2) ^ 2 := by
    rw [hnormsq]
    nlinarith [hinnerβ, hsquare, hβτ0, norm_nonneg e]
  exact (sq_le_sq₀ (norm_nonneg _) htarget).mp hsq

end

end HeavyTailedNoise.UpperK1
