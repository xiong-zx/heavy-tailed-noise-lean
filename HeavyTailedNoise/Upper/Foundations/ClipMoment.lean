import HeavyTailedNoise.Upper.Foundations.ClipGeometry

/-!
Pointwise clipping interpolation for centered p-moment estimates. This is a
deterministic dimension-free bound. In applications `u = g(x,ξ)-w` and
`v = ∇F(x)-w`, so the right-hand difference is the original centered noise,
not an unassumed conditional moment of `g(x,ξ)-w`.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

/-- Two clipped vectors differ by at most the original difference and by twice
the threshold. Both bounds hold for zero vectors. -/
theorem upperClip_difference_le_min {d : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (u v : Point d) :
    ‖upperClip τ u - upperClip τ v‖ ≤ min ‖u - v‖ (2 * τ) := by
  apply le_min
  · exact upperClip_norm_sub_le hτ u v
  · calc
      ‖upperClip τ u - upperClip τ v‖ ≤ ‖upperClip τ u‖ + ‖upperClip τ v‖ :=
        norm_sub_le _ _
      _ ≤ τ + τ := add_le_add (upperClip_norm_le hτ u) (upperClip_norm_le hτ v)
      _ = 2 * τ := by ring

/-- Interpolation used to convert centered p-BCM into a clipped second moment
without imposing any moment condition at a random clipping center. -/
theorem upperClip_difference_sq_le_rpow {d : ℕ} {τ p : ℝ}
    (hτ : 0 < τ) (hp : 1 < p ∧ p ≤ 2) (u v : Point d) :
    ‖upperClip τ u - upperClip τ v‖ ^ 2 ≤
      (2 * τ) ^ (2 - p) * ‖u - v‖ ^ p := by
  let a : ℝ := ‖upperClip τ u - upperClip τ v‖
  let b : ℝ := ‖u - v‖
  let M : ℝ := 2 * τ
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hap : 0 ≤ p := by linarith [hp.1]
  have h2p : 0 ≤ 2 - p := by linarith [hp.2]
  have hab : a ≤ b := (upperClip_difference_le_min hτ u v).trans
    (min_le_left _ _)
  have haM : a ≤ M := (upperClip_difference_le_min hτ u v).trans
    (min_le_right _ _)
  have hpow1 : a ^ p ≤ b ^ p := Real.rpow_le_rpow ha0 hab hap
  have hpow2 : a ^ (2 - p) ≤ M ^ (2 - p) :=
    Real.rpow_le_rpow ha0 haM h2p
  have hmul : a ^ p * a ^ (2 - p) ≤ b ^ p * M ^ (2 - p) :=
    mul_le_mul hpow1 hpow2 (Real.rpow_nonneg ha0 _) (Real.rpow_nonneg hb0 _)
  have hidentity : a ^ 2 = a ^ p * a ^ (2 - p) := by
    calc
      a ^ 2 = a ^ (2 : ℝ) := by simp
      _ = a ^ (p + (2 - p)) := by congr 1; ring
      _ = a ^ p * a ^ (2 - p) :=
        Real.rpow_add' ha0 (by norm_num : p + (2 - p) ≠ 0)
  dsimp [a, b, M] at hmul hidentity ⊢
  rw [hidentity]
  simpa only [mul_comm] using hmul

/-- With any fixed center `w`, the clipped response difference from the
clipped population gradient has a second-moment bound coming directly from
the oracle's original centered p-BCM condition. -/
theorem Admissible.upperClip_centered_difference_secondMoment
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar τ : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hτ : 0 < τ) (x w : Point d) :
    (∫⁻ ξ, ENNReal.ofReal
      (‖upperClip τ (I.oracle.response x ξ - w) -
        upperClip τ (I.objective.grad x - w)‖ ^ 2) ∂I.oracle.law) ≤
      ENNReal.ofReal ((2 * τ) ^ (2 - p) * σ ^ p) := by
  have hc : 0 ≤ (2 * τ) ^ (2 - p) :=
    Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * τ) _
  calc
    (∫⁻ ξ, ENNReal.ofReal
      (‖upperClip τ (I.oracle.response x ξ - w) -
        upperClip τ (I.objective.grad x - w)‖ ^ 2) ∂I.oracle.law) ≤
        ∫⁻ ξ, ENNReal.ofReal
          ((2 * τ) ^ (2 - p) *
            ‖I.oracle.response x ξ - I.objective.grad x‖ ^ p)
          ∂I.oracle.law := by
            apply lintegral_mono
            intro ξ
            apply ENNReal.ofReal_le_ofReal
            have h := upperClip_difference_sq_le_rpow hτ I.p_range
              (I.oracle.response x ξ - w) (I.objective.grad x - w)
            have hdiff : (I.oracle.response x ξ - w) -
                (I.objective.grad x - w) =
                  I.oracle.response x ξ - I.objective.grad x := by abel
            rw [hdiff] at h
            exact h
    _ = ENNReal.ofReal ((2 * τ) ^ (2 - p)) *
          ∫⁻ ξ, ENNReal.ofReal
            (‖I.oracle.response x ξ - I.objective.grad x‖ ^ p)
            ∂I.oracle.law := by
              simp_rw [ENNReal.ofReal_mul hc]
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((2 * τ) ^ (2 - p)) * ENNReal.ofReal (σ ^ p) := by
      simpa only [mul_comm] using
        (mul_le_mul_left (I.centered_moment x)
          (ENNReal.ofReal ((2 * τ) ^ (2 - p))))
    _ = ENNReal.ofReal ((2 * τ) ^ (2 - p) * σ ^ p) := by
      rw [ENNReal.ofReal_mul hc]

end

end HeavyTailedNoise
