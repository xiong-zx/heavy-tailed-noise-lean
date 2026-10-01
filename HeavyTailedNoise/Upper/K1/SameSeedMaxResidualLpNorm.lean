import HeavyTailedNoise.Upper.K1.SameSeedResidualLpNormBounds

/-!
The one-seed maximum of two endpoint residual norms is controlled by the
sum of their `L^p` norms.  Its bound uses only centered `p` noise and the
deterministic tracker errors at the two endpoints.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem Admissible.same_seed_max_residual_lpNorm_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x x' w w' : Point d) :
    lpNorm (fun ξ => max ‖I.oracle.response x' ξ - w'‖
      ‖I.oracle.response x ξ - w‖)
      (ENNReal.ofReal p) I.oracle.law ≤
      (σ + ‖I.objective.grad x' - w'‖) +
        (σ + ‖I.objective.grad x - w‖) := by
  let Y : Seed → Point d := fun ξ => I.oracle.response x' ξ - w'
  let X : Seed → Point d := fun ξ => I.oracle.response x ξ - w
  let R : Seed → ℝ := fun ξ => max ‖Y ξ‖ ‖X ξ‖
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  have hpENN : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal I.p_range.1.le
  have hresponse (a : Point d) : Measurable (I.oracle.response a) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hYm : Measurable Y := (hresponse x').sub measurable_const
  have hXm : Measurable X := (hresponse x).sub measurable_const
  have hY : MemLp Y (ENNReal.ofReal p) I.oracle.law :=
    Admissible.residual_memLp I x' w'
  have hX : MemLp X (ENNReal.ofReal p) I.oracle.law :=
    Admissible.residual_memLp I x w
  have hSum : MemLp (fun ξ => ‖Y ξ‖ + ‖X ξ‖)
      (ENNReal.ofReal p) I.oracle.law := by
    apply (hY.norm.add hX.norm).congr_norm
      ((hYm.norm.add hXm.norm).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun ξ => by
      simp only [Pi.add_apply]
  have hRle : lpNorm R (ENNReal.ofReal p) I.oracle.law ≤
      lpNorm (fun ξ => ‖Y ξ‖ + ‖X ξ‖)
        (ENNReal.ofReal p) I.oracle.law := by
    apply lpNorm_mono_real hSum
    intro ξ
    have hR0 : 0 ≤ R ξ :=
      (norm_nonneg (Y ξ)).trans (le_max_left _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hR0]
    exact max_le (by linarith [norm_nonneg (X ξ)])
      (by linarith [norm_nonneg (Y ξ)])
  have hSumLe : lpNorm (fun ξ => ‖Y ξ‖ + ‖X ξ‖)
      (ENNReal.ofReal p) I.oracle.law ≤
      lpNorm Y (ENNReal.ofReal p) I.oracle.law +
        lpNorm X (ENNReal.ofReal p) I.oracle.law := by
    have hfun : (fun ξ => ‖Y ξ‖ + ‖X ξ‖) =
        (fun ξ => ‖Y ξ‖) + (fun ξ => ‖X ξ‖) := by
      funext ξ
      rfl
    rw [hfun]
    calc
      lpNorm ((fun ξ => ‖Y ξ‖) + (fun ξ => ‖X ξ‖))
          (ENNReal.ofReal p) I.oracle.law ≤
        lpNorm (fun ξ => ‖Y ξ‖) (ENNReal.ofReal p) I.oracle.law +
          lpNorm (fun ξ => ‖X ξ‖) (ENNReal.ofReal p) I.oracle.law :=
        lpNorm_add_le hY.norm hpENN
      _ = lpNorm Y (ENNReal.ofReal p) I.oracle.law +
          lpNorm X (ENNReal.ofReal p) I.oracle.law := by
        rw [lpNorm_norm hY.aestronglyMeasurable,
          lpNorm_norm hX.aestronglyMeasurable]
  calc
    lpNorm R (ENNReal.ofReal p) I.oracle.law ≤
        lpNorm (fun ξ => ‖Y ξ‖ + ‖X ξ‖)
          (ENNReal.ofReal p) I.oracle.law := hRle
    _ ≤ lpNorm Y (ENNReal.ofReal p) I.oracle.law +
        lpNorm X (ENNReal.ofReal p) I.oracle.law := hSumLe
    _ ≤ (σ + ‖I.objective.grad x' - w'‖) +
        (σ + ‖I.objective.grad x - w‖) :=
      add_le_add (Admissible.residual_lpNorm_le I x' w')
        (Admissible.residual_lpNorm_le I x w)

end

end HeavyTailedNoise.UpperK1
