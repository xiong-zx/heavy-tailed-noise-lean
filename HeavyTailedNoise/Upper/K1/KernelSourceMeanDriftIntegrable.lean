import HeavyTailedNoise.Upper.K1.KernelSourceMeanDrift

/-!
The mixed same-seed integrand in the source-mean drift inequality is
integrable without any new moment assumption. The terminal dyadic cutoff
bounds its coefficient, while ordinary oracle response integrability controls
the same-seed residual difference. Quantitative q-WAS/Hölder bounds are a
separate next step.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem paperSchedule_kernel_mix_integrable
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar)
    (x x' w w' : Point d) :
    Integrable (fun ξ : Seed =>
      2 * ‖(I.oracle.response x' ξ - w') -
        (I.oracle.response x ξ - w)‖ *
        (((2 : ℝ) ^ paperSexp p q /
          ((2 : ℝ) ^ paperSexp p q - 1)) *
          (min ((max ‖I.oracle.response x' ξ - w'‖
              ‖I.oracle.response x ξ - w‖) / paperNu σ ε)
            (12 * (2 : ℝ) ^ paperJ p σ ε Ctail)) ^ paperSexp p q))
      I.oracle.law := by
  let s := paperSexp p q
  let ν := paperNu σ ε
  let U : ℝ := 12 * (2 : ℝ) ^ paperJ p σ ε Ctail
  let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
  let X : Seed → Point d := fun ξ => I.oracle.response x ξ - w
  let Y : Seed → Point d := fun ξ => I.oracle.response x' ξ - w'
  let D : Seed → Point d := fun ξ => Y ξ - X ξ
  let R : Seed → ℝ := fun ξ => max ‖Y ξ‖ ‖X ξ‖
  let F : Seed → ℝ := fun ξ =>
    2 * ‖D ξ‖ * (C * (min (R ξ / ν) U) ^ s)
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  have hν : 0 < ν := paperNu_pos (σ := σ) hε
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos (lt_trans zero_lt_one hp)
    apply sub_pos.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa using hq)
  have htwo : 1 < (2 : ℝ) ^ s :=
    Real.one_lt_rpow (by norm_num) hs
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hX : Integrable X I.oracle.law :=
    (I.integrable_response x).sub (integrable_const _)
  have hY : Integrable Y I.oracle.law :=
    (I.integrable_response x').sub (integrable_const _)
  have hD : Integrable D I.oracle.law := hY.sub hX
  have hresponse (a : Point d) : Measurable (I.oracle.response a) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hXm : Measurable X := (hresponse x).sub measurable_const
  have hYm : Measurable Y := (hresponse x').sub measurable_const
  have hDm : Measurable D := hYm.sub hXm
  have hRm : Measurable R := hYm.norm.max hXm.norm
  have hminMeas : Measurable (fun ξ => min (R ξ / ν) U) :=
    (hRm.div_const ν).min measurable_const
  have hFm : Measurable F := by
    exact (measurable_const.mul hDm.norm).mul
      (measurable_const.mul
        ((Real.continuous_rpow_const hs.le).measurable.comp hminMeas))
  have hfactor (ξ : Seed) : C * (min (R ξ / ν) U) ^ s ≤ C * U ^ s := by
    have hR : 0 ≤ R ξ :=
      (norm_nonneg (Y ξ)).trans (le_max_left _ _)
    have hmin : 0 ≤ min (R ξ / ν) U :=
      le_min (div_nonneg hR hν.le) hU
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hmin (min_le_right _ _) hs.le) hC
  have hbound (ξ : Seed) : ‖F ξ‖ ≤ (2 * (C * U ^ s)) * ‖D ξ‖ := by
    have hpow : 0 ≤ (min (R ξ / ν) U) ^ s := by positivity
    have hFn : 0 ≤ F ξ := by
      dsimp [F]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hFn]
    calc
      F ξ = 2 * ‖D ξ‖ * (C * (min (R ξ / ν) U) ^ s) := rfl
      _ ≤ 2 * ‖D ξ‖ * (C * U ^ s) :=
        mul_le_mul_of_nonneg_left (hfactor ξ) (by positivity)
      _ = (2 * (C * U ^ s)) * ‖D ξ‖ := by ring
  have hFInt : Integrable F I.oracle.law :=
    Integrable.mono' (hD.norm.const_mul (2 * (C * U ^ s)))
      hFm.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  simpa only [F, D, X, Y, R, C, U, ν, s] using hFInt

/-- The same-seed source-mean drift bridge now has no auxiliary
integrability premise; the quantitative q-WAS/Hölder estimate is downstream. -/
theorem paperSchedule_highBand_sourceMean_drift_le_mixed
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar)
    (x x' w w' : Point d) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    (∑ j : Fin P.J,
      (12 * (2 : ℝ) ^ j.val) ^ paperSexp p q *
        ‖upperResidualSourceMean I.oracle (highBand P j) x' w' -
          upperResidualSourceMean I.oracle (highBand P j) x w‖) ≤
      ∫ ξ : Seed,
        2 * ‖(I.oracle.response x' ξ - w') -
          (I.oracle.response x ξ - w)‖ *
          (((2 : ℝ) ^ paperSexp p q /
            ((2 : ℝ) ^ paperSexp p q - 1)) *
            (min ((max ‖I.oracle.response x' ξ - w'‖
                ‖I.oracle.response x ξ - w‖) / paperNu σ ε)
              (12 * (2 : ℝ) ^ paperJ p σ ε Ctail)) ^ paperSexp p q)
        ∂I.oracle.law :=
  paperSchedule_highBand_sourceMean_drift_le_of_mix_integrable
    p q Δ σ Lbar ε Ctail ch κ Cb CI
    hp hq hε hch hCb hCI I x x' w w'
    (paperSchedule_kernel_mix_integrable
      p q Δ σ Lbar ε Ctail ch κ Cb CI
      hp hq hε hch hCb hCI I x x' w w')

end

end HeavyTailedNoise.UpperK1
