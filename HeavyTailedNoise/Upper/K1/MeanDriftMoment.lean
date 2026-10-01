import HeavyTailedNoise.Upper.K1.CoarseTrackerPaperScheduleScale

/-!
The actual tracker moment controls its endpoint `Lp` norm under the literal
paper schedule.  This is a physical, dimension-free bound for the one
canonical tracker, not a new tracker hypothesis.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

private theorem lpNorm_le_root_of_nonnegative_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    {p M : ℝ} (hp : 0 < p)
    (hM : (∫ z, f z ^ p ∂μ) ≤ M) :
    lpNorm f (ENNReal.ofReal p) μ ≤ M ^ p⁻¹ := by
  have hIntegral0 : 0 ≤ ∫ z, f z ^ p ∂μ :=
    integral_nonneg (fun z => Real.rpow_nonneg (hf0 z) _)
  have hEq : lpNorm f (ENNReal.ofReal p) μ =
      (∫ z, f z ^ p ∂μ) ^ p⁻¹ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top hf.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hp.le]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
  rw [hEq]
  exact Real.rpow_le_rpow hIntegral0 hM (inv_nonneg.mpr hp.le)

/-- The `Lp` readout at any actual runtime boundary is bounded entirely by
physical parameters.  The constant is exactly the one in the certified
uniform tracker moment; it is independent of dimension and time. -/
theorem Admissible.paperSchedule_actualTracker_lpNorm_le_root
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    (t : ℕ)
    (ht : t ≤ (paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI).T) :
    let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
    let ν := paperNu σ ε
    let Cp : ℝ := 4 * (1 + (36 : ℝ) ^ p +
      815 * (243 / 8 : ℝ) ^ p)
    lpNorm (actualTrackerAtBoundary P I t) (ENNReal.ofReal p)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))) ≤
      (Cp * ν ^ p) ^ p⁻¹ := by
  dsimp only
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  let ν := paperNu σ ε
  let Cp : ℝ := 4 * (1 + (36 : ℝ) ^ p +
    815 * (243 / 8 : ℝ) ^ p)
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  have hmoment := Admissible.paperSchedule_eighth_tracker_p_moment_le_nu
    I ε Ctail κ Cb CI hε hCb hCI t ht
  change Integrable (fun z => (actualTrackerAtBoundary P I t z) ^ p) μ ∧
    (∫ z, (actualTrackerAtBoundary P I t z) ^ p ∂μ) ≤
      Cp * ν ^ p at hmoment
  exact lpNorm_le_root_of_nonnegative_moment μ
    (actualTrackerAtBoundary P I t)
    (measurable_actualTrackerAtBoundary P I t)
    (actualTrackerAtBoundary_nonneg P I t)
    (lt_trans zero_lt_one I.p_range.1) hmoment.2

end

end HeavyTailedNoise.UpperK1
