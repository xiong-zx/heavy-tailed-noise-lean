import HeavyTailedNoise.Upper.K1.KernelActualTrackerMemLp
import HeavyTailedNoise.Upper.K1.KernelDriftOuterScale

/-!
The generic two-error outer-history power bound applied to the one actual
adaptive tracker at consecutive runtime-batch boundaries.  The `MemLp`
premises are supplied by `actualTrackerAtBoundary_memLp_of_uniform` once
the existing scalar exponential constants are chosen.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualTracker_pair_outer_scale_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) {s c : ℝ} (hs : 0 < s) (hsp : s ≤ p)
    (hc : 0 ≤ c)
    (hpre : MemLp (actualTrackerAtBoundary P I u.val)
      (ENNReal.ofReal p)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))))
    (hpost : MemLp (actualTrackerAtBoundary P I (u.val + 1))
      (ENNReal.ofReal p)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P)))) :
    let μ := (algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw I.oracle (responseCount P))
    (∫ z, (c + actualTrackerAtBoundary P I u.val z +
      actualTrackerAtBoundary P I (u.val + 1) z) ^ s ∂μ) ≤
      (c + lpNorm (actualTrackerAtBoundary P I u.val)
          (ENNReal.ofReal p) μ +
        lpNorm (actualTrackerAtBoundary P I (u.val + 1))
          (ENNReal.ofReal p) μ) ^ s := by
  dsimp only
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle (responseCount P)) :=
    freshSeedLaw_probability I.oracle (responseCount P)
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  exact integral_two_errors_rpow_le_lpNorm μ
    (actualTrackerAtBoundary P I u.val)
    (actualTrackerAtBoundary P I (u.val + 1))
    (measurable_actualTrackerAtBoundary P I u.val)
    (measurable_actualTrackerAtBoundary P I (u.val + 1))
    (actualTrackerAtBoundary_nonneg P I u.val)
    (actualTrackerAtBoundary_nonneg P I (u.val + 1))
    I.p_range.1.le hs hsp hc hpre hpost

end

end HeavyTailedNoise.UpperK1
