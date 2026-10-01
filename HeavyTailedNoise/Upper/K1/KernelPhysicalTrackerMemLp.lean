import HeavyTailedNoise.Upper.K1.KernelActualTrackerMemLp
import HeavyTailedNoise.Upper.K1.CoarseTrackerPaperScheduleMoment

/-!
The canonical actual tracker has `MemLp p` at every runtime boundary under
the literal paper schedule with the legal fixed step coefficient `1/8`.
The exact tracker moment is consumed from its single schedule-specific owner;
this theorem adds no oracle or algorithm assumption.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem paperSchedule_actualTracker_memLp
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar)
    (t : ℕ)
    (ht : t ≤ (paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI).T) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    MemLp (actualTrackerAtBoundary P I t) (ENNReal.ofReal p)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))) := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  have hmoment := Admissible.paperSchedule_eighth_tracker_uniform_p_moment
    I ε Ctail κ Cb CI hε hCb hCI t ht
  exact actualTrackerAtBoundary_memLp_of_p_integrable P I t hmoment.1

end

end HeavyTailedNoise.UpperK1
