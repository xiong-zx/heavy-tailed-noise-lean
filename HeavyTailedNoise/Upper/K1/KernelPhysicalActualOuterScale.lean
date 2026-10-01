import HeavyTailedNoise.Upper.K1.KernelPhysicalTrackerMemLp
import HeavyTailedNoise.Upper.K1.KernelActualDriftOuterScale

/-!
The actual adjacent-boundary tracker errors in the literal paper schedule
have the outer-history `s = p(1-1/q)` moment required by high-band source
drift.  Both `MemLp p` premises are discharged from the single canonical
paper-schedule tracker moment; the q=1 branch has no EMA lag.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem paperSchedule_actualTracker_outer_scale_le
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hq : 1 < q)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    let μ := (algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw I.oracle (responseCount P))
    ∀ u : Fin P.T,
      (∫ z, (2 * σ + actualTrackerAtBoundary P I u.val z +
        actualTrackerAtBoundary P I (u.val + 1) z) ^
          paperSexp p q ∂μ) ≤
        (2 * σ +
          lpNorm (actualTrackerAtBoundary P I u.val)
            (ENNReal.ofReal p) μ +
          lpNorm (actualTrackerAtBoundary P I (u.val + 1))
            (ENNReal.ofReal p) μ) ^ paperSexp p q := by
  dsimp only
  intro u
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let s := paperSexp p q
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hpPos : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos hpPos
    apply sub_pos.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa using hq)
  have hsp : s ≤ p := by
    dsimp [s, paperSexp]
    apply mul_le_of_le_one_right hpPos.le
    exact sub_le_self _ (div_nonneg (by norm_num) hqpos.le)
  have hc : 0 ≤ 2 * σ := mul_nonneg (by norm_num) I.sigma_nonneg
  have hpre := paperSchedule_actualTracker_memLp
    p q Δ σ Lbar ε Ctail κ Cb CI hε hCb hCI I
    u.val (Nat.le_of_lt u.isLt)
  have hpost := paperSchedule_actualTracker_memLp
    p q Δ σ Lbar ε Ctail κ Cb CI hε hCb hCI I
    (u.val + 1) (Nat.succ_le_iff.mpr u.isLt)
  simpa only [s, P] using
    (actualTracker_pair_outer_scale_le P I u hs hsp hc hpre hpost)

end

end HeavyTailedNoise.UpperK1
