import HeavyTailedNoise.Upper.K1.CoarseTrackerPaperScheduleGates
import HeavyTailedNoise.Upper.K1.CoarseTrackerActualBounds

/-!
The actual adaptive coarse tracker's shifted exponential tail for the
literal paper schedule with the legal fixed choice `c_h = 1/8`.  The event
is measured on the complete private and fresh-seed path; every runtime
boundary through `T` is covered.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem Admissible.paperSchedule_eighth_tracker_shifted_tail
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    (t : ℕ)
    (ht : t ≤ (paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI).T)
    (x : ℝ) :
    let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
    let δ := (1 / 8 : ℝ) *
      (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
    let lam := δ / C ^ 2
    (((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))).real
      {z | x ≤ actualTrackerAtBoundary P I t z -
        actualTrackerAtBoundary P I 0 z -
          (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + C)}) ≤
      163 * Real.exp (-lam * x) := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  have hgate := paperSchedule_eighth_tracker_gates
    p q Δ σ Lbar ε Ctail κ Cb CI hε I.Lbar_pos hCb hCI
  change 0 < P.beta ∧ P.beta ≤ 1 / 4 ∧ 0 ≤ P.h ∧
    12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ∧
    Lbar * P.h ≤ P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8 at hgate
  obtain ⟨hbeta, hbeta_le, hh, hscale, hmove⟩ := hgate
  have htP : t ≤ P.T := ht
  have htail := actualTracker_shifted_tail_concrete P I
    hbeta hbeta_le hh hscale hmove t htP x
  simpa only [P] using htail

end

end HeavyTailedNoise.UpperK1
