import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialState
import HeavyTailedNoise.Upper.K1.CoarseTrackerAdaptiveLyapunov
import HeavyTailedNoise.Upper.K1.CoarseTrackerMomentFromExp

/-!
The actual adaptive coarse tracker has a uniform `p`-moment once the
physical scalar exponential coefficient is chosen.  The initial heavy-tail
moment and the bounded-excursion moment are kept separate throughout.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped NNReal

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualTracker_uniform_p_moment
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hbeta : 0 ≤ P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hscale : 12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8)
    (lam K : ℝ) (hlam : 0 < lam) (hKbase : 1 ≤ K)
    (hKstep : trackerMGFContraction P Lbar lam * K + 1 ≤ K)
    (t : ℕ) (ht : t ≤ P.T) :
    Integrable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        (actualTrackerAtBoundary P I t z) ^ p)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))) ∧
    lam ^ p *
      (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
        (actualTrackerAtBoundary P I t z) ^ p
        ∂((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw I.oracle (responseCount P)))) ≤
      4 * (lam ^ p * σ ^ p +
        lam ^ p *
          (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ +
            (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h)) ^ p +
        5 * K) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle (responseCount P)) :=
    freshSeedLaw_probability I.oracle (responseCount P)
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  let b := 2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
  have hC : 0 ≤ C :=
    add_nonneg (mul_nonneg hbeta (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩).le)
      (mul_nonneg I.Lbar_pos.le hh)
  have hover : 0 ≤ b + C := by
    dsimp [b]
    have hb : 0 ≤ 2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ :=
      mul_nonneg (by norm_num) (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩).le
    exact add_nonneg hb hC
  have hInit := actualTrackerAtBoundary_initial_p_integrable_bound P I
  have hExpInt := actualTrackerShiftedWeight_integrable P I
    b lam hlam.le hbeta hh t ht
  have hExpBound := actualTracker_shiftedWeight_uniform P I
    hbeta hbeta_le hh hscale hmove lam K hlam.le hKbase hKstep t ht
  exact tracker_p_moment_from_shifted_exp μ
    (actualTrackerAtBoundary P I 0)
    (actualTrackerAtBoundary P I t)
    (measurable_actualTrackerAtBoundary P I 0)
    (measurable_actualTrackerAtBoundary P I t)
    p (b + C) lam (σ ^ p) K
    I.p_range.1.le I.p_range.2 hover hlam
    (actualTrackerAtBoundary_nonneg P I 0)
    (actualTrackerAtBoundary_nonneg P I t)
    hInit.1 hInit.2 hExpInt hExpBound

end

end HeavyTailedNoise.UpperK1
