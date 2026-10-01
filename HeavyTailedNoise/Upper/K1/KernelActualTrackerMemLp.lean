import HeavyTailedNoise.Upper.K1.CoarseTrackerUniformMoment

/-!
The canonical actual-boundary tracker error inherits `MemLp p` from the
already proved uniform `p`-moment estimate.  This is a thin interface for
outer-history source-drift estimates; it defines no new tracker process.
The supplied exponential parameters are exactly the existing intermediate
premises of `actualTracker_uniform_p_moment`.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped NNReal

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualTrackerAtBoundary_memLp_of_p_integrable
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (t : ℕ)
    (hInt : Integrable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        (actualTrackerAtBoundary P I t z) ^ p)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P)))) :
    MemLp (actualTrackerAtBoundary P I t) (ENNReal.ofReal p)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))) := by
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  have hp : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hnormFun :
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        ‖actualTrackerAtBoundary P I t z‖ ^ p) =
      (fun z => (actualTrackerAtBoundary P I t z) ^ p) := by
    funext z
    rw [Real.norm_eq_abs,
      abs_of_nonneg (actualTrackerAtBoundary_nonneg P I t z)]
  have hNormInt : Integrable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        ‖actualTrackerAtBoundary P I t z‖ ^ p) μ := by
    rw [hnormFun]
    exact hInt
  apply (integrable_norm_rpow_iff
    (measurable_actualTrackerAtBoundary P I t).aestronglyMeasurable
    (p := ENNReal.ofReal p)
    (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hp.le] using hNormInt

theorem actualTrackerAtBoundary_memLp_of_uniform
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hbeta : 0 ≤ P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hscale : 12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8)
    (lam K : ℝ) (hlam : 0 < lam) (hKbase : 1 ≤ K)
    (hKstep :
      Real.exp
        (((((‖(P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h) -
                -(P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h)‖₊ /
              2) ^ 2 : ℝ≥0) : ℝ) * lam ^ 2 / 2) -
          lam * ((1 / 8 : ℝ) *
            (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩))) * K + 1 ≤ K)
    (t : ℕ) (ht : t ≤ P.T) :
    MemLp (actualTrackerAtBoundary P I t) (ENNReal.ofReal p)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))) := by
  exact actualTrackerAtBoundary_memLp_of_p_integrable P I t
    (actualTracker_uniform_p_moment P I hbeta hbeta_le hh
      hscale hmove lam K hlam hKbase hKstep t ht).1

end

end HeavyTailedNoise.UpperK1
