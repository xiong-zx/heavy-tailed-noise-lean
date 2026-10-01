import HeavyTailedNoise.Upper.K1.CoarseTrackerLyapunovConstants

/-!
Concrete, dimension-free tail and `p`-moment bounds for the exact adaptive
coarse tracker.  The remaining premises in this internal interface are
literal coefficient checks of the physical paper schedule, not oracle
assumptions.  In particular `σ=0` remains allowed.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualTracker_uniform_p_moment_concrete
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hbeta : 0 < P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hscale : 12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8)
    (t : ℕ) (ht : t ≤ P.T) :
    let δ := (1 / 8 : ℝ) *
      (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
    let lam := δ / C ^ 2
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
        lam ^ p * (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + C) ^ p +
        815) := by
  dsimp only
  let δ := (1 / 8 : ℝ) *
    (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
  let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
  let lam := δ / C ^ 2
  have hchoice := tracker_schedule_scalar_choice P I hbeta hh hmove
  have hlam : 0 < lam := hchoice.1
  have hK := hchoice.2
  have hmain := actualTracker_uniform_p_moment P I
    hbeta.le hbeta_le hh hscale hmove lam 163 hlam
    (by norm_num) hK t ht
  have hnum : (5 : ℝ) * 163 = 815 := by norm_num
  simpa only [C, lam, δ, hnum] using hmain

theorem actualTracker_shifted_tail_concrete
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hbeta : 0 < P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hscale : 12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8)
    (t : ℕ) (ht : t ≤ P.T) (x : ℝ) :
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
  dsimp only
  let δ := (1 / 8 : ℝ) *
    (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
  let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
  let lam := δ / C ^ 2
  have hchoice := tracker_schedule_scalar_choice P I hbeta hh hmove
  have htail := actualTracker_shifted_tail P I
    hbeta.le hbeta_le hh hscale hmove lam 163
    hchoice.1.le (by norm_num) hchoice.2 t ht x
  simpa only [C, lam, δ, mul_comm] using htail

end

end HeavyTailedNoise.UpperK1
