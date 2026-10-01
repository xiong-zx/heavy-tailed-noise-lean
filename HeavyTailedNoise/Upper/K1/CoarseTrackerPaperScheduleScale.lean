import HeavyTailedNoise.Upper.Foundations.CoarseTrackerMomentPhysicalScale
import HeavyTailedNoise.Upper.K1.CoarseTrackerPaperScheduleMoment
import HeavyTailedNoise.Upper.K1.CoarseTrackerLyapunovConstants

/-!
The manuscript-scale uniform tracker moment for the literal shared-batch
algorithm with the legal fixed choice `c_h = 1/8`.  The constant depends on
`p` only and is independent of dimension, horizon, `σ`, and other physical
parameters.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem Admissible.paperSchedule_eighth_tracker_p_moment_le_nu
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
    Integrable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        (actualTrackerAtBoundary P I t z) ^ p)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))) ∧
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      (actualTrackerAtBoundary P I t z) ^ p
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P)))) ≤
      4 * (1 + (36 : ℝ) ^ p +
        815 * (243 / 8 : ℝ) ^ p) * ν ^ p := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  let τ := P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  let δ := (1 / 8 : ℝ) * (P.beta * τ)
  let C := P.beta * τ + Lbar * P.h
  let lam := δ / C ^ 2
  let ν := paperNu σ ε
  let a := 2 * τ + C
  have hgate := paperSchedule_eighth_tracker_gates
    p q Δ σ Lbar ε Ctail κ Cb CI hε I.Lbar_pos hCb hCI
  change 0 < P.beta ∧ P.beta ≤ 1 / 4 ∧ 0 ≤ P.h ∧
    12 * σ ≤ τ ∧ Lbar * P.h ≤ P.beta * τ / 8 at hgate
  obtain ⟨hbeta, hbeta_le, hh, _hscale, hmove⟩ := hgate
  have hscale := tracker_schedule_exponent_overshoot_scale
    P I hbeta hbeta_le hh hmove
  have hInv : lam⁻¹ ≤ (81 / 32 : ℝ) * τ := hscale.1
  have haτ : a ≤ 3 * τ := hscale.2
  have hτ : τ = 12 * ν := by
    change paperTau σ ε 0 = 12 * paperNu σ ε
    simp [paperTau]
  have hν : 0 ≤ ν := (paperNu_pos hε).le
  have ha : 0 ≤ a := by
    have hτpos := P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩
    have hC : 0 ≤ C :=
      add_nonneg (mul_nonneg hbeta.le hτpos.le)
        (mul_nonneg I.Lbar_pos.le hh)
    dsimp [a]
    linarith
  have hmain := Admissible.paperSchedule_eighth_tracker_uniform_p_moment
    I ε Ctail κ Cb CI hε hCb hCI t ht
  have hbound :
      lam ^ p *
        (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          (actualTrackerAtBoundary P I t z) ^ p
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw I.oracle (responseCount P)))) ≤
      4 * (lam ^ p * σ ^ p + lam ^ p * a ^ p + 815) := hmain.2
  have hlam : 0 < lam := by
    have hchoice := tracker_schedule_scalar_choice P I hbeta hh hmove
    exact hchoice.1
  refine ⟨hmain.1, ?_⟩
  exact tracker_p_moment_le_nu_rpow
    (lt_trans zero_lt_one I.p_range.1)
    I.sigma_nonneg hν ha hlam (le_max_left σ ε)
    hτ haτ hInv hbound

end

end HeavyTailedNoise.UpperK1
