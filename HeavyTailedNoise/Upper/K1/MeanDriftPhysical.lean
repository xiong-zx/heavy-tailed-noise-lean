import HeavyTailedNoise.Upper.K1.MeanDriftMoment
import HeavyTailedNoise.Upper.K1.KernelRuntimeSourceDriftExpectation

/-!
The expected same-source high-band mean drift along one actual completed
batch, with both endpoint `Lp` norms removed using the true tracker's
dimension-free physical moment bound.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem paperSchedule_actualBatch_highBand_sourceMean_drift_physical_le
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    let μ := (algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw I.oracle (responseCount P))
    let s := paperSexp p q
    let ν := paperNu σ ε
    let Cp : ℝ := 4 * (1 + (36 : ℝ) ^ p +
      815 * (243 / 8 : ℝ) ^ p)
    let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
    let K : ℝ := 2 * C / ν ^ s
    let B : ℝ := Lbar * P.h +
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
    ∀ u : Fin P.T,
      (∫⁻ z, ENNReal.ofReal
        (actualHighBandSourceDrift P I.oracle s u z) ∂μ) ≤
        ENNReal.ofReal
          (K * B * (2 * σ + 2 * (Cp * ν ^ p) ^ p⁻¹) ^ s) := by
  dsimp only
  intro u
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  let s := paperSexp p q
  let ν := paperNu σ ε
  let Cp : ℝ := 4 * (1 + (36 : ℝ) ^ p +
    815 * (243 / 8 : ℝ) ^ p)
  let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
  let K : ℝ := 2 * C / ν ^ s
  let B : ℝ := Lbar * P.h +
    P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  let R : ℝ := (Cp * ν ^ p) ^ p⁻¹
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos (lt_trans zero_lt_one hp)
    apply sub_pos.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa using hq)
  have hν : 0 < ν := paperNu_pos (σ := σ) hε
  have htwo : 1 < (2 : ℝ) ^ s :=
    Real.one_lt_rpow (by norm_num) hs
  have hK : 0 ≤ K := by
    dsimp [K, C]
    positivity
  have hgate := paperSchedule_eighth_tracker_gates
    p q Δ σ Lbar ε Ctail κ Cb CI hε I.Lbar_pos hCb hCI
  change 0 < P.beta ∧ P.beta ≤ 1 / 4 ∧ 0 ≤ P.h ∧
    12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ∧
    Lbar * P.h ≤ P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8 at hgate
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg
      (mul_nonneg I.Lbar_pos.le hgate.2.2.1)
      (mul_nonneg hgate.1.le
        (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩).le)
  have hpre : lpNorm (actualTrackerAtBoundary P I u.val)
      (ENNReal.ofReal p) μ ≤ R := by
    simpa only [P, μ, R, Cp, ν] using
      (Admissible.paperSchedule_actualTracker_lpNorm_le_root
        I ε Ctail κ Cb CI hε hCb hCI u.val
        (Nat.le_of_lt u.isLt))
  have hpost : lpNorm (actualTrackerAtBoundary P I (u.val + 1))
      (ENNReal.ofReal p) μ ≤ R := by
    simpa only [P, μ, R, Cp, ν] using
      (Admissible.paperSchedule_actualTracker_lpNorm_le_root
        I ε Ctail κ Cb CI hε hCb hCI (u.val + 1)
        (Nat.succ_le_iff.mpr u.isLt))
  have hleft0 : 0 ≤ 2 * σ +
      lpNorm (actualTrackerAtBoundary P I u.val)
        (ENNReal.ofReal p) μ +
      lpNorm (actualTrackerAtBoundary P I (u.val + 1))
        (ENNReal.ofReal p) μ := by
    have hσ : 0 ≤ 2 * σ := mul_nonneg (by norm_num) I.sigma_nonneg
    exact add_nonneg (add_nonneg hσ lpNorm_nonneg) lpNorm_nonneg
  have hpow :
      (2 * σ +
        lpNorm (actualTrackerAtBoundary P I u.val)
          (ENNReal.ofReal p) μ +
        lpNorm (actualTrackerAtBoundary P I (u.val + 1))
          (ENNReal.ofReal p) μ) ^ s ≤
      (2 * σ + 2 * R) ^ s := by
    apply Real.rpow_le_rpow hleft0 _ hs.le
    linarith
  have hreal : K * B *
      (2 * σ +
        lpNorm (actualTrackerAtBoundary P I u.val)
          (ENNReal.ofReal p) μ +
        lpNorm (actualTrackerAtBoundary P I (u.val + 1))
          (ENNReal.ofReal p) μ) ^ s ≤
      K * B * (2 * σ + 2 * R) ^ s :=
    mul_le_mul_of_nonneg_left hpow (mul_nonneg hK hB)
  have hbase := paperSchedule_actualBatch_highBand_sourceMean_drift_lintegral_le
    p q Δ σ Lbar ε Ctail κ Cb CI hp hq hε hCb hCI I u
  exact hbase.trans (ENNReal.ofReal_le_ofReal hreal)

end

end HeavyTailedNoise.UpperK1
