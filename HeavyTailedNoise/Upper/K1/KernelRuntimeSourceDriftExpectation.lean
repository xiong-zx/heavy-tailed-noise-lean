import HeavyTailedNoise.Upper.K1.KernelRuntimeSourceDriftPointwise
import HeavyTailedNoise.Upper.K1.KernelPhysicalOuterScaleIntegrable
import HeavyTailedNoise.Upper.K1.KernelDriftIntegralBridge
import HeavyTailedNoise.Upper.K1.KernelPhysicalActualOuterScale
import HeavyTailedNoise.Upper.K1.CoarseTrackerPaperScheduleGates

/-!
The same-path high-band source drift has a finite outer nonnegative
integral.  Pathwise geometry, tracker-scale integrability, and the generic
integral comparison live in separate small lemmas.  This wrapper only
instantiates them under the literal paper schedule and full seed law.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem paperSchedule_actualBatch_highBand_sourceMean_drift_lintegral_le
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    let μ := (algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw I.oracle (responseCount P))
    ∀ u : Fin P.T,
      let s := paperSexp p q
      let ν := paperNu σ ε
      let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
      let K : ℝ := 2 * C / ν ^ s
      let B : ℝ := Lbar * P.h +
        P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
      (∫⁻ z, ENNReal.ofReal
        (actualHighBandSourceDrift P I.oracle s u z) ∂μ) ≤
        ENNReal.ofReal
          (K * B *
            (2 * σ +
              lpNorm (actualTrackerAtBoundary P I u.val)
                (ENNReal.ofReal p) μ +
              lpNorm (actualTrackerAtBoundary P I (u.val + 1))
                (ENNReal.ofReal p) μ) ^ s) := by
  dsimp only
  intro u
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  let s := paperSexp p q
  let ν := paperNu σ ε
  let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
  let K : ℝ := 2 * C / ν ^ s
  let B : ℝ := Lbar * P.h +
    P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  let scale : Fin P.T × (Fin (responseCount P) → Seed) → ℝ :=
    actualTrackerPairScale P I u
  let major : Fin P.T × (Fin (responseCount P) → Seed) → ℝ :=
    fun z => K * B * (scale z) ^ s
  let bound : ℝ := K * B *
    (2 * σ +
      lpNorm (actualTrackerAtBoundary P I u.val)
        (ENNReal.ofReal p) μ +
      lpNorm (actualTrackerAtBoundary P I (u.val + 1))
        (ENNReal.ofReal p) μ) ^ s
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos (lt_trans zero_lt_one hp)
    apply sub_pos.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa using hq)
  have hν : 0 < ν := paperNu_pos (σ := σ) hε
  have htwo : 1 < (2 : ℝ) ^ s :=
    Real.one_lt_rpow (by norm_num) hs
  have hC : 0 ≤ C := by
    dsimp [C]
    exact (div_pos (Real.rpow_pos_of_pos (by norm_num) s)
      (sub_pos.mpr htwo)).le
  have hK : 0 ≤ K := by dsimp [K]; positivity
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
  have hscale0 (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      0 ≤ scale z := by
    change 0 ≤ actualTrackerPairScale P I u z
    rw [actualTrackerPairScale]
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) I.sigma_nonneg)
        (actualTrackerAtBoundary_nonneg P I u.val z))
      (actualTrackerAtBoundary_nonneg P I (u.val + 1) z)
  have hscaleInt : Integrable (fun z => (scale z) ^ s) μ := by
    simpa only [scale, μ, s] using
      (paperSchedule_actualTrackerPairScale_rpow_integrable
        p q Δ σ Lbar ε Ctail κ Cb CI hq hε hCb hCI I u)
  have hmajorInt : Integrable major μ := by
    change Integrable (fun z => (K * B) * (scale z) ^ s) μ
    exact hscaleInt.const_mul (K * B)
  have hmajorNonneg : 0 ≤ᵐ[μ] major :=
    Filter.Eventually.of_forall fun z => by
      change 0 ≤ K * B * (scale z) ^ s
      exact mul_nonneg (mul_nonneg hK hB)
        (Real.rpow_nonneg (hscale0 z) _)
  have hpoint (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      actualHighBandSourceDrift P I.oracle s u z ≤ major z := by
    change actualHighBandSourceDrift P I.oracle s u z ≤
      K * B * (actualTrackerPairScale P I u z) ^ s
    exact (paperSchedule_actualHighBandSourceDrift_pointwise
      p q Δ σ Lbar ε Ctail κ Cb CI
      hp hq hε hCb hCI I) u z
  have houter : (∫ z, (scale z) ^ s ∂μ) ≤
      (2 * σ +
        lpNorm (actualTrackerAtBoundary P I u.val)
          (ENNReal.ofReal p) μ +
        lpNorm (actualTrackerAtBoundary P I (u.val + 1))
          (ENNReal.ofReal p) μ) ^ s := by
    simpa only [scale, μ, s, actualTrackerPairScale] using
      (paperSchedule_actualTracker_outer_scale_le
        p q Δ σ Lbar ε Ctail κ Cb CI hq hε hCb hCI I u)
  have hmajorBound : (∫ z, major z ∂μ) ≤ bound := by
    change (∫ z, (K * B) * (scale z) ^ s ∂μ) ≤ _
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left houter (mul_nonneg hK hB)
  exact lintegral_ofReal_le_of_integrable_majorant μ
    (actualHighBandSourceDrift P I.oracle s u) major bound
    hmajorInt hmajorNonneg hpoint hmajorBound

end

end HeavyTailedNoise.UpperK1
