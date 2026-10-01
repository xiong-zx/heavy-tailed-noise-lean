import HeavyTailedNoise.Upper.K1.MeanDriftPhysical
import HeavyTailedNoise.Upper.K1.CoarseTrackerPhysicalCoefficients

/-!
The physical same-source mean drift is at most a constant depending only on
`p,q` times the target accuracy.  The fixed `c_h=1/8` and the actual ceiling
in `β` are used; neither dimension nor the number of dyadic bands enters.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

/-- A loose explicit dimension-free constant suffices for EMA drift. -/
def paperMeanDriftConstant (p q : ℝ) : ℝ :=
  let s := paperSexp p q
  let Cp : ℝ := 4 * (1 + (36 : ℝ) ^ p +
    815 * (243 / 8 : ℝ) ^ p)
  let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
  (2 * C) * (25 / 8) * (2 + 2 * Cp) ^ s

theorem paperSchedule_actualBatch_highBand_sourceMean_drift_epsilon_le
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
      (∫⁻ z, ENNReal.ofReal
        (actualHighBandSourceDrift P I.oracle (paperSexp p q) u z) ∂μ) ≤
        ENNReal.ofReal (paperMeanDriftConstant p q * ε) := by
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
  let D : ℝ := paperMeanDriftConstant p q
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos hp0
    apply sub_pos.mpr
    exact (div_lt_iff₀ hq0).2 (by simpa using hq)
  have hν : 0 < ν := paperNu_pos (σ := σ) hε
  have hνs : 0 < ν ^ s := Real.rpow_pos_of_pos hν _
  have htwo : 1 < (2 : ℝ) ^ s :=
    Real.one_lt_rpow (by norm_num) hs
  have hC : 0 ≤ C := by
    dsimp [C]
    exact (div_pos (Real.rpow_pos_of_pos (by norm_num) s)
      (sub_pos.mpr htwo)).le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCp : 1 ≤ Cp := by
    dsimp [Cp]
    have h36 : 0 ≤ (36 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
    have h243 : 0 ≤ (243 / 8 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
    nlinarith
  have hCp0 : 0 ≤ Cp := le_trans (by norm_num) hCp
  have hR : R ≤ Cp * ν := by
    have hCpPow : Cp ^ p⁻¹ ≤ Cp :=
      Real.rpow_le_self_of_one_le hCp ((inv_le_one₀ hp0).2 hp.le)
    have hνPow : (ν ^ p) ^ p⁻¹ = ν := by
      rw [← Real.rpow_mul hν.le,
        mul_inv_cancel₀ hp0.ne', Real.rpow_one]
    calc
      R = Cp ^ p⁻¹ * (ν ^ p) ^ p⁻¹ := by
        dsimp [R]
        rw [Real.mul_rpow hCp0 (Real.rpow_nonneg hν.le _)]
      _ = Cp ^ p⁻¹ * ν := by rw [hνPow]
      _ ≤ Cp * ν := mul_le_mul_of_nonneg_right hCpPow hν.le
  have hS := paperS_pos σ ε
  let k : ℝ := Nat.ceil (paperS σ ε)
  have hk : 0 < k := by
    have hk1 := (one_le_paperS σ ε).trans (paperS_le_ceil σ ε)
    dsimp [k]
    linarith
  have hνceil : ν ≤ ε * k := by
    have hνEq : ν = ε * paperS σ ε := paperNu_eq_eps_mul_paperS hε
    rw [hνEq]
    exact mul_le_mul_of_nonneg_left (paperS_le_ceil σ ε) hε.le
  have hβτ : P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ≤
      3 * ε := by
    have hformula : P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ =
        3 * ν / k := by
      dsimp [P, paperSchedule, paperBeta, paperTau, k, ν]
      simp only [pow_zero, mul_one]
      field_simp [ne_of_gt hk]
      ring
    rw [hformula]
    apply (div_le_iff₀ hk).2
    nlinarith [hνceil]
  have hstep : Lbar * P.h = ε / 8 := by
    change Lbar * paperStep (1 / 8) ε Lbar = ε / 8
    exact Lbar_mul_paperStep_eighth I.Lbar_pos
  have hB : B ≤ (25 / 8 : ℝ) * ε := by
    change Lbar * P.h +
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ≤
        (25 / 8 : ℝ) * ε
    rw [hstep]
    linarith [hβτ]
  have hscaledBase : 2 * σ + 2 * R ≤ (2 + 2 * Cp) * ν := by
    have hσ : σ ≤ ν := le_max_left σ ε
    nlinarith [hR]
  have hscaledBase0 : 0 ≤ 2 * σ + 2 * R := by
    have hR0 : 0 ≤ R := Real.rpow_nonneg (mul_nonneg hCp0
      (Real.rpow_nonneg hν.le _)) _
    nlinarith [I.sigma_nonneg]
  have hpow : (2 * σ + 2 * R) ^ s ≤
      ((2 + 2 * Cp) * ν) ^ s :=
    Real.rpow_le_rpow hscaledBase0 hscaledBase hs.le
  have hKcancel : K * ν ^ s = 2 * C := by
    dsimp [K]
    field_simp [ne_of_gt hνs]
  have hfactor : 0 ≤ (2 * C) * (2 + 2 * Cp) ^ s := by
    positivity
  have hreal : K * B * (2 * σ + 2 * R) ^ s ≤ D * ε := by
    calc
      K * B * (2 * σ + 2 * R) ^ s ≤
          K * B * ((2 + 2 * Cp) * ν) ^ s := by
            exact mul_le_mul_of_nonneg_left hpow
              (mul_nonneg hK (by
                have hB0 : 0 ≤ B := by
                  have hgate := paperSchedule_eighth_tracker_gates
                    p q Δ σ Lbar ε Ctail κ Cb CI hε
                    I.Lbar_pos hCb hCI
                  change 0 < P.beta ∧ P.beta ≤ 1 / 4 ∧ 0 ≤ P.h ∧
                    12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ∧
                    Lbar * P.h ≤ P.beta *
                      P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8 at hgate
                  exact add_nonneg
                    (mul_nonneg I.Lbar_pos.le hgate.2.2.1)
                    (mul_nonneg hgate.1.le
                      (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩).le)
                exact hB0))
      _ = ((2 * C) * (2 + 2 * Cp) ^ s) * B := by
            rw [Real.mul_rpow (by nlinarith [hCp]) hν.le]
            calc
              K * B * ((2 + 2 * Cp) ^ s * ν ^ s) =
                  (K * ν ^ s) * (2 + 2 * Cp) ^ s * B := by ring
              _ = ((2 * C) * (2 + 2 * Cp) ^ s) * B := by
                    rw [hKcancel]
      _ ≤ ((2 * C) * (2 + 2 * Cp) ^ s) *
          ((25 / 8 : ℝ) * ε) :=
            mul_le_mul_of_nonneg_left hB hfactor
      _ = D * ε := by
            dsimp [D, paperMeanDriftConstant, s, Cp, C]
            ring
  have hbase := paperSchedule_actualBatch_highBand_sourceMean_drift_physical_le
    p q Δ σ Lbar ε Ctail κ Cb CI hp hq hε hCb hCI I u
  exact hbase.trans (ENNReal.ofReal_le_ofReal hreal)

end

end HeavyTailedNoise.UpperK1
