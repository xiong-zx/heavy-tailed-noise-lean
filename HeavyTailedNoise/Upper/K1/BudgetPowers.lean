import HeavyTailedNoise.Upper.K1.CutoffBounds
import HeavyTailedNoise.Upper.K1.RateArithmetic

/-!
Power conversion for the literal least-dyadic cutoff. The bounds here keep
`J = 0` and the critical equality curve; no asymptotic notation is used.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem paperU_le_scaled (p σ ε Ctail : ℝ)
    (hp : 1 < p) (hε : 0 < ε) (hCtail : 12 ≤ Ctail) :
    paperU p σ ε Ctail ≤
      (2 * Ctail) * (paperS σ ε) ^ (1 / (p - 1)) := by
  have h := (paperU_lt_two_target (σ := σ) (ε := ε) hp hε hCtail).le
  simpa only [paperTailTarget, mul_assoc] using h

/-- A nonnegative power of the actual cutoff is bounded by the power of its
factor-two least-dyadic envelope, with a separately visible constant. -/
theorem paperCutoff_power_envelope (p σ ε Ctail a : ℝ)
    (hp : 1 < p) (hε : 0 < ε) (hCtail : 12 ≤ Ctail)
    (ha : 0 ≤ a) :
    (paperS σ ε) ^ 2 * (paperU p σ ε Ctail) ^ a ≤
      (2 * Ctail) ^ a *
        (paperS σ ε) ^ (2 + a / (p - 1)) := by
  let S := paperS σ ε
  let U := paperU p σ ε Ctail
  let t : ℝ := 1 / (p - 1)
  have hS : 0 < S := paperS_pos σ ε
  have hU : 0 ≤ U := (paperU_pos (p := p) (σ := σ) (Ctail := Ctail) hε).le
  have hC : 0 ≤ 2 * Ctail := by linarith
  have hSt : 0 ≤ S ^ t := Real.rpow_nonneg hS.le _
  have hpow : U ^ a ≤ ((2 * Ctail) * S ^ t) ^ a :=
    Real.rpow_le_rpow hU (paperU_le_scaled p σ ε Ctail hp hε hCtail) ha
  have hpowid : S ^ 2 * (S ^ t) ^ a = S ^ (2 + t * a) := by
    calc
      S ^ 2 * (S ^ t) ^ a = S ^ (2 : ℝ) * S ^ (t * a) := by
        rw [Real.rpow_mul hS.le t a]
        exact congrArg (fun v : ℝ => v * (S ^ t) ^ a)
          (Real.rpow_natCast S 2).symm
      _ = S ^ (2 + t * a) := (Real.rpow_add hS 2 (t * a)).symm
  calc
    S ^ 2 * U ^ a ≤ S ^ 2 * ((2 * Ctail) * S ^ t) ^ a :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg S)
    _ = S ^ 2 * (2 * Ctail) ^ a * (S ^ t) ^ a := by
      rw [Real.mul_rpow hC hSt]
      ring
    _ = (2 * Ctail) ^ a * S ^ (2 + t * a) := by
      calc
        S ^ 2 * (2 * Ctail) ^ a * (S ^ t) ^ a =
            (2 * Ctail) ^ a * (S ^ 2 * (S ^ t) ^ a) := by ac_rfl
        _ = (2 * Ctail) ^ a * S ^ (2 + t * a) := by rw [hpowid]
    _ = (2 * Ctail) ^ a * S ^ (2 + a / (p - 1)) := by
      have he : t * a = a / (p - 1) := by
        dsimp [t]
        ring
      rw [he]

/-- The rounded initialization scale is controlled by the `S^r` term. -/
theorem paper_initial_power_le_rate (p σ ε Ctail : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hε : 0 < ε) (hCtail : 12 ≤ Ctail) :
    (paperS σ ε) ^ 2 *
        (paperU p σ ε Ctail) ^ (paperA p) ≤
      (2 * Ctail) ^ (paperA p) *
        (paperS σ ε) ^ (p / (p - 1)) := by
  have ha : 0 ≤ paperA p := by
    unfold paperA
    linarith
  have h := paperCutoff_power_envelope p σ ε Ctail (paperA p)
    hp hε hCtail ha
  rw [show (2 : ℝ) + paperA p / (p - 1) = p / (p - 1) by
    simpa only [paperA] using initial_exponent_identity hp] at h
  exact h

/-- The runtime scale is controlled by the exact max of the two manuscript
exponents, including `q = r/2`. -/
theorem paper_runtime_power_le_rate (p q σ ε Ctail : ℝ)
    (hp : 1 < p) (hq : 0 < q) (hε : 0 < ε) (hCtail : 12 ≤ Ctail) :
    (paperS σ ε) ^ 2 *
        (paperU p σ ε Ctail) ^ (paperEplus p q) ≤
      (2 * Ctail) ^ (paperEplus p q) *
        (paperS σ ε) ^
          (max 2 ((p / (p - 1)) / q)) := by
  have h := paperCutoff_power_envelope p σ ε Ctail (paperEplus p q)
    hp hε hCtail (paperEplus_nonneg p q)
  rw [runtime_max_exponent_identity hp hq] at h
  exact h

end

end HeavyTailedNoise.UpperK1
