import HeavyTailedNoise.Lower.Randomized.ScaledInstance
import HeavyTailedNoise.Lower.Fradin.NoiseInstance

/-!
One public choice of all physical scales. The true lift uses R=1000√T,
η=1/5 and increment budget 7000. No numerical condition remains in the
resulting admissible instance except positivity of its chosen chain length.
-/

namespace HeavyTailedNoise.RandomizedLift

open HeavyTailedNoise.Fradin MeasureTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false

def physicalChainConstant : ℝ := 12 * 64 * 7000

def physicalAmplitude (ε : ℝ) : ℝ := 8 * ε

def physicalTheta (σ ε p : ℝ) (hp : 1 < p) : unitInterval :=
  revealParameter 368 (σ / ε) (tailExponent p) (by norm_num) (tailExponent_pos hp)

def physicalLambda (L ε θ q : ℝ) : ℝ :=
  7000 * physicalAmplitude ε / (L * θ ^ ((q - 1) / q))

def physicalChainArgument (L Δ ε θ q : ℝ) : ℝ :=
  (L * Δ / ε ^ 2) * θ ^ ((q - 1) / q) / physicalChainConstant

def physicalChainLength (L Δ ε θ q : ℝ) : ℕ :=
  ⌊physicalChainArgument L Δ ε θ q⌋₊

theorem physicalChainConstant_pos : 0 < physicalChainConstant := by
  norm_num [physicalChainConstant]

def physicalAccuracyConstant : ℝ := 1 / Real.sqrt (2 * physicalChainConstant)

theorem physicalAccuracyConstant_pos : 0 < physicalAccuracyConstant := by
  unfold physicalAccuracyConstant
  exact one_div_pos.mpr (Real.sqrt_pos.mpr
    (mul_pos (by norm_num : (0 : ℝ) < 2) physicalChainConstant_pos))

theorem physical_accuracy_of_absolute_epsilon_bound {L Δ ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hbound : ε ≤ physicalAccuracyConstant * Real.sqrt (L * Δ)) :
    2 * physicalChainConstant ≤ L * Δ / ε ^ 2 := by
  have h2C : 0 < 2 * physicalChainConstant :=
    mul_pos (by norm_num : (0 : ℝ) < 2) physicalChainConstant_pos
  have hsqrtC : 0 < Real.sqrt (2 * physicalChainConstant) :=
    Real.sqrt_pos.mpr h2C
  have hbound' : ε ≤ Real.sqrt (L * Δ) / Real.sqrt (2 * physicalChainConstant) := by
    simpa only [physicalAccuracyConstant, div_eq_mul_inv, one_mul, mul_comm] using hbound
  have hm := (le_div_iff₀ hsqrtC).mp hbound'
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ ε * Real.sqrt (2 * physicalChainConstant)) hm 2
  rw [mul_pow, Real.sq_sqrt h2C.le,
    Real.sq_sqrt (mul_pos hL hΔ).le] at hsquare
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  nlinarith

theorem physicalTheta_pos {σ ε p : ℝ} (hp : 1 < p) :
    0 < (physicalTheta σ ε p hp : ℝ) := revealRate_pos (by norm_num)

@[simp] theorem physicalTheta_zero_noise (ε p : ℝ) (hp : 1 < p) :
    (physicalTheta 0 ε p hp : ℝ) = 1 := by
  simp [physicalTheta, revealParameter, revealRate]

theorem physicalAmplitude_pos {ε : ℝ} (hε : 0 < ε) : 0 < physicalAmplitude ε := by
  unfold physicalAmplitude
  positivity

theorem physicalLambda_pos {L ε θ q : ℝ} (hL : 0 < L) (hε : 0 < ε) (hθ : 0 < θ) :
    0 < physicalLambda L ε θ q := by
  unfold physicalLambda
  exact div_pos (mul_pos (by norm_num) (physicalAmplitude_pos hε))
    (mul_pos hL (Real.rpow_pos_of_pos hθ _))

theorem physicalChainArgument_nonneg {L Δ ε θ q : ℝ}
    (hL : 0 < L) (hΔ : 0 ≤ Δ) (hθ : 0 < θ) :
    0 ≤ physicalChainArgument L Δ ε θ q := by
  unfold physicalChainArgument
  exact div_nonneg
    (mul_nonneg (div_nonneg (mul_nonneg hL.le hΔ) (sq_nonneg ε))
      (Real.rpow_nonneg hθ.le _)) physicalChainConstant_pos.le

/-- The reference precision 46ε gives the actual centered amplitude 184ε. -/
theorem revealParameter_lift_amplitude {ε σ p : ℝ} (hε : 0 < ε) (hp : 1 < p) :
    revealParameter 8 (σ / (46 * ε)) (tailExponent p)
      (by norm_num) (tailExponent_pos hp) = physicalTheta σ ε p hp := by
  apply Subtype.ext
  change revealRate 8 (σ / (46 * ε)) (tailExponent p) =
    revealRate 368 (σ / ε) (tailExponent p)
  have hguard : σ / (46 * ε) ≤ 8 ↔ σ / ε ≤ 368 := by
    rw [div_le_iff₀ (by positivity : 0 < 46 * ε), div_le_iff₀ hε]
    constructor <;> intro h <;> nlinarith
  unfold revealRate
  by_cases hs : σ / ε ≤ 368
  · rw [if_pos hs, if_pos (hguard.mpr hs)]
  · rw [if_neg hs, if_neg ((not_congr hguard).mpr hs)]
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring

theorem physical_moment_budget {p ε σ : ℝ} (hp : 1 < p)
    (hε : 0 < ε) (hσ : 0 ≤ σ) :
    let θ := physicalTheta σ ε p hp
    (physicalAmplitude ε) ^ p *
      (2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) ≤ σ ^ p := by
  let θ := physicalTheta σ ε p hp
  have hnoise := noise_moment_condition_revealParameter (c := 8)
    (ε := 46 * ε) (σ := σ) (p := p) (by norm_num) (by positivity) hσ hp
  dsimp only at hnoise
  rw [revealParameter_lift_amplitude hε hp] at hnoise
  have hproduct : (physicalAmplitude ε) ^ p * (23 : ℝ) ^ p = (4 * (46 * ε)) ^ p := by
    rw [← Real.mul_rpow (physicalAmplitude_pos hε).le (by norm_num)]
    congr 1
    unfold physicalAmplitude
    ring
  change (physicalAmplitude ε) ^ p *
    (2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) ≤ σ ^ p
  calc
    _ = 2 * ((physicalAmplitude ε) ^ p * (23 : ℝ) ^ p) *
        (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) := by ring
    _ = 2 * (4 * (46 * ε)) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) := by rw [hproduct]
    _ ≤ σ ^ p := hnoise

theorem physical_increment_budget_eq {L ε θ q : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hθ : 0 < θ) (hq : 1 ≤ q) :
    (physicalAmplitude ε) ^ q * (7000 : ℝ) ^ q *
      ((physicalLambda L ε θ q)⁻¹) ^ q / θ ^ (q - 1) = L ^ q := by
  have hlam := physicalLambda_pos (q := q) hL hε hθ
  have hq0 : 0 < q := by linarith
  have hscale : physicalAmplitude ε * 7000 * (physicalLambda L ε θ q)⁻¹ =
      L * θ ^ ((q - 1) / q) := by
    unfold physicalLambda physicalAmplitude
    field_simp [hL.ne', hε.ne', (Real.rpow_pos_of_pos hθ ((q - 1) / q)).ne'] <;> ring
  have hpower : (θ ^ ((q - 1) / q)) ^ q = θ ^ (q - 1) := by
    rw [← Real.rpow_mul hθ.le]
    congr 1
    exact div_mul_cancel₀ _ hq0.ne'
  calc
    _ = (physicalAmplitude ε * 7000 * (physicalLambda L ε θ q)⁻¹) ^ q / θ ^ (q - 1) := by
      rw [Real.mul_rpow (mul_nonneg (physicalAmplitude_pos hε).le (by norm_num))
        (inv_nonneg.mpr hlam.le), Real.mul_rpow (physicalAmplitude_pos hε).le (by norm_num)]
    _ = (L * θ ^ ((q - 1) / q)) ^ q / θ ^ (q - 1) := by rw [hscale]
    _ = L ^ q := by
      rw [Real.mul_rpow hL.le (Real.rpow_nonneg hθ.le _), hpower,
        mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hθ (q - 1)).ne']

theorem physical_gap_budget {L Δ ε θ q : ℝ}
    (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hθ : 0 < θ) :
    physicalAmplitude ε * physicalLambda L ε θ q *
      (12 * (physicalChainLength L Δ ε θ q : ℝ)) ≤ Δ := by
  let w := θ ^ ((q - 1) / q)
  have hw : 0 < w := Real.rpow_pos_of_pos hθ _
  have hfloor := Nat.floor_le (physicalChainArgument_nonneg (ε := ε) (q := q) hL hΔ hθ)
  have hT : (physicalChainLength L Δ ε θ q : ℝ) * physicalChainConstant ≤
      (L * Δ / ε ^ 2) * w := by
    exact (le_div_iff₀ physicalChainConstant_pos).mp hfloor
  have hm := mul_le_mul_of_nonneg_right hT (sq_nonneg ε)
  have hA : (L * Δ / ε ^ 2) * ε ^ 2 = L * Δ :=
    div_mul_cancel₀ _ (pow_ne_zero _ hε.ne')
  have hAw : (L * Δ / ε ^ 2) * w * ε ^ 2 = L * Δ * w := by
    calc
      _ = ((L * Δ / ε ^ 2) * ε ^ 2) * w := by ring
      _ = _ := by rw [hA]
  rw [hAw] at hm
  have heq : physicalAmplitude ε * physicalLambda L ε θ q *
      (12 * (physicalChainLength L Δ ε θ q : ℝ)) =
      physicalChainConstant * ε ^ 2 * (physicalChainLength L Δ ε θ q : ℝ) / (L * w) := by
    unfold physicalAmplitude physicalLambda physicalChainConstant
    change 8 * ε * (7000 * (8 * ε) / (L * w)) *
      (12 * (physicalChainLength L Δ ε θ q : ℝ)) = _
    field_simp [hL.ne', hw.ne'] <;> ring
  rw [heq]
  apply (div_le_iff₀ (mul_pos hL hw)).2
  nlinarith

/-- Public chain length and actual formula, with all scalar checks closed. -/
def physicalAdmissible {d : ℕ} (hd : 0 < d) {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (U : Fin (physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q) → Point d)
    (hU : Orthonormal ℝ U)
    (hT : 0 < physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q) :
    Admissible d Bool p q Δ σ L := by
  let θ := physicalTheta σ ε p hp.1
  have hθ : 0 < (θ : ℝ) := physicalTheta_pos hp.1
  exact scaledAdmissible hd U hU hT hp hq hΔ hσ hL
    (physicalAmplitude_pos hε) (physicalLambda_pos hL hε hθ) θ hθ
    (physical_gap_budget hL hΔ.le hε hθ)
    (physical_moment_budget hp.1 hε hσ)
    (physical_increment_budget_eq hL hε hθ hq).le

theorem physical_risk_identity {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (hd : 0 < d) {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (U : Fin (physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q) → Point d)
    (hU : Orthonormal ℝ U)
    (hT : 0 < physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q)
    (A : RandomAlgorithm d N Private) :
    let θ := physicalTheta σ ε p hp.1
    let T := physicalChainLength L Δ ε θ q
    let lam := physicalLambda L ε θ q
    let B := rescaledAlgorithm lam (physicalAmplitude ε) A
    risk (physicalAdmissible hd hp hq hL hΔ hε hσ U hU hT) A =
      ENNReal.ofReal (physicalAmplitude ε) *
        ∫⁻ r, ∫⁻ seeds, ENNReal.ofReal ‖populationGradient U (liftRadius T) (1/5)
          (B.output r (runTranscript (oracle U (liftRadius_pos hT) (1/5) θ) B r N seeds))‖
          ∂freshSeedLaw (oracle U (liftRadius_pos hT) (1/5) θ) N ∂B.privateLaw := by
  exact scaled_actualOutput_risk_identity U (liftRadius_pos hT)
    (physicalAmplitude_pos hε).le (physicalLambda_pos hL hε (physicalTheta_pos hp.1))
    (1/5) (physicalTheta σ ε p hp.1) A

end
end HeavyTailedNoise.RandomizedLift
