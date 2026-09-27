import HeavyTailedNoise.Lower.Randomized.PhysicalParameters
import HeavyTailedNoise.Lower.Randomized.NoiseRisk
import HeavyTailedNoise.Analysis.LowerBoundArithmetic

/-!
Public finite-q response accounting. The chain/noise dichotomy is numerical.
The actual unscaled geometric average-risk premise is named explicitly;
its discharge belongs to the independently proved Haar experiment.
-/

namespace HeavyTailedNoise.RandomizedLift

open HeavyTailedNoise.Fradin MeasureTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false
universe u

def physicalChainRateFactor (p q : ℝ) : ℝ := (368 : ℝ) ^ (tailExponent p / q)

def physicalChainRateConstant (p q : ℝ) : ℝ :=
  1 / (32 * physicalChainConstant * physicalChainRateFactor p q)

def physicalBaselineCoefficient (p q : ℝ) : ℝ :=
  (1 / 3) * min (physicalChainRateConstant p q) (noiseRateConstant p)

theorem physicalChainRateFactor_pos (p q : ℝ) : 0 < physicalChainRateFactor p q := by
  unfold physicalChainRateFactor
  positivity

theorem physicalChainRateConstant_pos (p q : ℝ) : 0 < physicalChainRateConstant p q := by
  unfold physicalChainRateConstant
  exact one_div_pos.mpr (mul_pos
    (mul_pos (by norm_num : (0 : ℝ) < 32) physicalChainConstant_pos)
    (physicalChainRateFactor_pos p q))

theorem physicalBaselineCoefficient_pos (p q : ℝ) : 0 < physicalBaselineCoefficient p q := by
  unfold physicalBaselineCoefficient
  exact mul_pos (by norm_num)
    (lt_min (physicalChainRateConstant_pos p q) (noiseRateConstant_pos p))

theorem revealRate_sharp_chain_factor {S r q : ℝ} (hS : 368 < S) (hq : 1 ≤ q) :
    (368 : ℝ) ^ (r / q) * (revealRate 368 S r) ^ ((q - 1) / q) /
      revealRate 368 S r = S ^ (r / q) := by
  have hS0 : 0 < S := by linarith
  have hq0 : 0 < q := by linarith
  have hexp : r * ((q - 1) / q) + r / q = r := by
    field_simp [hq0.ne'] <;> ring
  have hθpow : (revealRate 368 S r) ^ ((q - 1) / q) =
      (368 : ℝ) ^ (r * ((q - 1) / q)) / S ^ (r * ((q - 1) / q)) := by
    rw [revealRate, if_neg (not_le.mpr hS),
      ← Real.rpow_mul (div_nonneg (by norm_num) hS0.le),
      Real.div_rpow (by norm_num) hS0.le]
  have hθ : revealRate 368 S r = (368 : ℝ) ^ r / S ^ r := by
    rw [revealRate, if_neg (not_le.mpr hS), Real.div_rpow (by norm_num) hS0.le]
  have hsplitS : S ^ r = S ^ (r * ((q - 1) / q)) * S ^ (r / q) := by
    rw [← Real.rpow_add hS0, hexp]
  have hsplitC : (368 : ℝ) ^ r =
      (368 : ℝ) ^ (r * ((q - 1) / q)) * (368 : ℝ) ^ (r / q) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 368), hexp]
  rw [hθpow, hθ, hsplitS, hsplitC]
  field_simp [(Real.rpow_pos_of_pos hS0 (r * ((q - 1) / q))).ne',
    (Real.rpow_pos_of_pos hS0 (r / q)).ne',
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 368) (r * ((q - 1) / q))).ne',
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 368) (r / q)).ne'] <;> ring

theorem revealRate_sharp_chain_factor_bounds {S r q : ℝ}
    (hS : 0 ≤ S) (hr : 0 < r) (hq : 1 ≤ q) :
    1 ≤ (368 : ℝ) ^ (r / q) * (revealRate 368 S r) ^ ((q - 1) / q) /
        revealRate 368 S r ∧
    S ^ (r / q) ≤ (368 : ℝ) ^ (r / q) * (revealRate 368 S r) ^ ((q - 1) / q) /
        revealRate 368 S r := by
  have hq0 : 0 < q := by linarith
  have he : 0 ≤ r / q := div_nonneg hr.le hq0.le
  by_cases hs : S ≤ 368
  · simp only [revealRate, if_pos hs, Real.one_rpow, mul_one, div_one]
    exact ⟨Real.one_le_rpow (by norm_num) he, Real.rpow_le_rpow hS hs he⟩
  · rw [revealRate_sharp_chain_factor (lt_of_not_ge hs) hq]
    exact ⟨Real.one_le_rpow (by linarith) he, le_rfl⟩

/-- This is the actual budget dichotomy, including sigma=0 and q=1.
The accuracy condition is the one absolute restriction A≥2C. -/
theorem physical_baseline_budget_dichotomy {A S p q : ℝ} (N : ℕ)
    (hA : 2 * physicalChainConstant ≤ A) (hS : 0 ≤ S)
    (hp : 1 < p) (hq : 1 ≤ q)
    (hN : (N : ℝ) ≤ physicalBaselineCoefficient p q *
      (A + S ^ tailExponent p + A * (S ^ tailExponent p) ^ (1 / q))) :
    let θ := revealRate 368 S (tailExponent p)
    let Z := A * θ ^ ((q - 1) / q) / physicalChainConstant
    (2 ≤ Z ∧ 0 < ⌊Z⌋₊ ∧ 8 * (N : ℝ) * θ ≤ (⌊Z⌋₊ : ℝ)) ∨
      (N : ℝ) ≤ noiseRateConstant p * S ^ tailExponent p := by
  let θ := revealRate 368 S (tailExponent p)
  let Z := A * θ ^ ((q - 1) / q) / physicalChainConstant
  let B := S ^ tailExponent p
  let D := physicalChainRateFactor p q
  let K := D * (A * θ ^ ((q - 1) / q) / θ)
  let m := min (physicalChainRateConstant p q) (noiseRateConstant p)
  have hA0 : 0 ≤ A :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) physicalChainConstant_pos.le).trans hA
  have hB0 : 0 ≤ B := Real.rpow_nonneg hS _
  have hθ : 0 < θ := revealRate_pos (by norm_num)
  have hD : 0 < D := physicalChainRateFactor_pos p q
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm : 0 ≤ m := le_min (physicalChainRateConstant_pos p q).le (noiseRateConstant_pos p).le
  have hc : 0 ≤ physicalBaselineCoefficient p q := (physicalBaselineCoefficient_pos p q).le
  have hpower : (S ^ tailExponent p) ^ (1 / q) = S ^ (tailExponent p / q) := by
    rw [← Real.rpow_mul hS]
    congr 1
    ring
  have hfactor := revealRate_sharp_chain_factor_bounds hS (tailExponent_pos hp) hq
  have hAssoc : A * (D * θ ^ ((q - 1) / q) / θ) = K := by
    dsimp [K]
    ring
  have hAK : A ≤ K := by
    have h := mul_le_mul_of_nonneg_left hfactor.1 hA0
    change A * 1 ≤ A * (D * θ ^ ((q - 1) / q) / θ) at h
    rw [hAssoc] at h
    simpa only [mul_one] using h
  have hWK : A * (S ^ tailExponent p) ^ (1 / q) ≤ K := by
    rw [hpower]
    have h := mul_le_mul_of_nonneg_left hfactor.2 hA0
    change A * S ^ (tailExponent p / q) ≤ A * (D * θ ^ ((q - 1) / q) / θ) at h
    rwa [hAssoc] at h
  have hX : A + B + A * (S ^ tailExponent p) ^ (1 / q) ≤ 3 * max K B := by
    nlinarith [le_max_left K B, le_max_right K B]
  have hNmax : (N : ℝ) ≤ m * max K B := by
    calc
      _ ≤ physicalBaselineCoefficient p q * (A + B + A * (S ^ tailExponent p) ^ (1 / q)) := hN
      _ ≤ physicalBaselineCoefficient p q * (3 * max K B) := mul_le_mul_of_nonneg_left hX hc
      _ = m * max K B := by unfold physicalBaselineCoefficient; dsimp [m]; ring
  by_cases hKB : K ≤ B
  · right
    rw [max_eq_right hKB] at hNmax
    exact hNmax.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hB0)
  · have hNK : (N : ℝ) ≤ physicalChainRateConstant p q * K := by
      rw [max_eq_left (lt_of_not_ge hKB).le] at hNmax
      exact hNmax.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hK)
    have hNKZ : (N : ℝ) ≤ Z / (32 * θ) := by
      have heq : physicalChainRateConstant p q * K = Z / (32 * θ) := by
        dsimp [physicalChainRateConstant, K, Z, D]
        field_simp [hθ.ne', (physicalChainRateFactor_pos p q).ne',
          physicalChainConstant_pos.ne'] <;> ring
      rwa [heq] at hNK
    by_cases hZ : 2 ≤ Z
    · left
      have hfloor : Z / 2 ≤ (⌊Z⌋₊ : ℝ) := natFloor_ge_half_of_ge_two hZ
      have hT2 : (2 : ℕ) ≤ ⌊Z⌋₊ := Nat.le_floor hZ
      refine ⟨hZ, ?_, ?_⟩
      · change 0 < ⌊Z⌋₊
        exact lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hT2
      · change 8 * (N : ℝ) * θ ≤ (⌊Z⌋₊ : ℝ)
        have hn := (le_div_iff₀ (by positivity : 0 < 32 * θ)).mp hNKZ
        nlinarith
    · right
      have hZsmall : Z < 2 := lt_of_not_ge hZ
      have hSlarge : 368 < S := by
        by_contra hnot
        have hs : S ≤ 368 := le_of_not_gt hnot
        have hθone : θ = 1 := revealRate_eq_one hs
        have hz : Z = A / physicalChainConstant := by dsimp [Z]; rw [hθone]; simp
        rw [hz] at hZsmall
        have h := (div_lt_iff₀ physicalChainConstant_pos).mp hZsmall
        linarith
      have hSpos : 0 < S := by linarith
      have hθB : θ * B = (368 : ℝ) ^ tailExponent p := by
        dsimp [θ, B]
        rw [revealRate, if_neg (not_le.mpr hSlarge), Real.div_rpow (by norm_num) hSpos.le]
        exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hSpos _).ne'
      have hpow : 0 < (368 : ℝ) ^ tailExponent p := Real.rpow_pos_of_pos (by norm_num) _
      have hsmallwork : (N : ℝ) ≤ B / (16 * (368 : ℝ) ^ tailExponent p) := by
        calc
          _ ≤ Z / (32 * θ) := hNKZ
          _ ≤ 2 / (32 * θ) := div_le_div_of_nonneg_right hZsmall.le (by positivity)
          _ = B / (16 * (368 : ℝ) ^ tailExponent p) := by
            apply (div_eq_div_iff (by positivity : 32 * θ ≠ 0) (by positivity : 16 * (368 : ℝ) ^ tailExponent p ≠ 0)).2
            nlinarith
      have h8 : 0 < (8 : ℝ) ^ tailExponent p := Real.rpow_pos_of_pos (by norm_num) _
      have hpowle : (8 : ℝ) ^ tailExponent p ≤ (368 : ℝ) ^ tailExponent p :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (tailExponent_pos hp).le
      have hcoef : 1 / (16 * (368 : ℝ) ^ tailExponent p) ≤ noiseRateConstant p := by
        unfold noiseRateConstant
        apply (div_le_div_iff₀ (by positivity : 0 < 16 * (368 : ℝ) ^ tailExponent p)
          (by positivity : 0 < 4 * (8 : ℝ) ^ tailExponent p)).2
        nlinarith
      calc
        _ ≤ B / (16 * (368 : ℝ) ^ tailExponent p) := hsmallwork
        _ = (1 / (16 * (368 : ℝ) ^ tailExponent p)) * B := by ring
        _ ≤ noiseRateConstant p * B := mul_le_mul_of_nonneg_right hcoef hB0

theorem physical_accuracy_implies_noise_gap {L Δ ε : ℝ} (hε : 0 < ε)
    (hA : 2 * physicalChainConstant ≤ L * Δ / ε ^ 2) :
    8 * ε ^ 2 ≤ L * Δ := by
  have h8 : (8 : ℝ) ≤ 2 * physicalChainConstant := by norm_num [physicalChainConstant]
  exact (le_div_iff₀ (sq_pos_of_pos hε)).mp (h8.trans hA)

/-- Concrete risk interface for the actual physical family. The one prior
and one dimension precede the algorithm. Only the unscaled geometric risk
estimate remains an input, and the normalization is independent of V. -/
theorem physical_averageRisk_gt_of_unscaled_average
    {d N : ℕ} {Private Frame : Type*}
    [MeasurableSpace Private] [MeasurableSpace Frame]
    (hd : 0 < d) {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hT : 0 < physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q)
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (frameAt : Frame → Fin (physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q) → Point d)
    (hframe : ∀ V, Orthonormal ℝ (frameAt V))
    (hgeometry : ∀ B : RandomAlgorithm d N Private,
      ENNReal.ofReal (1 / 8 : ℝ) <
        ∫⁻ V, ∫⁻ r, ∫⁻ seeds, ENNReal.ofReal ‖populationGradient (frameAt V)
          (liftRadius (physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q)) (1/5)
          (B.output r (runTranscript
            (oracle (frameAt V) (liftRadius_pos hT) (1/5) (physicalTheta σ ε p hp.1)) B r N seeds))‖
          ∂freshSeedLaw (oracle (frameAt V) (liftRadius_pos hT) (1/5) (physicalTheta σ ε p hp.1)) N
          ∂B.privateLaw ∂μ)
    (A : RandomAlgorithm d N Private) :
    ENNReal.ofReal ε < ∫⁻ V,
      risk (physicalAdmissible hd hp hq hL hΔ hε hσ (frameAt V) (hframe V) hT) A ∂μ := by
  let θ := physicalTheta σ ε p hp.1
  let T := physicalChainLength L Δ ε θ q
  let lam := physicalLambda L ε θ q
  let B := rescaledAlgorithm lam (physicalAmplitude ε) A
  have hpoint (V : Frame) :=
    physical_risk_identity hd hp hq hL hΔ hε hσ (frameAt V) (hframe V) hT A
  have hscaled := ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_pos.mpr (physicalAmplitude_pos hε)).ne'
    ENNReal.ofReal_ne_top (hgeometry B)
  have hthreshold : ENNReal.ofReal (physicalAmplitude ε) * ENNReal.ofReal (1 / 8 : ℝ) =
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul (physicalAmplitude_pos hε).le]
    congr 1
    unfold physicalAmplitude
    ring
  rw [hthreshold] at hscaled
  simp_rw [hpoint]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact hscaled

/-- Extracts a deterministic legal frame through Model.Distributional.
The actual Haar/geometric estimate is still an explicit theorem argument. -/
theorem physical_geometry_refutes_dimension_uniform_guarantee
    {d N : ℕ} {Frame : Type*} [MeasurableSpace Frame]
    (hd : 0 < d) {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hT : 0 < physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q)
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (frameAt : Frame → Fin (physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q) → Point d)
    (hframe : ∀ V, Orthonormal ℝ (frameAt V))
    (hgeometry : ∀ (Private : Type u) (privateSpace : MeasurableSpace Private)
      (B : @RandomAlgorithm d N Private privateSpace),
      ENNReal.ofReal (1 / 8 : ℝ) <
        ∫⁻ V, ∫⁻ r, ∫⁻ seeds, ENNReal.ofReal ‖populationGradient (frameAt V)
          (liftRadius (physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q)) (1/5)
          (B.output r (runTranscript
            (oracle (frameAt V) (liftRadius_pos hT) (1/5) (physicalTheta σ ε p hp.1)) B r N seeds))‖
          ∂freshSeedLaw (oracle (frameAt V) (liftRadius_pos hT) (1/5) (physicalTheta σ ε p hp.1)) N
          ∂B.privateLaw ∂μ) :
    ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ L ε := by
  apply fixed_average_refutes_dimension_uniform_guarantee hd μ
    (fun V => physicalAdmissible hd hp hq hL hΔ hε hσ (frameAt V) (hframe V) hT)
  intro Private privateSpace A
  letI : MeasurableSpace Private := privateSpace
  exact physical_averageRisk_gt_of_unscaled_average hd hp hq hL hΔ hε hσ hT μ frameAt hframe
    (hgeometry Private privateSpace) A

/-- Public numerical bridge awaiting the actual chain-risk theorem.
The chain premise must apply to unrestricted shared-model algorithms. -/
theorem physical_baseline_refutes_of_chain
    {p q L Δ σ ε : ℝ} (N : ℕ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hA : 2 * physicalChainConstant ≤ L * Δ / ε ^ 2)
    (hN : (N : ℝ) ≤ physicalBaselineCoefficient p q *
      ((L * Δ / ε ^ 2) + (σ / ε) ^ tailExponent p +
        (L * Δ / ε ^ 2) * ((σ / ε) ^ tailExponent p) ^ (1 / q)))
    (hchain :
      0 < physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q →
      8 * (N : ℝ) * (physicalTheta σ ε p hp.1 : ℝ) ≤
        (physicalChainLength L Δ ε (physicalTheta σ ε p hp.1) q : ℝ) →
      ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ L ε) :
    ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ L ε := by
  rcases physical_baseline_budget_dichotomy N hA (div_nonneg hσ hε.le) hp.1 hq hN with
    hlarge | hnoise
  · exact hchain hlarge.2.1 hlarge.2.2
  · exact noisePair_refutes_dimension_uniform_guarantee hp hq hL hΔ hε hσ
      (physical_accuracy_implies_noise_gap hε hA)
      (noiseRate_budget_implies_reveal_budget hp.1 hσ hε hnoise)

end
end HeavyTailedNoise.RandomizedLift
