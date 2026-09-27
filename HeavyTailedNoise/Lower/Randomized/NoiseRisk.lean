import HeavyTailedNoise.Lower.Randomized.OutputRisk
import HeavyTailedNoise.Lower.Fradin.NoiseInstance

/-!
The genuine one-dimensional Bernoulli quadratic pair defeats arbitrary
randomized gradient-only algorithms. There is no zero-respecting premise,
no fixed initial query, and no requirement to query the final output.
-/

namespace HeavyTailedNoise.RandomizedLift

open HeavyTailedNoise.Fradin MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false
universe u

def fairSign : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

def signPair {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L) (s : Bool) :
    Admissible d Seed p q Δ σ L := if s then I else reflectAdmissible I

theorem bernoulli_false_mass (ρ : unitInterval) :
    bernoulliLaw ρ {false} = ENNReal.ofReal (1 - (ρ : ℝ)) := by
  rw [bernoulliLaw, bernoulliMeasure_apply ρ (measurableSet_singleton false)]
  simp only [Set.mem_singleton_iff, Bool.true_eq_false, ↓reduceIte]
  rw [ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]

theorem noise_fresh_false_mass (L ε : ℝ) (ρ : unitInterval) (N : ℕ) :
    freshSeedLaw (noiseOracle L ε ρ) N {fun _ => false} =
      ENNReal.ofReal ((1 - (ρ : ℝ)) ^ N) := by
  haveI : IsProbabilityMeasure (noiseOracle L ε ρ).law := (noiseOracle L ε ρ).law_probability
  rw [freshSeedLaw, Measure.pi_singleton]
  simp only [noiseOracle, bernoulli_false_mass, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [ENNReal.ofReal_pow (sub_nonneg.mpr ρ.property.2)]

theorem noReveal_probability_ge_three_quarters (ρ : unitInterval) (N : ℕ)
    (hbudget : 4 * (N : ℝ) * (ρ : ℝ) ≤ 1) :
    (3 / 4 : ℝ) ≤ (1 - (ρ : ℝ)) ^ N := by
  have hbern := one_add_mul_le_pow (a := -(ρ : ℝ)) (by linarith [ρ.property.2]) N
  have hbern' : 1 - (N : ℝ) * (ρ : ℝ) ≤ (1 - (ρ : ℝ)) ^ N := by
    simpa only [mul_neg, ← sub_eq_add_neg] using hbern
  nlinarith [hbern']

theorem noise_reflection_response_false (L ε : ℝ) (ρ : unitInterval) (x : Point 1) :
    noiseResponse L ε ρ x false = -noiseResponse L ε ρ (-x) false := by
  simp

theorem noise_reflection_gradient_pair_barrier {L ε : ℝ} (hε : 0 ≤ ε)
    (x : Point 1) :
    8 * ε ≤ ‖noiseGradient L ε x‖ + ‖-noiseGradient L ε (-x)‖ := by
  have hdiff : noiseGradient L ε x - (-noiseGradient L ε (-x)) =
      (-8 * ε) • noiseUnit := by
    ext i
    simp only [noiseGradient, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
      smul_eq_mul]
    ring
  have h := norm_sub_le (noiseGradient L ε x) (-noiseGradient L ε (-x))
  rw [hdiff, norm_smul, norm_noiseUnit, mul_one, Real.norm_eq_abs] at h
  have ha : |-8 * ε| = 8 * ε := by
    rw [neg_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 8 * ε)]
  rwa [ha] at h

/-- The law is selected before the algorithm; only its sign is hidden. -/
theorem noisePair_averageRisk_gt {N : ℕ} {Private : Type u}
    [MeasurableSpace Private] {p q L Δ σ ε : ℝ}
    (ρ : unitInterval) (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hρ : 0 < (ρ : ℝ)) (hgap : 8 * ε ^ 2 ≤ L * Δ)
    (hmoment : 2 * (4 * ε) ^ p * (1 - (ρ : ℝ)) / (ρ : ℝ) ^ (p - 1) ≤ σ ^ p)
    (hbudget : 4 * (N : ℝ) * (ρ : ℝ) ≤ 1)
    (A : RandomAlgorithm 1 N Private) :
    let I := noiseInstance ρ hp hq hL hΔ hε hσ hρ hgap hmoment
    ENNReal.ofReal ε < ∫⁻ s, risk (signPair I s) A ∂bernoulliLaw fairSign := by
  let I := noiseInstance ρ hp hq hL hΔ hε hσ hρ hgap hmoment
  have hpair := singleton_pairRisk_lower_bound I (reflectAdmissible I) A false
    (by positivity : 0 ≤ 8 * ε) rfl
    (noise_reflection_response_false L ε ρ)
    (noise_reflection_gradient_pair_barrier hε.le)
  have hmass : ENNReal.ofReal (3 / 4 : ℝ) ≤
      freshSeedLaw I.oracle N {fun _ => false} := by
    change ENNReal.ofReal (3 / 4 : ℝ) ≤
      freshSeedLaw (noiseOracle L ε ρ) N {fun _ => false}
    rw [noise_fresh_false_mass]
    exact ENNReal.ofReal_le_ofReal (noReveal_probability_ge_three_quarters ρ N hbudget)
  have hlower : ENNReal.ofReal (6 * ε) ≤ risk I A + risk (reflectAdmissible I) A := by
    calc
      _ = ENNReal.ofReal (8 * ε) * ENNReal.ofReal (3 / 4 : ℝ) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * ε)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (8 * ε) * freshSeedLaw I.oracle N {fun _ => false} :=
        mul_le_mul' le_rfl hmass
      _ ≤ _ := hpair
  have hstrict : ENNReal.ofReal (2 * ε) < risk I A + risk (reflectAdmissible I) A :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 (by linarith) |>.trans_le hlower
  have havg := ENNReal.mul_lt_mul_right
    (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0) ENNReal.ofReal_ne_top hstrict
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (2 * ε) =
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  rw [hhalf] at havg
  change ENNReal.ofReal ε < ∫⁻ s, risk (signPair I s) A ∂bernoulliLaw fairSign
  rw [lintegral_bernoulliLaw]
  norm_num [fairSign, signPair, mul_add] at havg ⊢
  exact havg

/-- A legal fixed sign exists for each arbitrary algorithm, including N=0. -/
theorem noisePair_bad_instance {N : ℕ} {Private : Type u}
    [MeasurableSpace Private] {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hgap : 8 * ε ^ 2 ≤ L * Δ)
    (hbudget : 4 * (N : ℝ) * revealRate 8 (σ / ε) (tailExponent p) ≤ 1)
    (A : RandomAlgorithm 1 N Private) :
    ∃ I : Admissible 1 Bool p q Δ σ L, ENNReal.ofReal ε < risk I A := by
  let ρ := revealParameter 8 (σ / ε) (tailExponent p)
    (by norm_num) (tailExponent_pos hp.1)
  let I := noiseInstance_revealParameter (c := 8) (by norm_num)
    hp hq hL hΔ hε hσ hgap
  obtain ⟨s, hs⟩ := bad_orientation_of_average (bernoulliLaw fairSign) (signPair I) A
    (noisePair_averageRisk_gt ρ hp hq hL hΔ hε hσ
      (revealRate_pos (by norm_num)) hgap
      (noise_moment_condition_revealParameter (by norm_num : (8 : ℝ) ≤ 8) hε hσ hp.1)
      hbudget A)
  exact ⟨signPair I s, hs⟩

theorem noisePair_refutes_dimension_uniform_guarantee {N : ℕ} {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hgap : 8 * ε ^ 2 ≤ L * Δ)
    (hbudget : 4 * (N : ℝ) * revealRate 8 (σ / ε) (tailExponent p) ≤ 1) :
    ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ L ε := by
  intro hguarantee
  obtain ⟨Private, privateSpace, A, hA⟩ := hguarantee 1 (by norm_num)
  letI : MeasurableSpace Private := privateSpace
  obtain ⟨I, hbad⟩ := noisePair_bad_instance hp hq hL hΔ hε hσ hgap hbudget A
  exact not_lt_of_ge (hA Bool inferInstance I) hbad

def noiseRateConstant (p : ℝ) : ℝ := 1 / (4 * (8 : ℝ) ^ tailExponent p)

theorem noiseRateConstant_pos (p : ℝ) : 0 < noiseRateConstant p := by
  unfold noiseRateConstant
  positivity

theorem revealRate_times_noise_ratio {S r : ℝ} (hS : 0 ≤ S) (hr : 0 < r) :
    S ^ r * revealRate 8 S r ≤ (8 : ℝ) ^ r := by
  unfold revealRate
  split_ifs with h
  · simpa using Real.rpow_le_rpow hS h hr.le
  · have hs : 0 < S := by linarith
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 8) hS]
    exact (le_of_eq (by field_simp [(Real.rpow_pos_of_pos hs r).ne'] <;> ring))

theorem noiseRate_budget_implies_reveal_budget {N : ℕ} {p σ ε : ℝ}
    (hp : 1 < p) (hσ : 0 ≤ σ) (hε : 0 < ε)
    (hN : (N : ℝ) ≤ noiseRateConstant p * (σ / ε) ^ tailExponent p) :
    4 * (N : ℝ) * revealRate 8 (σ / ε) (tailExponent p) ≤ 1 := by
  have hρ := revealRate_pos (c := 8) (S := σ / ε) (r := tailExponent p) (by norm_num)
  have hprod := revealRate_times_noise_ratio (div_nonneg hσ hε.le) (tailExponent_pos hp)
  have hn := mul_le_mul_of_nonneg_right hN hρ.le
  have hpow : 0 < (8 : ℝ) ^ tailExponent p := Real.rpow_pos_of_pos (by norm_num) _
  unfold noiseRateConstant at hn
  have hfrac : (1 / (4 * (8 : ℝ) ^ tailExponent p) *
      (σ / ε) ^ tailExponent p) * revealRate 8 (σ / ε) (tailExponent p) =
      ((σ / ε) ^ tailExponent p * revealRate 8 (σ / ε) (tailExponent p)) /
        (4 * (8 : ℝ) ^ tailExponent p) := by ring
  rw [hfrac] at hn
  have hbound := (div_le_div_of_nonneg_right hprod (by positivity :
    0 ≤ 4 * (8 : ℝ) ^ tailExponent p))
  have hquarter : (8 : ℝ) ^ tailExponent p / (4 * (8 : ℝ) ^ tailExponent p) = 1 / 4 := by
    field_simp [hpow.ne']
  rw [hquarter] at hbound
  nlinarith [hn.trans hbound]

end
end HeavyTailedNoise.RandomizedLift
