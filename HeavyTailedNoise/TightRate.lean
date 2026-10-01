import HeavyTailedNoise.Lower.Full
import HeavyTailedNoise.Upper.K1.Main
import HeavyTailedNoise.Upper.K1.RateComparison
import HeavyTailedNoise.Upper.K1.UniformGuarantee

/-!
Same-model matching-rate corollaries for the strict-K=1 gradient-only oracle.
The upper witness is the literal shared-batch algorithm. The lower statement
retains the published dimension-uniform, fixed-response randomized algorithm
class and its absolute-accuracy regime. Neither result uses a Fradin
zero-respecting restriction or an extra estimator-error premise.
-/

namespace HeavyTailedNoise

open HeavyTailedNoise.UpperK1
open HeavyTailedNoise.RandomizedLift
open HeavyTailedNoise.Fradin

noncomputable section

universe u

/-- The dimensionless rate in the actual upper response cap. -/
def strictK1UpperRateShape (p q Lbar Δ σ ε : ℝ) : ℝ :=
  (paperS σ ε) ^ (p / (p - 1)) +
    paperAplus Lbar Δ ε *
      max ((paperS σ ε) ^ 2)
        ((paperS σ ε) ^ ((p / (p - 1)) / q))

/-- The max-form lower rate from the complete unrestricted lower package. -/
def strictK1LowerRateShape (p q Lbar Δ σ ε : ℝ) : ℝ :=
  max (baselineRate (Lbar * Δ / ε ^ 2)
      ((σ / ε) ^ tailExponent p) q)
    ((Lbar * Δ / ε ^ 2) * (paperS σ ε) ^ 2)

theorem strictK1_precision_constant :
    2 * physicalChainConstant = (10752000 : ℝ) := by
  norm_num [physicalChainConstant]

/-- The common `A ≥ 10,752,000` regime implies the already published
absolute-accuracy condition, with no additional physical assumption. -/
theorem strictK1_absolute_accuracy_of_precision
    {Lbar Δ ε : ℝ} (hLbar : 0 < Lbar) (hΔ : 0 < Δ)
    (hε : 0 < ε)
    (hA : (10752000 : ℝ) ≤ Lbar * Δ / ε ^ 2) :
    ε ≤ physicalAccuracyConstant * Real.sqrt (Lbar * Δ) := by
  let c : ℝ := 2 * physicalChainConstant
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (by norm_num) physicalChainConstant_pos
  have hA' : c ≤ Lbar * Δ / ε ^ 2 := by
    simpa only [c, strictK1_precision_constant] using hA
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hprod : c * ε ^ 2 ≤ Lbar * Δ :=
    (le_div_iff₀ hεsq).mp hA'
  have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsquare : (ε * Real.sqrt c) ^ 2 ≤
      (Real.sqrt (Lbar * Δ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le,
      Real.sq_sqrt (mul_pos hLbar hΔ).le]
    convert hprod using 1 <;> ring
  have hlinear : ε * Real.sqrt c ≤ Real.sqrt (Lbar * Δ) :=
    (sq_le_sq₀ (mul_nonneg hε.le hsqrtc.le)
      (Real.sqrt_nonneg _)).mp hsquare
  have hdivision : ε ≤ Real.sqrt (Lbar * Δ) / Real.sqrt c :=
    (le_div_iff₀ hsqrtc).mpr hlinear
  calc
    ε ≤ Real.sqrt (Lbar * Δ) / Real.sqrt c := hdivision
    _ = physicalAccuracyConstant * Real.sqrt (Lbar * Δ) := by
      dsimp [physicalAccuracyConstant, c]
      ring

/-- The actual upper witness and the published unrestricted lower minimax
rate have the same physical shape, up to factors depending only on `p,q`.
The instance `I` is arbitrary in the shared `Admissible` model. -/
theorem strictK1_same_model_tight_rate
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar ε : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (hε : 0 < ε)
    (hA : (10752000 : ℝ) ≤ Lbar * Δ / ε ^ 2) :
    let P := upperSchedule p q Δ σ Lbar ε hε
    risk I (algorithm P) ≤ ENNReal.ofReal ε ∧
      (responseCount P : ℝ) ≤
        2 * upperRateConstant p q *
          strictK1LowerRateShape p q Lbar Δ σ ε ∧
      ENNReal.ofReal
        (fullPublicRateCoefficient p q *
          strictK1LowerRateShape p q Lbar Δ σ ε) <
        (dimensionUniformMinimaxComplexity.{u, 0}
          p q Δ σ Lbar ε : ENNReal) ∧
      strictK1UpperRateShape p q Lbar Δ σ ε ≤
        2 * strictK1LowerRateShape p q Lbar Δ σ ε ∧
      strictK1LowerRateShape p q Lbar Δ σ ε ≤
        2 * strictK1UpperRateShape p q Lbar Δ σ ε := by
  dsimp only
  let P := upperSchedule p q Δ σ Lbar ε hε
  have hA' : 2 * physicalChainConstant ≤ Lbar * Δ / ε ^ 2 := by
    simpa only [strictK1_precision_constant] using hA
  have hAone : 1 ≤ Lbar * Δ / ε ^ 2 := by
    exact (by norm_num : (1 : ℝ) ≤ 10752000).trans hA
  have hUpper := UpperK1.Admissible.strict_k1_shared_batch_ema_upper
    I ε hε
  change risk I (algorithm P) ≤ ENNReal.ofReal ε ∧
    (responseCount P : ℝ) ≤
      upperRateConstant p q * strictK1UpperRateShape p q Lbar Δ σ ε
    at hUpper
  have hLower := full_minimax_complexity_lower_bound.{u}
    I.p_range I.q_range I.Lbar_pos I.delta_pos hε I.sigma_nonneg hA'
  have hCompareUL := paper_upper_shape_le_two_full_lower_shape
    p q Lbar Δ σ ε I.p_range.1 I.q_range I.sigma_nonneg hε hAone
  have hCompareLU := full_lower_shape_le_two_paper_upper_shape
    p q Lbar Δ σ ε I.p_range.1 I.q_range I.sigma_nonneg hε hAone
  have hUL : strictK1UpperRateShape p q Lbar Δ σ ε ≤
      2 * strictK1LowerRateShape p q Lbar Δ σ ε := by
    simpa only [strictK1UpperRateShape, strictK1LowerRateShape,
      baselineRate, tailExponent] using hCompareUL
  have hLU : strictK1LowerRateShape p q Lbar Δ σ ε ≤
      2 * strictK1UpperRateShape p q Lbar Δ σ ε := by
    simpa only [strictK1UpperRateShape, strictK1LowerRateShape,
      baselineRate, tailExponent] using hCompareLU
  have hcap : (responseCount P : ℝ) ≤
      2 * upperRateConstant p q *
        strictK1LowerRateShape p q Lbar Δ σ ε := by
    calc
      _ ≤ upperRateConstant p q *
          strictK1UpperRateShape p q Lbar Δ σ ε := hUpper.2
      _ ≤ upperRateConstant p q *
          (2 * strictK1LowerRateShape p q Lbar Δ σ ε) :=
        mul_le_mul_of_nonneg_left hUL (upperRateConstant_pos p q).le
      _ = _ := by ring
  refine ⟨hUpper.1, hcap, ?_, hUL, hLU⟩
  simpa only [strictK1LowerRateShape, paperS] using hLower

/-- Both inequalities refer to the same unrestricted fixed-response
dimension-uniform minimax complexity. The upper side uses the actual
shared-batch algorithm encoded as a fixed-cap uniform guarantee; the lower
side is the complete published finite-q lower theorem. -/
theorem strictK1_same_model_minimax_tight_rate
    {p q Δ σ Lbar ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hLbar : 0 < Lbar) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hA : (10752000 : ℝ) ≤ Lbar * Δ / ε ^ 2) :
    ENNReal.ofReal
      (fullPublicRateCoefficient p q *
        strictK1LowerRateShape p q Lbar Δ σ ε) <
      (dimensionUniformMinimaxComplexity.{u, 0}
        p q Δ σ Lbar ε : ENNReal) ∧
    (dimensionUniformMinimaxComplexity.{u, 0}
        p q Δ σ Lbar ε : ENNReal) ≤
      ENNReal.ofReal
        (2 * upperRateConstant p q *
          strictK1LowerRateShape p q Lbar Δ σ ε) := by
  have hA' : 2 * physicalChainConstant ≤ Lbar * Δ / ε ^ 2 := by
    simpa only [strictK1_precision_constant] using hA
  have hAone : 1 ≤ Lbar * Δ / ε ^ 2 :=
    (by norm_num : (1 : ℝ) ≤ 10752000).trans hA
  have hlower := full_minimax_complexity_lower_bound.{u}
    hp hq hLbar hΔ hε hσ hA'
  have hupper := strict_k1_shared_batch_ema_minimax_le_rate.{u}
    p q Δ σ Lbar ε hp hq hΔ hσ hLbar hε
  have hcompare := paper_upper_shape_le_two_full_lower_shape
    p q Lbar Δ σ ε hp.1 hq hσ hε hAone
  have hshape : strictK1UpperRateShape p q Lbar Δ σ ε ≤
      2 * strictK1LowerRateShape p q Lbar Δ σ ε := by
    simpa only [strictK1UpperRateShape, strictK1LowerRateShape,
      baselineRate, tailExponent] using hcompare
  have hcap : upperRateConstant p q *
      strictK1UpperRateShape p q Lbar Δ σ ε ≤
      2 * upperRateConstant p q *
        strictK1LowerRateShape p q Lbar Δ σ ε := by
    calc
      _ ≤ upperRateConstant p q *
          (2 * strictK1LowerRateShape p q Lbar Δ σ ε) :=
        mul_le_mul_of_nonneg_left hshape (upperRateConstant_pos p q).le
      _ = _ := by ring
  constructor
  · simpa only [strictK1LowerRateShape, paperS] using hlower
  · have hupper' :
        (dimensionUniformMinimaxComplexity.{u, 0}
          p q Δ σ Lbar ε : ENNReal) ≤
        ENNReal.ofReal
          (upperRateConstant p q *
            strictK1UpperRateShape p q Lbar Δ σ ε) := by
      simpa only [strictK1UpperRateShape] using hupper
    exact hupper'.trans (ENNReal.ofReal_le_ofReal hcap)

/-- Every precommitted natural response budget below the published lower
threshold fails the dimension-uniform guarantee for arbitrary measurable
randomized algorithms of that fixed cap. -/
theorem strictK1_same_model_refutes_response_budget
    {p q Δ σ Lbar ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hLbar : 0 < Lbar) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hA : (10752000 : ℝ) ≤ Lbar * Δ / ε ^ 2)
    (N : ℕ)
    (hN : (N : ℝ) ≤ fullPublicRateCoefficient p q *
      strictK1LowerRateShape p q Lbar Δ σ ε) :
    ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ Lbar ε := by
  have haccuracy := strictK1_absolute_accuracy_of_precision
    hLbar hΔ hε hA
  apply full_lower_bound_refutes_response_budget.{u} N
    hp hq hLbar hΔ hε hσ haccuracy
  simpa only [strictK1LowerRateShape, paperS] using hN

end

end HeavyTailedNoise
