import HeavyTailedNoise.Upper.K1.EstimatorAverageBound
import HeavyTailedNoise.Upper.K1.StationarityActualPhysicalConditional
import HeavyTailedNoise.Upper.K1.BudgetRateMax

/-!
Public interface for the frozen strict-K=1 shared-batch EMA method.
The actual estimator-error theorem is discharged in the unconditional upper
statement below.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

/-- The manuscript schedule with explicit legal numerical constants. -/
def upperSchedule (p q Δ σ Lbar ε : ℝ) (hε : 0 < ε) : Schedule q :=
  paperSchedule p q Δ σ Lbar ε (upperCtail p) (1 / 8)
    (upperKappa p q) (upperCb p q) upperCI hε (by norm_num)
    (upperCb_pos p q) upperCI_pos

/-- One dimension-free response coefficient depending only on `p,q`. -/
def upperRateConstant (p q : ℝ) : ℝ :=
  paperRateConstant p q (upperCtail p) (1 / 8) (upperCb p q) upperCI

theorem upperRateConstant_pos (p q : ℝ) : 0 < upperRateConstant p q := by
  have hfirst : 0 < 2 + upperCI * (2 * upperCtail p) ^ paperA p := by
    have hCI := upperCI_pos
    have htail := upperCtail_pos p
    positivity
  exact lt_of_lt_of_le hfirst (le_max_left _ _)

/-- The no-extra-analytical-premise upper statement for the unchanged
actual algorithm and the original finite-q gradient-only oracle class. -/
theorem Admissible.strict_k1_shared_batch_ema_upper
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε : ℝ) (hε : 0 < ε) :
    let P := upperSchedule p q Δ σ Lbar ε hε
    risk I (algorithm P) ≤ ENNReal.ofReal ε ∧
      (responseCount P : ℝ) ≤
        upperRateConstant p q *
          ((paperS σ ε) ^ (p / (p - 1)) +
            paperAplus Lbar Δ ε *
              max ((paperS σ ε) ^ 2)
                ((paperS σ ε) ^ ((p / (p - 1)) / q))) := by
  dsimp only
  constructor
  · apply Admissible.paperSchedule_risk_le_of_actual_estimator_error
      I ε (upperCtail p) (1 / 8) (upperKappa p q)
      (upperCb p q) upperCI hε (by norm_num) (by norm_num)
      (upperCb_pos p q) upperCI_pos
    exact Admissible.paperSchedule_average_actual_estimator_error_le I ε hε
  · exact paperSchedule_responseCount_le_rate_max
      p q Δ σ Lbar ε (upperCtail p) (1 / 8) (upperKappa p q)
      (upperCb p q) upperCI I.p_range.1 I.p_range.2 I.q_range hε
      (upperCtail_ge_twelve p I.p_range.1 I.p_range.2)
      (by norm_num) (upperCb_pos p q) upperCI_pos

end

end HeavyTailedNoise.UpperK1
