import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchEstimateHistoryMeasurable
import HeavyTailedNoise.Upper.Foundations.CoarseTrackerFreshBatchDrift

/-! The unique actual-history tracker increment and its pathwise cap. -/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

irreducible_def trackerIncrementOnHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar) (u : Fin P.T)
    (H : BatchHistory P d u) (seeds : Fin P.n → Seed) : ℝ :=
  trackerError I
      (batchDecision P u H - P.h • direction
        (batchEstimateOnHistory P I.oracle u H seeds))
      (coarseCenter P (batchCenter P u H)
        (I.oracle.response (batchDecision P u H)
          (seeds ⟨0, P.n_pos⟩))) -
    trackerError I (batchDecision P u H) (batchCenter P u H)

/-- The deterministic increment envelope holds for every response block,
even if its vectors are correlated through use in the completed estimate. -/
theorem trackerIncrementOnHistory_abs_le {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar) (u : Fin P.T)
    (H : BatchHistory P d u) (seeds : Fin P.n → Seed)
    (hbeta : 0 ≤ P.beta) (hh : 0 ≤ P.h) :
    |trackerIncrementOnHistory P I u H seeds| ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h := by
  have hbase := trackerError_increment_abs_le P I
    (batchDecision P u H) (batchCenter P u H)
    (I.oracle.response (batchDecision P u H)
      (seeds ⟨0, P.n_pos⟩))
    (batchEstimateOnHistory P I.oracle u H seeds) hbeta hh
  simpa only [trackerIncrementOnHistory] using hbase


end

end HeavyTailedNoise.UpperK1
