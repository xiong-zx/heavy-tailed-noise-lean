import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchAccumulatorTerminal
import HeavyTailedNoise.Upper.K1.CoarseTrackerActualBatch

/-!
The genuine logged complete batch reaches the same accumulator reset as the
unique local state fold. No independent seed or alternative state is used.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualBatch_end_accumulators_zero {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (r u : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    lowSum P (stateAt P (batchEndTime P u)
      (batchEndTranscript P O r u seeds)) = 0 ∧
    highSums P (stateAt P (batchEndTime P u)
      (batchEndTranscript P O r u seeds)) = fun _ => 0 := by
  rw [actualBatch_state_eq_fold P O r u seeds]
  exact foldResponses_fullBatch_accumulators_zero P u
    (stateAt P (batchStart P u.val)
      (batchHistoryOfRun P O u (r, seeds)).2)
    (upperBatchResponses O
      (batchDecision P u (batchHistoryOfRun P O u (r, seeds)))
      (batchSeedBlock P u seeds))

end

end HeavyTailedNoise.UpperK1
