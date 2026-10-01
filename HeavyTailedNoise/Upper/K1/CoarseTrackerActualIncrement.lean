import HeavyTailedNoise.Upper.K1.CoarseTrackerActualTerminal
import HeavyTailedNoise.Upper.K1.CoarseTrackerIncrement

/-!
The tracker-error consequence of the canonical actual-batch terminal state.
This file introduces no second transcript, estimator, or state update.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- In the genuine full oracle run, the coarse-error change across batch
`u` is exactly the increment integrated by the adaptive drift and mgf bounds. -/
theorem actualBatch_tracker_increment_eq
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (r u : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    trackerError I
      (point P (stateAt P (batchEndTime P u)
        (batchEndTranscript P I.oracle r u seeds)))
      (center P (stateAt P (batchEndTime P u)
        (batchEndTranscript P I.oracle r u seeds))) -
      trackerError I
        (batchDecision P u (batchHistoryOfRun P I.oracle u (r, seeds)))
        (batchCenter P u (batchHistoryOfRun P I.oracle u (r, seeds))) =
    trackerIncrementOnHistory P I u
      (batchHistoryOfRun P I.oracle u (r, seeds))
      (batchSeedBlock P u seeds) := by
  have hterminal := actualBatch_terminal_point_center P I.oracle r u seeds
  rw [hterminal.1, hterminal.2]
  rw [trackerIncrementOnHistory]

end

end HeavyTailedNoise.UpperK1
