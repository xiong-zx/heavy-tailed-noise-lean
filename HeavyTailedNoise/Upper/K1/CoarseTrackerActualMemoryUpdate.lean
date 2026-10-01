import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchMemoryExpanded
import HeavyTailedNoise.Upper.K1.CoarseTrackerActualBoundaryAccumulatorZero

/-!
At every genuine logged runtime batch, each high-band memory is updated by
the single current-batch mean and the one algorithmic EMA weight. The actual
pre-batch high accumulator is zero by the proved boundary-state invariant.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualBatch_memory_eq_highEMA {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (r u : Fin P.T) (seeds : Fin (responseCount P) → Seed)
    (j : Fin P.J) :
    let H := batchHistoryOfRun P O u (r, seeds)
    let s := stateAt P (batchStart P u.val) H.2
    let block := batchSeedBlock P u seeds
    memories P (stateAt P (batchEndTime P u)
      (batchEndTranscript P O r u seeds)) j =
      (1 - P.alpha j) • memories P s j +
        P.alpha j • upperResidualBatchMean O (highBand P j)
          (batchDecision P u H) (batchCenter P u H) block := by
  dsimp only
  let z : Fin P.T × (Fin (responseCount P) → Seed) := (r, seeds)
  let H := batchHistoryOfRun P O u z
  let s := stateAt P (batchStart P u.val) H.2
  let block := batchSeedBlock P u seeds
  let x := batchDecision P u H
  let ys := upperBatchResponses O x block
  have hzero : highSums P s = fun _ => 0 := by
    have h := actualBoundary_accumulators_zero P O u.val
      (Nat.le_of_lt u.isLt) z
    rw [boundaryTranscript_eq_batchHistory P O u z] at h
    exact h.2
  have hzeroj : highSums P s j = 0 := by
    rw [hzero]
  rw [actualBatch_state_eq_fold P O r u seeds,
    foldResponses_fullBatch_memory_eq_highEMA P u s ys j]
  simp only [hzeroj, zero_add]
  rfl

end

end HeavyTailedNoise.UpperK1
