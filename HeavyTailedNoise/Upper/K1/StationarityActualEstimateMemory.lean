import HeavyTailedNoise.Upper.K1.StationarityActualEstimatorFormula
import HeavyTailedNoise.Upper.K1.CoarseTrackerActualMemoryUpdate

/-!
The actual completed direction estimate uses the current low-band batch
mean and the memories written at the end of that same batch. This identifies
the formula in the manuscript's EMA recursion with the one logged algorithm.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualRuntimeEstimate_eq_lowBatch_add_postMemories
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) :
    let r : Fin P.T := ⟨0, P.T_pos⟩
    let H := batchHistoryOfRun P O u (r, seeds)
    let block := batchSeedBlock P u seeds
    actualRuntimeEstimate P O seeds u.val =
      batchCenter P u H +
        upperResidualBatchMean O (lowBand P)
          (batchDecision P u H) (batchCenter P u H) block +
        ∑ j : Fin P.J,
          memories P (stateAt P (batchEndTime P u)
            (batchEndTranscript P O r u seeds)) j := by
  dsimp only
  let r : Fin P.T := ⟨0, P.T_pos⟩
  let H := batchHistoryOfRun P O u (r, seeds)
  let block := batchSeedBlock P u seeds
  let s := stateAt P (batchStart P u.val) H.2
  have hformula := actualRuntimeEstimate_eq_lowBatch_add_highEMA P O seeds u
  change actualRuntimeEstimate P O seeds u.val =
    batchCenter P u H +
      upperResidualBatchMean O (lowBand P)
        (batchDecision P u H) (batchCenter P u H) block +
      ∑ j : Fin P.J,
        memories P (stateAt P (batchEndTime P u)
          (batchEndTranscript P O r u seeds)) j
  calc
    actualRuntimeEstimate P O seeds u.val =
        batchCenter P u H +
          upperResidualBatchMean O (lowBand P)
            (batchDecision P u H) (batchCenter P u H) block +
          ∑ j : Fin P.J,
            ((1 - P.alpha j) • memories P s j +
              P.alpha j • upperResidualBatchMean O (highBand P j)
                (batchDecision P u H) (batchCenter P u H) block) := hformula
    _ = batchCenter P u H +
          upperResidualBatchMean O (lowBand P)
            (batchDecision P u H) (batchCenter P u H) block +
          ∑ j : Fin P.J,
            memories P (stateAt P (batchEndTime P u)
              (batchEndTranscript P O r u seeds)) j := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            exact (actualBatch_memory_eq_highEMA P O r u seeds j).symm

end

end HeavyTailedNoise.UpperK1
