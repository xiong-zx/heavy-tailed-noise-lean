import HeavyTailedNoise.Upper.K1.CoarseTrackerActualBoundaryAccumulatorZero
import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchEstimateExpanded
import HeavyTailedNoise.Upper.K1.StationarityActualPath

/-!
The completed estimate on the genuine global seed path is exactly the
manuscript's shared-batch low-band mean plus the high-band EMA update. Every
band uses the same current response block. The pre-batch accumulators vanish
by the verified algorithm state, not by a new assumption.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualRuntimeEstimate_eq_lowBatch_add_highEMA
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) :
    let H := batchHistoryOfRun P O u
      ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
    let s := stateAt P (batchStart P u.val) H.2
    let block := batchSeedBlock P u seeds
    let x := batchDecision P u H
    let w := batchCenter P u H
    actualRuntimeEstimate P O seeds u.val =
      w + upperResidualBatchMean O (lowBand P) x w block +
        ∑ j : Fin P.J,
          ((1 - P.alpha j) • memories P s j +
            P.alpha j • upperResidualBatchMean O (highBand P j)
              x w block) := by
  dsimp only
  let z : Fin P.T × (Fin (responseCount P) → Seed) :=
    ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
  let H := batchHistoryOfRun P O u z
  let s := stateAt P (batchStart P u.val) H.2
  let block := batchSeedBlock P u seeds
  let x := batchDecision P u H
  let w := batchCenter P u H
  let ys := upperBatchResponses O x block
  have hzero : lowSum P s = 0 ∧ highSums P s = fun _ => 0 := by
    have h := actualBoundary_accumulators_zero P O u.val
      (Nat.le_of_lt u.isLt) z
    rw [boundaryTranscript_eq_batchHistory P O u z] at h
    exact h
  have hactual : actualRuntimeEstimate P O seeds u.val =
      batchEstimateFromResponses P u s ys := by
    simp only [actualRuntimeEstimate, dif_pos u.isLt]
    rfl
  rw [hactual, batchEstimateFromResponses_eq_low_high_ema P u s ys]
  have hzeroj (j : Fin P.J) : highSums P s j = 0 := by
    rw [hzero.2]
  simp_rw [hzeroj]
  simp only [hzero.1, zero_add]
  rfl

end

end HeavyTailedNoise.UpperK1
