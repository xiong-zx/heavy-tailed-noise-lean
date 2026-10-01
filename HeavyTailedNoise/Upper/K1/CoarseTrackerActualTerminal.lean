import HeavyTailedNoise.Upper.K1.CoarseTrackerActualBatch

/-!
The actual batch-end point and center in the logged gradient-only run. This
combines the unique state fold with the already proved `Fin n` terminal
identity; no stochastic assumption is used in this pathwise statement.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualBatch_terminal_point_center {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (r u : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    let H := batchHistoryOfRun P O u (r, seeds)
    let block := batchSeedBlock P u seeds
    point P (stateAt P (batchEndTime P u)
      (batchEndTranscript P O r u seeds)) =
        batchDecision P u H - P.h • direction
          (batchEstimateOnHistory P O u H block) ∧
    center P (stateAt P (batchEndTime P u)
      (batchEndTranscript P O r u seeds)) =
        coarseCenter P (batchCenter P u H)
          (O.response (batchDecision P u H) (block ⟨0, P.n_pos⟩)) := by
  let H := batchHistoryOfRun P O u (r, seeds)
  let block := batchSeedBlock P u seeds
  let s := stateAt P (batchStart P u.val) H.2
  let ys := upperBatchResponses O (batchDecision P u H) block
  have hstate : stateAt P (batchEndTime P u)
      (batchEndTranscript P O r u seeds) =
      foldResponses P (batchStart P u.val) s P.n ys :=
    actualBatch_state_eq_fold P O r u seeds
  have hterminal := foldResponses_fullBatch_point_center P u s ys
  constructor
  · change point P (stateAt P (batchEndTime P u)
        (batchEndTranscript P O r u seeds)) =
        point P s - P.h • direction (batchEstimateFromResponses P u s ys)
    rw [hstate]
    exact hterminal.1
  · change center P (stateAt P (batchEndTime P u)
        (batchEndTranscript P O r u seeds)) =
        coarseCenter P (center P s) (ys ⟨0, P.n_pos⟩)
    rw [hstate]
    exact hterminal.2

end

end HeavyTailedNoise.UpperK1
