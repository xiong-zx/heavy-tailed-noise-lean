import HeavyTailedNoise.Upper.K1.CoarseTrackerActualAccumulatorReset
import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialAccumulatorReset

/-!
Every actual runtime batch begins after a reset of the same algorithm's
low/high accumulators. The first boundary uses the unique initialization
step; later boundaries are preceding batch ends in the full logged path.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualBoundary_accumulators_zero {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (t : ℕ) (ht : t ≤ P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    lowSum P (stateAt P (batchStart P t)
      (boundaryTranscript P O t ht z)) = 0 ∧
    highSums P (stateAt P (batchStart P t)
      (boundaryTranscript P O t ht z)) = fun _ => 0 := by
  cases t with
  | zero =>
      exact stateAt_firstRuntime_accumulators_zero P
        (boundaryTranscript P O 0 ht z)
  | succ t =>
      have hlt : t < P.T := Nat.lt_of_succ_le ht
      let u : Fin P.T := ⟨t, hlt⟩
      have htime := batchStart_succ_eq_batchEndTime P u
      have htrans := boundaryTranscript_succ_eq_batchEndTranscript P O u z
      have hstate : stateAt P (batchStart P (t + 1))
          (boundaryTranscript P O (t + 1) ht z) =
          stateAt P (batchEndTime P u)
            (batchEndTranscript P O z.1 u z.2) := by
        rw [← stateAt_transcript_cast P htime
          (boundaryTranscript P O (u.val + 1) ht z)]
        rw [htrans]
      rw [hstate]
      exact actualBatch_end_accumulators_zero P O z.1 u z.2

end

end HeavyTailedNoise.UpperK1
