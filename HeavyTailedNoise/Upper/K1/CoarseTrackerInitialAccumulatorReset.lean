import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchAccumulatorReset
import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialState

/-!
The first runtime batch begins with empty low and high accumulators after
the single first response and the optional independent high-band setup.
This reads only the final initial step of the unique algorithm.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

private theorem stateAt_initial_accumulators_zero {d : ℕ}
    (m : ℕ) (hm : m = initialResponses P)
    (H : Transcript d (1 + m)) :
    lowSum P (stateAt P (1 + m) H) = 0 ∧
      highSums P (stateAt P (1 + m) H) = fun _ => 0 := by
  cases m with
  | zero =>
      simp [stateAt, step, initialState, lowSum, highSums]
  | succ k =>
      have ht0 : 1 + k ≠ 0 := by omega
      have hinit : 1 + k < 1 + initialResponses P := by omega
      have hlast : (1 + k) + 1 = 1 + initialResponses P := by omega
      simp only [Nat.add_succ]
      change lowSum P (step P (1 + k)
          (stateAt P (1 + k) (fun i => H i.castSucc))
          (H (Fin.last (1 + k))).2) = 0 ∧
        highSums P (step P (1 + k)
          (stateAt P (1 + k) (fun i => H i.castSucc))
          (H (Fin.last (1 + k))).2) = fun _ => 0
      simp [step, ht0, hinit, hlast, lowSum, highSums]

theorem stateAt_firstRuntime_accumulators_zero {d : ℕ}
    (H : Transcript d (batchStart P 0)) :
    lowSum P (stateAt P (batchStart P 0) H) = 0 ∧
      highSums P (stateAt P (batchStart P 0) H) = fun _ => 0 := by
  have htime : batchStart P 0 = 1 + initialResponses P := by
    simp [batchStart]
  let H' : Transcript d (1 + initialResponses P) :=
    fun i => H (i.cast htime.symm)
  have hstate : stateAt P (batchStart P 0) H =
      stateAt P (1 + initialResponses P) H' :=
    (stateAt_transcript_cast P htime H).symm
  rw [hstate]
  exact stateAt_initial_accumulators_zero P
    (initialResponses P) rfl H'

end

end HeavyTailedNoise.UpperK1
