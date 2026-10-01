import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchEstimateExpanded

/-!
The single algorithm's terminal response clears both accumulators before
the next batch. This is a projection of `Algorithm.step` and holds for every
pre-terminal state, so no noise or moment hypothesis is involved.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem lowSum_step_runtime_terminal_zero {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d)
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hterminal : (t - (1 + initialResponses P) + 1) % P.n = 0) :
    lowSum P (step P t s y) = 0 := by
  have ht0 : t ≠ 0 := by omega
  have hnotinit : ¬t < 1 + initialResponses P := Nat.not_lt.mpr hstart
  simp [step, ht0, hnotinit, hend, hterminal, lowSum]

theorem highSums_step_runtime_terminal_zero {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d)
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hterminal : (t - (1 + initialResponses P) + 1) % P.n = 0) :
    highSums P (step P t s y) = fun _ => 0 := by
  have ht0 : t ≠ 0 := by omega
  have hnotinit : ¬t < 1 + initialResponses P := Nat.not_lt.mpr hstart
  simp [step, ht0, hnotinit, hend, hterminal, highSums]

end

end HeavyTailedNoise.UpperK1
