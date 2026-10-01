import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchEndState

/-!
The accumulator and memory projections of the one canonical runtime step.
These are readouts of `Algorithm.step`, not a second state transition.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem memories_step_runtime_nonterminal {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d)
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hnonterminal : (t - (1 + initialResponses P) + 1) % P.n ≠ 0) :
    memories P (step P t s y) = memories P s := by
  have ht0 : t ≠ 0 := by omega
  have hnotinit : ¬t < 1 + initialResponses P := Nat.not_lt.mpr hstart
  simp [step, ht0, hnotinit, hend, hnonterminal, memories]

theorem lowSum_step_runtime_nonterminal {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d)
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hnonterminal : (t - (1 + initialResponses P) + 1) % P.n ≠ 0) :
    lowSum P (step P t s y) =
      lowSum P s + lowBand P (y - center P s) := by
  have ht0 : t ≠ 0 := by omega
  have hnotinit : ¬t < 1 + initialResponses P := Nat.not_lt.mpr hstart
  simp [step, ht0, hnotinit, hend, hnonterminal,
    lowSum, accumulateResponse]

theorem highSums_step_runtime_nonterminal {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d) (j : Fin P.J)
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hnonterminal : (t - (1 + initialResponses P) + 1) % P.n ≠ 0) :
    highSums P (step P t s y) j =
      highSums P s j + highBand P j (y - center P s) := by
  have ht0 : t ≠ 0 := by omega
  have hnotinit : ¬t < 1 + initialResponses P := Nat.not_lt.mpr hstart
  simp [step, ht0, hnotinit, hend, hnonterminal,
    highSums, accumulateResponse]

theorem memories_step_runtime_terminal {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d)
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hterminal : (t - (1 + initialResponses P) + 1) % P.n = 0) :
    memories P (step P t s y) =
      updatedBands P s (accumulateResponse P s y).2 := by
  have ht0 : t ≠ 0 := by omega
  have hnotinit : ¬t < 1 + initialResponses P := Nat.not_lt.mpr hstart
  simp [step, ht0, hnotinit, hend, hterminal, memories]

end

end HeavyTailedNoise.UpperK1
