import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchState

/-!
The literal last-response branch of a runtime batch. All formulas here refer
to the single accumulator, EMA, estimator, and center functions called by
`Algorithm.step`; no second update is defined.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Before a runtime batch is complete, its first-response register records
the first vector of that batch and otherwise retains its earlier value. -/
theorem firstResponse_step_runtime_nonterminal {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d)
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hnonterminal : (t - (1 + initialResponses P) + 1) % P.n ≠ 0) :
    firstResponse P (step P t s y) =
      if (t - (1 + initialResponses P)) % P.n = 0 then y
      else firstResponse P s := by
  have ht0 : t ≠ 0 := by omega
  have hnotinit : ¬t < 1 + initialResponses P := Nat.not_lt.mpr hstart
  simp [step, ht0, hnotinit, hend, hnonterminal, firstResponse]

/-- On the last returned vector, the algorithm applies its unique completed
direction estimate and its unique coarse-center update. -/
theorem step_runtime_terminal_point_center {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d)
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hterminal : (t - (1 + initialResponses P) + 1) % P.n = 0) :
    point P (step P t s y) =
      point P s - P.h • direction
        (completedBatchEstimate P s (accumulateResponse P s y).1
          (updatedBands P s (accumulateResponse P s y).2)) ∧
    center P (step P t s y) =
      coarseCenter P (center P s)
        (if (t - (1 + initialResponses P)) % P.n = 0 then y
         else firstResponse P s) := by
  have ht0 : t ≠ 0 := by omega
  have hnotinit : ¬t < 1 + initialResponses P := Nat.not_lt.mpr hstart
  simp [step, ht0, hnotinit, hend, hterminal, point, center]

end

end HeavyTailedNoise.UpperK1
