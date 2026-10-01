import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialMemoryTerminal
import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchState

/-!
The memory at the first runtime state comes from precisely the optional
initialization response block. With no such block it is zero; with a block
it is its empirical high-band mean at the already frozen first-response
center. These are state readouts of the unique logged algorithm.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem stateAt_one_memories_zero {d : ℕ} (H : Transcript d 1) :
    memories P (stateAt P 1 H) = fun _ => 0 := by
  funext j
  simp [stateAt, step, initialState, memories]

theorem stateAt_initial_memory_of_pos {d : ℕ}
    (hpos : 0 < initialResponses P)
    (H : Transcript d (1 + initialResponses P))
    (j : Fin P.J) :
    memories P (stateAt P (1 + initialResponses P) H) j =
      (initialResponses P : ℝ)⁻¹ •
        ∑ i : Fin (initialResponses P),
          highBand P j
            ((transcriptBlockResponses 1 (initialResponses P) H) i -
              center P (stateAt P 1
                (transcriptPrefix 1 (initialResponses P) H))) := by
  let s := stateAt P 1 (transcriptPrefix 1 (initialResponses P) H)
  let ys := transcriptBlockResponses 1 (initialResponses P) H
  have hfold := stateAt_eq_foldResponses P 1 (initialResponses P) H
  have hmem0 : highSums P s j = 0 := by
    simp [s, stateAt, step, initialState, highSums]
  rw [hfold]
  rw [foldResponses_initial_memory_of_pos P s
    (initialResponses P) rfl hpos ys j]
  rw [hmem0, zero_add]

end

end HeavyTailedNoise.UpperK1
