import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchMemoryUpdate

/-!
The complete-batch memory field obeys the exact high-band EMA formula of
the single `updatedBands` helper. The old accumulator remains visible for an
arbitrary starting state and will be discharged on actual batch boundaries.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem foldResponses_fullBatch_memory_eq_highEMA {d : ℕ}
    (u : Fin P.T) (s : State d P.J)
    (ys : Fin P.n → Point d) (j : Fin P.J) :
    memories P (foldResponses P (batchStart P u.val) s P.n ys) j =
      (1 - P.alpha j) • memories P s j +
        P.alpha j • ((P.n : ℝ)⁻¹ •
          (highSums P s j + ∑ i : Fin P.n,
            highBand P j (ys i - center P s))) := by
  let k := P.n - 1
  let pre := foldResponses P (batchStart P u.val) s k
    (fun i : Fin k => ys (prefixResponseIndex P i))
  have hk : k < P.n := by
    dsimp [k]
    have hn := P.n_pos
    omega
  have hmem := foldResponses_prefix_memories P u s k hk
    (fun i : Fin k => ys (prefixResponseIndex P i))
  have hhigh := accumulateResponse_full_high P u s ys j
  rw [foldResponses_fullBatch_memories P u s ys]
  change (1 - P.alpha j) • memories P pre j +
    P.alpha j • ((P.n : ℝ)⁻¹ •
      (accumulateResponse P pre (ys (lastResponseIndex P))).2 j) = _
  have hmemj : memories P pre j = memories P s j :=
    congrArg (fun m => m j) hmem
  rw [hmemj, hhigh]

end

end HeavyTailedNoise.UpperK1
