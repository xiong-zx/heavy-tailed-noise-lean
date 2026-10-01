import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchAccumulatorFull

/-!
The completed estimate of the one canonical algorithm, expressed in terms
of its pre-batch state and all returned vectors. The pre-batch accumulators
are kept explicit here; their zero value on real batch boundaries is a
separate path invariant, not an added assumption.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem batchEstimateFromResponses_eq_low_high_ema {d : ℕ}
    (u : Fin P.T) (s : State d P.J) (ys : Fin P.n → Point d) :
    batchEstimateFromResponses P u s ys =
      center P s +
        (P.n : ℝ)⁻¹ •
          (lowSum P s + ∑ i : Fin P.n,
            lowBand P (ys i - center P s)) +
        ∑ j : Fin P.J,
          ((1 - P.alpha j) • memories P s j +
            P.alpha j • ((P.n : ℝ)⁻¹ •
              (highSums P s j + ∑ i : Fin P.n,
                highBand P j (ys i - center P s)))) := by
  let k := P.n - 1
  let pre := foldResponses P (batchStart P u.val) s k
    (fun i : Fin k => ys (prefixResponseIndex P i))
  let accumulated := accumulateResponse P pre (ys (lastResponseIndex P))
  have hk : k < P.n := by
    dsimp [k]
    have hn := P.n_pos
    omega
  have hcenter := (foldResponses_prefix_point_center P u s k hk
    (fun i : Fin k => ys (prefixResponseIndex P i))).2
  have hmem := foldResponses_prefix_memories P u s k hk
    (fun i : Fin k => ys (prefixResponseIndex P i))
  have hlow := accumulateResponse_full_low P u s ys
  have hhigh (j : Fin P.J) := accumulateResponse_full_high P u s ys j
  change center P pre + (P.n : ℝ)⁻¹ • accumulated.1 +
      ∑ j : Fin P.J,
        ((1 - P.alpha j) • memories P pre j +
          P.alpha j • ((P.n : ℝ)⁻¹ • accumulated.2 j)) = _
  rw [hcenter, hlow]
  apply congrArg (fun v : Point d =>
    center P s + (P.n : ℝ)⁻¹ •
      (lowSum P s + ∑ i : Fin P.n,
        lowBand P (ys i - center P s)) + v)
  apply Finset.sum_congr rfl
  intro j hj
  have hmemj : memories P pre j = memories P s j :=
    congrArg (fun m => m j) hmem
  rw [hmemj, hhigh j]

end

end HeavyTailedNoise.UpperK1
