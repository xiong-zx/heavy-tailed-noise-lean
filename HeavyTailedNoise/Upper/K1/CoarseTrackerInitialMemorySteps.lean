import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialState

/-!
Initial high-band samples are accumulated at the first response's frozen
center and written once into the sole algorithm memory field. The optional
initialization batch is handled separately from the runtime shared batches.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem highSums_step_initial_nonterminal {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d) (j : Fin P.J)
    (ht0 : t ≠ 0) (hinit : t < 1 + initialResponses P)
    (hlast : t + 1 ≠ 1 + initialResponses P) :
    highSums P (step P t s y) j =
      highSums P s j + highBand P j (y - center P s) := by
  simp [step, ht0, hinit, hlast, highSums]

theorem memories_step_initial_terminal {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d) (j : Fin P.J)
    (ht0 : t ≠ 0) (hinit : t < 1 + initialResponses P)
    (hlast : t + 1 = 1 + initialResponses P) :
    memories P (step P t s y) j =
      (initialResponses P : ℝ)⁻¹ •
        (highSums P s j + highBand P j (y - center P s)) := by
  simp [step, ht0, hinit, hlast, memories]

theorem foldResponses_initial_prefix_highSums {d : ℕ}
    (s : State d P.J) (k : ℕ) (hk : k < initialResponses P)
    (ys : Fin k → Point d) (j : Fin P.J) :
    highSums P (foldResponses P 1 s k ys) j =
      highSums P s j + ∑ i : Fin k,
        highBand P j (ys i - center P s) := by
  revert hk ys
  induction k with
  | zero =>
      intro hk ys
      simp [foldResponses]
  | succ k ih =>
      intro hk ys
      have hkprev : k < initialResponses P := by omega
      let pre := foldResponses P 1 s k (fun i => ys i.castSucc)
      have hprev := ih hkprev (fun i => ys i.castSucc)
      have hcenter := (foldResponses_initial_point_center P s k
        (Nat.le_of_lt hkprev) (fun i => ys i.castSucc)).2
      have ht0 : 1 + k ≠ 0 := by omega
      have hinit : 1 + k < 1 + initialResponses P := by omega
      have hlast : (1 + k) + 1 ≠ 1 + initialResponses P := by omega
      calc
        highSums P (foldResponses P 1 s (k + 1) ys) j =
            highSums P pre j +
              highBand P j (ys (Fin.last k) - center P pre) := by
                rw [foldResponses_succ]
                exact highSums_step_initial_nonterminal P (1 + k)
                  pre (ys (Fin.last k)) j ht0 hinit hlast
        _ = (highSums P s j + ∑ i : Fin k,
              highBand P j (ys i.castSucc - center P s)) +
              highBand P j (ys (Fin.last k) - center P s) := by
                rw [hprev, hcenter]
        _ = highSums P s j + ∑ i : Fin (k + 1),
              highBand P j (ys i - center P s) := by
                rw [Fin.sum_univ_castSucc]
                abel

end

end HeavyTailedNoise.UpperK1
