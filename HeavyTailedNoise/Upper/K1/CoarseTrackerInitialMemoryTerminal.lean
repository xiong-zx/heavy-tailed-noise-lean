import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialMemorySteps

/-!
If an optional initial high-band batch is present, its last response writes
the one empirical high-band mean into the canonical memory field. The first
raw response fixes the center but is not reused as an initialization sample.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem foldResponses_initial_memory_of_pos {d : ℕ}
    (s : State d P.J) (m : ℕ)
    (hm : m = initialResponses P) (hpos : 0 < m)
    (ys : Fin m → Point d) (j : Fin P.J) :
    memories P (foldResponses P 1 s m ys) j =
      (initialResponses P : ℝ)⁻¹ •
        (highSums P s j + ∑ i : Fin m,
          highBand P j (ys i - center P s)) := by
  cases m with
  | zero =>
      omega
  | succ k =>
      let pre := foldResponses P 1 s k (fun i => ys i.castSucc)
      have hk : k < initialResponses P := by omega
      have hprev := foldResponses_initial_prefix_highSums P s k hk
        (fun i => ys i.castSucc) j
      have hcenter := (foldResponses_initial_point_center P s k
        (Nat.le_of_lt hk) (fun i => ys i.castSucc)).2
      have ht0 : 1 + k ≠ 0 := by omega
      have hinit : 1 + k < 1 + initialResponses P := by omega
      have hlast : (1 + k) + 1 = 1 + initialResponses P := by omega
      rw [foldResponses_succ]
      rw [memories_step_initial_terminal P (1 + k) pre
        (ys (Fin.last k)) j ht0 hinit hlast]
      rw [hprev, hcenter, Fin.sum_univ_castSucc]
      congr 1
      abel

end

end HeavyTailedNoise.UpperK1
