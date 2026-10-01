import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchAccumulators

/-!
The unique runtime state's low and high accumulators after a proper batch
prefix are precisely finite sums of returned vectors at the frozen pre-batch
center. No fresh seed is introduced by these pathwise identities.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem foldResponses_prefix_memories {d : ℕ} (u : Fin P.T)
    (s : State d P.J) (k : ℕ) (hk : k < P.n)
    (ys : Fin k → Point d) :
    memories P (foldResponses P (batchStart P u.val) s k ys) =
      memories P s := by
  revert hk ys
  induction k with
  | zero =>
      intro hk ys
      rfl
  | succ k ih =>
      intro hk ys
      have hkprev : k < P.n := by omega
      let pre := foldResponses P (batchStart P u.val) s k
        (fun i => ys i.castSucc)
      have hprev := ih hkprev (fun i => ys i.castSucc)
      obtain ⟨hstart, hend, hnonterminal⟩ :=
        runtime_nonterminal_at_offset P u k hk
      rw [foldResponses_succ]
      exact (memories_step_runtime_nonterminal P
        (batchStart P u.val + k) pre (ys (Fin.last k))
        hstart hend hnonterminal).trans hprev

theorem foldResponses_prefix_lowSum {d : ℕ} (u : Fin P.T)
    (s : State d P.J) (k : ℕ) (hk : k < P.n)
    (ys : Fin k → Point d) :
    lowSum P (foldResponses P (batchStart P u.val) s k ys) =
      lowSum P s + ∑ i : Fin k,
        lowBand P (ys i - center P s) := by
  revert hk ys
  induction k with
  | zero =>
      intro hk ys
      simp [foldResponses]
  | succ k ih =>
      intro hk ys
      have hkprev : k < P.n := by omega
      let pre := foldResponses P (batchStart P u.val) s k
        (fun i => ys i.castSucc)
      have hprev := ih hkprev (fun i => ys i.castSucc)
      have hcenter := (foldResponses_prefix_point_center P u s k hkprev
        (fun i => ys i.castSucc)).2
      obtain ⟨hstart, hend, hnonterminal⟩ :=
        runtime_nonterminal_at_offset P u k hk
      calc
        lowSum P (foldResponses P (batchStart P u.val) s (k + 1) ys) =
            lowSum P pre +
              lowBand P (ys (Fin.last k) - center P pre) := by
                rw [foldResponses_succ]
                exact lowSum_step_runtime_nonterminal P
                  (batchStart P u.val + k) pre (ys (Fin.last k))
                  hstart hend hnonterminal
        _ = (lowSum P s + ∑ i : Fin k,
              lowBand P (ys i.castSucc - center P s)) +
              lowBand P (ys (Fin.last k) - center P s) := by
                rw [hprev, hcenter]
        _ = lowSum P s + ∑ i : Fin (k + 1),
              lowBand P (ys i - center P s) := by
                rw [Fin.sum_univ_castSucc]
                abel

theorem foldResponses_prefix_highSums {d : ℕ} (u : Fin P.T)
    (s : State d P.J) (k : ℕ) (hk : k < P.n)
    (ys : Fin k → Point d) (j : Fin P.J) :
    highSums P (foldResponses P (batchStart P u.val) s k ys) j =
      highSums P s j + ∑ i : Fin k,
        highBand P j (ys i - center P s) := by
  revert hk ys
  induction k with
  | zero =>
      intro hk ys
      simp [foldResponses]
  | succ k ih =>
      intro hk ys
      have hkprev : k < P.n := by omega
      let pre := foldResponses P (batchStart P u.val) s k
        (fun i => ys i.castSucc)
      have hprev := ih hkprev (fun i => ys i.castSucc)
      have hcenter := (foldResponses_prefix_point_center P u s k hkprev
        (fun i => ys i.castSucc)).2
      obtain ⟨hstart, hend, hnonterminal⟩ :=
        runtime_nonterminal_at_offset P u k hk
      calc
        highSums P (foldResponses P (batchStart P u.val) s (k + 1) ys) j =
            highSums P pre j +
              highBand P j (ys (Fin.last k) - center P pre) := by
                rw [foldResponses_succ]
                exact highSums_step_runtime_nonterminal P
                  (batchStart P u.val + k) pre (ys (Fin.last k)) j
                  hstart hend hnonterminal
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
