import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchAccumulatorReset
import HeavyTailedNoise.Upper.K1.CoarseTrackerFullBatch

/-!
The last response of every complete runtime batch clears the low and high
accumulators. The result is valid for arbitrary starting state and returned
vectors and therefore also for the one actual logged batch.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem foldResponses_terminal_accumulators_zero {d : ℕ}
    (u : Fin P.T) (s : State d P.J) (k : ℕ)
    (hk : k + 1 = P.n) (ys : Fin (k + 1) → Point d) :
    lowSum P (foldResponses P (batchStart P u.val) s (k + 1) ys) = 0 ∧
      highSums P (foldResponses P (batchStart P u.val) s (k + 1) ys) =
        fun _ => 0 := by
  let pre := foldResponses P (batchStart P u.val) s k
    (fun i : Fin k => ys i.castSucc)
  have hklt : k < P.n := by omega
  have hstart : 1 + initialResponses P ≤ batchStart P u.val + k := by
    dsimp [batchStart]
    omega
  have hend : batchStart P u.val + k < responseCount P := by
    have h := (batchResponseIndex P u (⟨k, hklt⟩ : Fin P.n)).isLt
    simpa only [batchResponseIndex_val] using h
  have hterminal :
      (batchStart P u.val + k - (1 + initialResponses P) + 1) % P.n = 0 := by
    rw [batch_offset P u k]
    have hsum : u.val * P.n + k + 1 = (u.val + 1) * P.n := by
      rw [Nat.succ_mul]
      omega
    rw [hsum]
    simp
  constructor
  · rw [foldResponses_succ]
    exact lowSum_step_runtime_terminal_zero P
      (batchStart P u.val + k) pre (ys (Fin.last k))
      hstart hend hterminal
  · rw [foldResponses_succ]
    exact highSums_step_runtime_terminal_zero P
      (batchStart P u.val + k) pre (ys (Fin.last k))
      hstart hend hterminal

theorem foldResponses_fullBatch_accumulators_zero {d : ℕ}
    (u : Fin P.T) (s : State d P.J) (ys : Fin P.n → Point d) :
    lowSum P (foldResponses P (batchStart P u.val) s P.n ys) = 0 ∧
      highSums P (foldResponses P (batchStart P u.val) s P.n ys) =
        fun _ => 0 := by
  let k := P.n - 1
  have hk : k + 1 = P.n := by
    have hn := P.n_pos
    dsimp [k]
    omega
  let ys' : Fin (k + 1) → Point d := fun i => ys (i.cast hk)
  have hfold : foldResponses P (batchStart P u.val) s (k + 1) ys' =
      foldResponses P (batchStart P u.val) s P.n ys :=
    foldResponses_cast P (batchStart P u.val) s hk ys
  have hterm := foldResponses_terminal_accumulators_zero P u s k hk ys'
  constructor
  · rw [← hfold]
    exact hterm.1
  · rw [← hfold]
    exact hterm.2

end

end HeavyTailedNoise.UpperK1
