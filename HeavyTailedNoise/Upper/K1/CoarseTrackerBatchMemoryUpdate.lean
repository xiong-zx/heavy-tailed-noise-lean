import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchAccumulatorFull
import HeavyTailedNoise.Upper.K1.CoarseTrackerFullBatch

/-!
The memory field after one complete batch is the unique `updatedBands`
called by `Algorithm.step`. This state readout is the missing bridge from
the actual run to the finite EMA algebra; it introduces no new recurrence.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem foldResponses_terminal_memories {d : ℕ}
    (u : Fin P.T) (s : State d P.J) (k : ℕ)
    (hk : k + 1 = P.n) (ys : Fin (k + 1) → Point d) :
    let pre := foldResponses P (batchStart P u.val) s k
      (fun i : Fin k => ys i.castSucc)
    memories P (foldResponses P (batchStart P u.val) s (k + 1) ys) =
      updatedBands P pre (accumulateResponse P pre (ys (Fin.last k))).2 := by
  dsimp only
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
  rw [foldResponses_succ]
  exact memories_step_runtime_terminal P
    (batchStart P u.val + k) pre (ys (Fin.last k))
    hstart hend hterminal

theorem foldResponses_fullBatch_memories {d : ℕ}
    (u : Fin P.T) (s : State d P.J) (ys : Fin P.n → Point d) :
    let k := P.n - 1
    let pre := foldResponses P (batchStart P u.val) s k
      (fun i : Fin k => ys (prefixResponseIndex P i))
    memories P (foldResponses P (batchStart P u.val) s P.n ys) =
      updatedBands P pre
        (accumulateResponse P pre (ys (lastResponseIndex P))).2 := by
  dsimp only
  let k := P.n - 1
  have hk : k + 1 = P.n := by
    have hn := P.n_pos
    dsimp [k]
    omega
  let ys' : Fin (k + 1) → Point d := fun i => ys (i.cast hk)
  have hprefix : (fun i : Fin k => ys' i.castSucc) =
      (fun i : Fin k => ys (prefixResponseIndex P i)) := by
    funext i
    exact congrArg ys (Fin.ext rfl)
  have hlast : ys' (Fin.last k) = ys (lastResponseIndex P) :=
    congrArg ys (Fin.ext rfl)
  have hfold : foldResponses P (batchStart P u.val) s (k + 1) ys' =
      foldResponses P (batchStart P u.val) s P.n ys :=
    foldResponses_cast P (batchStart P u.val) s hk ys
  have hterm := foldResponses_terminal_memories P u s k hk ys'
  rw [hfold, hprefix, hlast] at hterm
  exact hterm

end

end HeavyTailedNoise.UpperK1
