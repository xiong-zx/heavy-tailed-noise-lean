import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchFirst

/-!
The final response of one complete runtime batch. The point uses the unique
completed estimator from `Algorithm`, and the next center uses exactly the
first vector of this same batch. The arbitrary pre-batch state and all
returned vectors remain explicit.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem foldResponses_terminal_point_center {d : ℕ} (u : Fin P.T)
    (s : State d P.J) (k : ℕ) (hk : k + 1 = P.n)
    (ys : Fin (k + 1) → Point d) :
    let pre := foldResponses P (batchStart P u.val) s k
      (fun i : Fin k => ys i.castSucc)
    let last := ys (Fin.last k)
    let accumulated := accumulateResponse P pre last
    let updated := updatedBands P pre accumulated.2
    let estimate := completedBatchEstimate P pre accumulated.1 updated
    point P (foldResponses P (batchStart P u.val) s (k + 1) ys) =
      point P s - P.h • direction estimate ∧
    center P (foldResponses P (batchStart P u.val) s (k + 1) ys) =
      coarseCenter P (center P s) (ys ⟨0, by omega⟩) := by
  let pre := foldResponses P (batchStart P u.val) s k
    (fun i : Fin k => ys i.castSucc)
  let last := ys (Fin.last k)
  let accumulated := accumulateResponse P pre last
  let updated := updatedBands P pre accumulated.2
  let estimate := completedBatchEstimate P pre accumulated.1 updated
  have hklt : k < P.n := by omega
  have hpre := foldResponses_prefix_point_center P u s k hklt
    (fun i : Fin k => ys i.castSucc)
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
  have hfirst :
      (if (batchStart P u.val + k - (1 + initialResponses P)) % P.n = 0
       then last else firstResponse P pre) = ys ⟨0, by omega⟩ := by
    rw [batch_offset_mod P u k hklt]
    by_cases hk0 : k = 0
    · subst k
      rfl
    · rw [if_neg hk0]
      have hprev := foldResponses_prefix_firstResponse P u s k
        (Nat.pos_of_ne_zero hk0) hklt
        (fun i : Fin k => ys i.castSucc)
      simpa only [pre, Fin.castSucc_mk] using hprev
  have hstep := step_runtime_terminal_point_center P
    (batchStart P u.val + k) pre last hstart hend hterminal
  constructor
  · change point P (foldResponses P (batchStart P u.val) s (k + 1) ys) =
      point P s - P.h • direction estimate
    rw [foldResponses_succ]
    exact hstep.1.trans (by rw [hpre.1])
  · change center P (foldResponses P (batchStart P u.val) s (k + 1) ys) =
      coarseCenter P (center P s) (ys ⟨0, by omega⟩)
    rw [foldResponses_succ]
    calc
      _ = coarseCenter P (center P pre)
          (if (batchStart P u.val + k - (1 + initialResponses P)) % P.n = 0
           then last else firstResponse P pre) := hstep.2
      _ = coarseCenter P (center P s) (ys ⟨0, by omega⟩) := by
        rw [hpre.2, hfirst]

end

end HeavyTailedNoise.UpperK1
