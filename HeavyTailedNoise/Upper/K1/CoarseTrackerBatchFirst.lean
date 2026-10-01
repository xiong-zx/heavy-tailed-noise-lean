import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchEndState

/-!
The first returned vector of a runtime batch remains in the algorithm's
first-response register until the final response consumes it. This is a
deterministic invariant for the unique `Algorithm.step` fold.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem batch_offset_mod (u : Fin P.T) (k : ℕ) (hk : k < P.n) :
    (batchStart P u.val + k - (1 + initialResponses P)) % P.n = k := by
  rw [batch_offset P u k]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hk]

/-- At any nonempty proper prefix of a runtime batch, the state register is
exactly the first returned vector of that same batch. -/
theorem foldResponses_prefix_firstResponse {d : ℕ} (u : Fin P.T)
    (s : State d P.J) (k : ℕ) (hkpos : 0 < k) (hk : k < P.n)
    (ys : Fin k → Point d) :
    firstResponse P (foldResponses P (batchStart P u.val) s k ys) =
      ys ⟨0, hkpos⟩ := by
  revert hkpos hk ys
  induction k with
  | zero =>
      intro hkpos
      omega
  | succ k ih =>
      intro hkpos hk ys
      let pre := foldResponses P (batchStart P u.val) s k
        (fun i => ys i.castSucc)
      obtain ⟨hstart, hend, hnonterminal⟩ :=
        runtime_nonterminal_at_offset P u k hk
      rw [foldResponses_succ]
      rw [firstResponse_step_runtime_nonterminal P
        (batchStart P u.val + k) pre (ys (Fin.last k))
        hstart hend hnonterminal]
      rw [batch_offset_mod P u k (by omega)]
      by_cases hk0 : k = 0
      · subst k
        rfl
      · rw [if_neg hk0]
        have hprev := ih (Nat.pos_of_ne_zero hk0) (by omega)
          (fun i : Fin k => ys i.castSucc)
        simpa only [Fin.castSucc_mk] using hprev

end

end HeavyTailedNoise.UpperK1
