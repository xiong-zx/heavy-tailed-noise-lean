import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchEnd

/-!
Finite response-block invariants for the unique algorithm state. The first
step proves that neither the query point nor the coarse center changes after
any proper prefix of a runtime batch. A later theorem identifies the stored
first response and the completed batch update.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem batch_offset (u : Fin P.T) (k : ℕ) :
    batchStart P u.val + k - (1 + initialResponses P) = u.val * P.n + k := by
  dsimp [batchStart]
  omega

theorem runtime_nonterminal_at_offset (u : Fin P.T) (k : ℕ)
    (hk : k + 1 < P.n) :
    1 + initialResponses P ≤ batchStart P u.val + k ∧
    batchStart P u.val + k < responseCount P ∧
    (batchStart P u.val + k - (1 + initialResponses P) + 1) % P.n ≠ 0 := by
  have hstart : 1 + initialResponses P ≤ batchStart P u.val + k := by
    dsimp [batchStart]
    omega
  have hk0 : k < P.n := by omega
  have hend : batchStart P u.val + k < responseCount P := by
    have h := (batchResponseIndex P u (⟨k, hk0⟩ : Fin P.n)).isLt
    simpa only [batchResponseIndex_val] using h
  have hmod : (u.val * P.n + k + 1) % P.n = k + 1 := by
    calc
      _ = (u.val * P.n + (k + 1)) % P.n := by rw [Nat.add_assoc]
      _ = (k + 1) % P.n := by simp [Nat.add_mod]
      _ = k + 1 := Nat.mod_eq_of_lt hk
  refine ⟨hstart, hend, ?_⟩
  rw [batch_offset P u k, hmod]
  omega

/-- Every proper prefix of a runtime batch retains the pre-batch query point
and coarse center, regardless of the returned vectors. -/
theorem foldResponses_prefix_point_center {d : ℕ} (u : Fin P.T)
    (s : State d P.J) (k : ℕ) (hk : k < P.n)
    (ys : Fin k → Point d) :
    point P (foldResponses P (batchStart P u.val) s k ys) = point P s ∧
      center P (foldResponses P (batchStart P u.val) s k ys) = center P s := by
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
      have hpre := ih hkprev (fun i => ys i.castSucc)
      obtain ⟨hstart, hend, hnonterminal⟩ := runtime_nonterminal_at_offset P u k hk
      constructor
      · calc
          point P (foldResponses P (batchStart P u.val) s (k + 1) ys) =
              point P (step P (batchStart P u.val + k) pre (ys (Fin.last k))) := rfl
          _ = point P pre := point_step_runtime_nonterminal P _ pre _
            hstart hend hnonterminal
          _ = point P s := hpre.1
      · calc
          center P (foldResponses P (batchStart P u.val) s (k + 1) ys) =
              center P (step P (batchStart P u.val + k) pre (ys (Fin.last k))) := rfl
          _ = center P pre := center_step_runtime_nonterminal P _ pre _
            hstart hend hnonterminal
          _ = center P s := hpre.2

end

end HeavyTailedNoise.UpperK1
