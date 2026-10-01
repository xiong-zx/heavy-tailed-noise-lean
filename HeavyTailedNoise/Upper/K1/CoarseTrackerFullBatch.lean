import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchEstimate

/-!
The terminal state theorem in the literal `Fin P.n` batch interface used by
the oracle law. Natural-number index equality only transports the same block;
the estimator and state update remain the unique Algorithm definitions.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem foldResponses_cast {d : ℕ} (start : ℕ) (s : State d P.J)
    {m n : ℕ} (h : m = n) (ys : Fin n → Point d) :
    foldResponses P start s m (fun i => ys (i.cast h)) =
      foldResponses P start s n ys := by
  cases h
  rfl

/-- A complete `Fin P.n` response block changes the point through the
single completed estimator and changes the center using its first vector. -/
theorem foldResponses_fullBatch_point_center {d : ℕ} (u : Fin P.T)
    (s : State d P.J) (ys : Fin P.n → Point d) :
    point P (foldResponses P (batchStart P u.val) s P.n ys) =
      point P s - P.h • direction (batchEstimateFromResponses P u s ys) ∧
    center P (foldResponses P (batchStart P u.val) s P.n ys) =
      coarseCenter P (center P s) (ys ⟨0, P.n_pos⟩) := by
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
  have hfirst : ys' ⟨0, Nat.zero_lt_succ k⟩ = ys ⟨0, P.n_pos⟩ :=
    congrArg ys (Fin.ext rfl)
  have hfold : foldResponses P (batchStart P u.val) s (k + 1) ys' =
      foldResponses P (batchStart P u.val) s P.n ys :=
    foldResponses_cast P (batchStart P u.val) s hk ys
  have hterm := foldResponses_terminal_point_center P u s k hk ys'
  constructor
  · have hpoint := hterm.1
    rw [hfold] at hpoint
    rw [hprefix, hlast] at hpoint
    simpa only [batchEstimateFromResponses, k] using hpoint
  · have hcenter := hterm.2
    rw [hfold] at hcenter
    simpa only [hfirst] using hcenter

end

end HeavyTailedNoise.UpperK1
