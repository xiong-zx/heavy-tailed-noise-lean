import HeavyTailedNoise.Lower.Gated.NextDirectionFrozenKernel

/-!
The canonical revealed-prefix/next-direction frame has exactly the same
truncated response as the original full frame. This deterministic identity
is shared by the initial and positive-stage conditional-law assemblies.
-/

namespace HeavyTailedNoise

noncomputable section

theorem nextDirectionPrefixFrame_actual_agree
    {d T : ℕ} (U : Fin T → Point d) (j : Fin T) :
    ∀ i : Fin T, i ≤ j →
      nextDirectionPrefixFrame j
        (framePrefix (Nat.le_of_lt j.isLt) U) (U j) i = U i := by
  have hsnoc :
      Fin.snoc (framePrefix (Nat.le_of_lt j.isLt) U) (U j) =
        framePrefix (Nat.succ_le_iff.mpr j.isLt) U := by
    funext b
    refine Fin.lastCases ?_ (fun b => ?_) b
    · rw [Fin.snoc_last]
      rfl
    · rw [Fin.snoc_castSucc]
      rfl
  have hprefix := framePrefix_nextDirectionPrefixFrame j
    (framePrefix (Nat.le_of_lt j.isLt) U) (U j)
  rw [hsnoc] at hprefix
  intro i hi
  have hival : i.val < j.val + 1 := by omega
  have heq := congrFun hprefix ⟨i.val, hival⟩
  exact heq

theorem actualFrozenGaussianSeedState_nextDirectionPrefixFrame
    {d T N n : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ)
    (ξ : Fin n → Point d) :
    actualFrozenGaussianSeedState hT
      (nextDirectionPrefixFrame j
        (framePrefix (Nat.le_of_lt j.isLt) U) (U j))
      j A r s a n ξ =
        actualFrozenGaussianSeedState hT U j A r s a n ξ := by
  have hpot := prefixHardPotential_eq_of_agree j
    (nextDirectionPrefixFrame_actual_agree U j)
  have hmean :
      frozenStageHistoryMean
        (nextDirectionPrefixFrame j
          (framePrefix (Nat.le_of_lt j.isLt) U) (U j))
        j (actualFrozenQuery A r s) =
      frozenStageHistoryMean U j (actualFrozenQuery A r s) := by
    funext t tr
    simp only [frozenStageHistoryMean, hpot]
  unfold actualFrozenGaussianSeedState
  rw [hmean]

end

end HeavyTailedNoise
