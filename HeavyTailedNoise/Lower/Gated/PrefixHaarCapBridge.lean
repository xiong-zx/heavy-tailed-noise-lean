import HeavyTailedNoise.Lower.Gated.HaarCapBound
import HeavyTailedNoise.Lower.Gated.IdealFrozenCapEventInclusion

/-!
The manuscript's exact `prefixCapSet` is the same cap as the fixed-prefix
Haar bound when the next hidden direction is the next frame column. This is
an algebraic finite-sum reindexing, independent of orthonormality.
-/

namespace HeavyTailedNoise

noncomputable section

theorem frameResidual_framePrefix_succ_eq_selectedResidual
    {d T : ℕ} (U : Fin T → Point d) (j : Fin T) (y : Point d) :
    frameResidual
      (framePrefix (Nat.succ_le_iff.mpr j.isLt) U) y =
      frameOrthogonalResidual U
        (Finset.univ.filter (· ≤ j)) y := by
  let hj : j.val + 1 ≤ T := Nat.succ_le_iff.mpr j.isLt
  have hsum :
      (∑ i : Fin (j.val + 1),
        inner ℝ ((framePrefix hj U) i) y • (framePrefix hj U) i) =
      ∑ i ∈ Finset.univ.filter (· ≤ j),
        frameCoordinates U y i • U i := by
    classical
    apply Finset.sum_bij (fun i _ => i.castLE hj)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
      simpa only [Fin.val_castLE] using Nat.le_of_lt_succ i.isLt
    · intro i hi i' hi' heq
      exact (Fin.castLE_injective hj) heq
    · intro b hb
      have hbj : b.val ≤ j.val := (Finset.mem_filter.mp hb).2
      refine ⟨⟨b.val, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      rfl
    · intro i hi
      simp [framePrefix, frameCoordinates]
  unfold frameResidual frameOrthogonalResidual
  exact congrArg (fun z : Point d => y - z) hsum

lemma framePrefix_snoc_eq_succPrefix
    {d T : ℕ} (U : Fin T → Point d) (j : Fin T) :
    Fin.snoc (framePrefix (Nat.le_of_lt j.isLt) U) (U j) =
      framePrefix (Nat.succ_le_iff.mpr j.isLt) U := by
  funext i
  by_cases hi : i.val < j.val
  · have hcast : i = (⟨i.val, hi⟩ : Fin j.val).castSucc := Fin.ext rfl
    rw [hcast, Fin.snoc_castSucc]
    rfl
  · have hlast : i = Fin.last j.val := by
      apply Fin.ext
      simp only [Fin.val_last]
      have hle : i.val < j.val + 1 := i.isLt
      have hge : j.val ≤ i.val := Nat.le_of_not_gt hi
      omega
    rw [hlast, Fin.snoc_last]
    rfl

theorem mem_prefixCapSet_iff_fixedPrefixCap
    {d T : ℕ} (U : Fin T → Point d) (j : Fin T) (y : Point d) :
    y ∈ prefixCapSet U j ↔
      U j ∈ fixedPrefixCap
        (framePrefix (Nat.le_of_lt j.isLt) U) y := by
  rw [fixedPrefixCap_snoc_iff]
  rw [framePrefix_snoc_eq_succPrefix U j]
  rw [frameResidual_framePrefix_succ_eq_selectedResidual U j y]
  simp [prefixCapSet, frameCoordinates, real_inner_comm]

end

end HeavyTailedNoise
