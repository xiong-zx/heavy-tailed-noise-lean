import HeavyTailedNoise.Lower.Gated.PartialPrefixContrast
import HeavyTailedNoise.Lower.Gated.IdealStoppedHistory

/-!
A single fixed revealed prefix plus a proposed next direction determines the
exact truncated hard response. Unrevealed columns are filled with zero only
inside this deterministic prefix potential; the actual hard instance remains
the preselected full orthonormal frame.
-/

namespace HeavyTailedNoise

noncomputable section

def nextDirectionPrefixFrame
    {d T : ℕ} (j : Fin T) (v : Fin j.val → Point d)
    (θ : Point d) : Fin T → Point d :=
  idealPrefixExtension j (Fin.snoc v θ)

lemma framePrefix_nextDirectionPrefixFrame
    {d T : ℕ} (j : Fin T) (v : Fin j.val → Point d)
    (θ : Point d) :
    framePrefix (Nat.succ_le_iff.mpr j.isLt)
      (nextDirectionPrefixFrame j v θ) = Fin.snoc v θ := by
  funext i
  have hi : i.val < j.val + 1 := i.isLt
  simp [framePrefix, nextDirectionPrefixFrame,
    idealPrefixExtension, hi]

lemma nextDirectionPrefixFrame_eq_before
    {d T : ℕ} (j : Fin T) (v : Fin j.val → Point d)
    (θ θ' : Point d) (i : Fin T) (hi : i < j) :
    nextDirectionPrefixFrame j v θ i =
      nextDirectionPrefixFrame j v θ' i := by
  have hlt : i.val < j.val + 1 := by omega
  have hcast : (⟨i.val, hlt⟩ : Fin (j.val + 1)) =
      (⟨i.val, hi⟩ : Fin j.val).castSucc := Fin.ext rfl
  have hval (w : Point d) :
      nextDirectionPrefixFrame j v w i = v ⟨i.val, hi⟩ := by
    change (if h : i.val < j.val + 1 then
      (Fin.snoc v w : Fin (j.val + 1) → Point d) ⟨i.val, h⟩ else 0) =
        v ⟨i.val, hi⟩
    rw [dif_pos hlt, hcast, Fin.snoc_castSucc]
  rw [hval θ, hval θ']

lemma measurable_nextDirectionPrefixFrame
    {d T : ℕ} (j : Fin T) (v : Fin j.val → Point d) :
    Measurable (nextDirectionPrefixFrame j v) := by
  have hinput : Measurable (fun θ : Point d => (v, θ)) :=
    (measurable_const : Measurable (fun _ : Point d => v)).prodMk measurable_id
  have hsnoc : Measurable (fun θ : Point d =>
      (Fin.snoc v θ : Fin (j.val + 1) → Point d)) := by
    simpa only [Function.comp_def] using
      (measurable_frameSnoc d j.val).comp hinput
  exact (measurable_idealPrefixExtension j).comp hsnoc

end

end HeavyTailedNoise
