import HeavyTailedNoise.Lower.Gated.FrozenHaarReferenceCap

/-!
A later frozen response can never change a previously selected full-history
query. At or beyond the hard response cap the update is the identity, so this
also covers the arbitrary response-free output decision.
-/

namespace HeavyTailedNoise

noncomputable section

theorem actualFrozenQuery_update_later
    {d N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N)
    (u t : ℕ) (hu : u ≤ t)
    (tr : Transcript d N) (y : Point d) :
    actualFrozenQuery A r s u
      (actualFrozenUpdate A r s t (tr, y)) =
      actualFrozenQuery A r s u tr := by
  by_cases hat : actualFrozenActive s t
  · have htt : s.time + t < N := hat.2
    have hnu : s.time + u < N := by omega
    have hau : actualFrozenActive s u := ⟨hat.1, hnu⟩
    by_cases hzero : u = 0
    · subst u
      rw [actualFrozenQuery_first A r s hau,
        actualFrozenQuery_first A r s hau]
    · rw [actualFrozenQuery_later A r s u hau hzero,
        actualFrozenQuery_later A r s u hau hzero]
      have hpast : actualFrozenPast s u hau.2
          (actualFrozenUpdate A r s t (tr, y)) =
          actualFrozenPast s u hau.2 tr := by
        funext i
        have hne : (⟨i.val, lt_trans i.isLt hau.2⟩ : Fin N) ≠
            (⟨s.time + t, hat.2⟩ : Fin N) := by
          intro heq
          have hv := congrArg Fin.val heq
          simp only [Fin.val_mk] at hv
          omega
        simp [actualFrozenPast, actualFrozenUpdate, hat,
          Function.update, hne]
      rw [hpast]
  · simp [actualFrozenUpdate, hat]

end

end HeavyTailedNoise
