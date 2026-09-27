import HeavyTailedNoise.Lower.Gated.ActualFrozenQueryStability

/-!
Every frozen query read from the final `m`-step transcript equals the query
chosen after its own prefix of fresh Gaussian responses. This makes the
frozen cap event a measurable event of the final transcript state.
-/

namespace HeavyTailedNoise

noncomputable section

theorem actualFrozenQuery_finalState_eq_prefixState
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ)
    (m u : ℕ) (hu : u ≤ m) (ζ : Fin m → Point d) :
    actualFrozenQuery A r s u
      (actualFrozenGaussianSeedState hT U j A r s a m ζ) =
    actualFrozenQuery A r s u
      (actualFrozenGaussianSeedState hT U j A r s a u
        (idealTailPrefix hu ζ)) := by
  induction m generalizing u with
  | zero =>
      have hu0 : u = 0 := by omega
      subst u
      rfl
  | succ m ih =>
      by_cases hum : u ≤ m
      · let ζprev : Fin m → Point d := fun i => ζ i.castSucc
        let old := actualFrozenGaussianSeedState hT U j A r s a m ζprev
        let y := frozenStageHistoryMean U j (actualFrozenQuery A r s) m old +
          a • ζ (Fin.last m)
        have hstep : actualFrozenGaussianSeedState hT U j A r s a (m + 1) ζ =
            actualFrozenUpdate A r s m (old, y) := rfl
        have hprefix : idealTailPrefix hum ζprev =
            idealTailPrefix hu ζ := by
          funext i
          rfl
        rw [hstep]
        rw [actualFrozenQuery_update_later A r s u m hum old y]
        have hih := ih u hum ζprev
        rw [hih, hprefix]
      · have hueq : u = m + 1 := by omega
        subst u
        have hfull : idealTailPrefix hu ζ = ζ := by
          funext i
          rfl
        rw [hfull]

end

end HeavyTailedNoise
