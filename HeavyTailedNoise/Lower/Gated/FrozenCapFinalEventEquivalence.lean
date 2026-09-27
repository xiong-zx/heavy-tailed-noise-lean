import HeavyTailedNoise.Lower.Gated.FrozenFinalQueryStability

/-!
The pathwise frozen cap event defined from each intermediate state is exactly
the measurable cap event read from the final `m`-step transcript. The same
query list can therefore be used in the Gaussian KL and Haar reference laws.
-/

namespace HeavyTailedNoise

noncomputable section

theorem frozenPrefixCapHitWithin_iff_finalCapHit
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ)
    (ζ : Fin m → Point d) :
    frozenPrefixCapHitWithin hT U j A r s a ζ ↔
      actualFrozenGaussianSeedState hT U j A r s a m ζ ∈
        frozenFinalCapHit (m := m) hT U j A r s := by
  constructor
  · rintro ⟨u, hu, hcap⟩
    let i : Fin (m + 1) := ⟨u, by omega⟩
    change ∃ i : Fin (m + 1),
      frozenFinalQueryList (m := m) hT A r s
        (actualFrozenGaussianSeedState hT U j A r s a m ζ) i ∈
          prefixCapSet U j
    refine ⟨i, ?_⟩
    change softProjection (hardRadius T)
      (actualFrozenQuery A r s u
        (actualFrozenGaussianSeedState hT U j A r s a m ζ)) ∈
          prefixCapSet U j
    rw [actualFrozenQuery_finalState_eq_prefixState
      hT U j A r s a m u hu ζ]
    exact hcap
  · rintro ⟨i, hcap⟩
    have hu : i.val ≤ m := by omega
    refine ⟨i.val, hu, ?_⟩
    change softProjection (hardRadius T)
      (actualFrozenQuery A r s i.val
        (actualFrozenGaussianSeedState hT U j A r s a m ζ)) ∈
          prefixCapSet U j at hcap
    rw [actualFrozenQuery_finalState_eq_prefixState
      hT U j A r s a m i.val hu ζ] at hcap
    exact hcap

end

end HeavyTailedNoise
