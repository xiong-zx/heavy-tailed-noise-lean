import HeavyTailedNoise.Lower.Gated.IdealFrozenTailPrefix

/-!
Every actual short stage transition forces a cap hit among the frozen
continuation's first `m+1` response-free query decisions. The exiting query
is included before its response; the final algorithm output has no response.
-/

namespace HeavyTailedNoise

noncomputable section

def frozenPrefixCapHitWithin
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ)
    (ζ : Fin m → Point d) : Prop :=
  ∃ u : ℕ, ∃ hu : u ≤ m,
    softProjection (hardRadius T)
      (actualFrozenQuery A r s u
        (actualFrozenGaussianSeedState hT U j A r s a u
          (idealTailPrefix hu ζ))) ∈ prefixCapSet U j

theorem positiveShortStage_implies_frozenCapHit
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (k j : Fin T) (hjk : j.val = k.val + 1)
    (A : RandomAlgorithm d N Private) (r : Private)
    (Ξ : Fin (N + m) → Point d) (a : ℝ)
    (hnext : idealStageStart hT U A r
      (idealExtendedNoiseTake Ξ) a (j.val + 1) ≤ N)
    (hshort : idealStageStart hT U A r
        (idealExtendedNoiseTake Ξ) a (j.val + 1) -
      idealStageStart hT U A r
        (idealExtendedNoiseTake Ξ) a (k.val + 1) ≤ m) :
    frozenPrefixCapHitWithin hT U j A r
      (idealStoppedPreHistory hT U k A r
        (idealExtendedNoiseTake Ξ) a) a
      (idealRandomStartTail hT U k A r a Ξ) := by
  let ξ := idealExtendedNoiseTake Ξ
  let τ := idealStageStart hT U A r ξ a (k.val + 1)
  let τnext := idealStageStart hT U A r ξ a (j.val + 1)
  let n := τnext - τ
  have hle : τ ≤ τnext :=
    idealStageStart_mono_target hT U A r ξ a
      (k.val + 1) (j.val + 1) (by omega)
  have hstart : τ ≤ N := le_trans hle hnext
  have hcap : τ + n ≤ N := by
    have hadd : τ + n = τnext := Nat.add_sub_of_le hle
    rw [hadd]
    exact hnext
  have hprefix := idealRandomStartTail_prefix_eq_originalNoiseSlice
    hT U k A r Ξ a hstart hshort hcap
  change ∃ u : ℕ, ∃ hu : u ≤ m,
    softProjection (hardRadius T)
      (actualFrozenQuery A r
        (idealStoppedPreHistory hT U k A r ξ a) u
        (actualFrozenGaussianSeedState hT U j A r
          (idealStoppedPreHistory hT U k A r ξ a) a u
          (idealTailPrefix hu
            (idealRandomStartTail hT U k A r a Ξ)))) ∈
      prefixCapSet U j
  refine ⟨n, hshort, ?_⟩
  rw [hprefix]
  exact actualFrozenExitQuery_mem_prefixCap
    hT U k j hjk A r ξ a hnext

theorem zeroShortStage_implies_frozenCapHit
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (Ξ : Fin (N + m) → Point d) (a : ℝ)
    (hnext : idealStageStart hT U A r
      (idealExtendedNoiseTake Ξ) a 1 ≤ N)
    (hshort : idealStageStart hT U A r
      (idealExtendedNoiseTake Ξ) a 1 ≤ m) :
    frozenPrefixCapHitWithin hT U ⟨0, hT⟩ A r
      (idealPreHistoryAtTime hT U A r (idealExtendedNoiseTake Ξ) a 0) a
      (idealExtendedNoiseTail 0 (Nat.zero_le N) Ξ) := by
  let ξ := idealExtendedNoiseTake Ξ
  let n := idealStageStart hT U A r ξ a 1
  have hcap : 0 + n ≤ N := by simpa [n] using hnext
  have hprefix : idealTailPrefix hshort
      (idealExtendedNoiseTail 0 (Nat.zero_le N) Ξ) =
      idealNoiseSlice 0 hcap ξ := by
    funext i
    rfl
  change ∃ u : ℕ, ∃ hu : u ≤ m,
    softProjection (hardRadius T)
      (actualFrozenQuery A r
        (idealPreHistoryAtTime hT U A r ξ a 0) u
        (actualFrozenGaussianSeedState hT U ⟨0, hT⟩ A r
          (idealPreHistoryAtTime hT U A r ξ a 0) a u
          (idealTailPrefix hu
            (idealExtendedNoiseTail 0 (Nat.zero_le N) Ξ)))) ∈
      prefixCapSet U ⟨0, hT⟩
  refine ⟨n, hshort, ?_⟩
  rw [hprefix]
  exact actualFrozenZeroExitQuery_mem_prefixCap
    hT U A r ξ a hnext

end

end HeavyTailedNoise
