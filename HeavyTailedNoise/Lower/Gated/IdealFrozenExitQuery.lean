import HeavyTailedNoise.Lower.Gated.IdealStageExitCap

/-!
For every positive stage, the query that exits it is selected from the same
complete pre-response transcript in the ideal and frozen continuations. The
claim includes the arbitrary response-free output at absolute time `N`.
-/

namespace HeavyTailedNoise

noncomputable section

theorem actualFrozenQuery_eq_ideal_exitQuery
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (k j : Fin T) (hjk : j.val = k.val + 1)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hnext : idealStageStart hT U A r ξ a (j.val + 1) ≤ N) :
    let τ := idealStageStart hT U A r ξ a (k.val + 1)
    let τnext := idealStageStart hT U A r ξ a (j.val + 1)
    let n := τnext - τ
    let s := idealStoppedPreHistory hT U k A r ξ a
    let hcap : τ + n ≤ N := by
      have hle := idealStageStart_mono_target hT U A r ξ a
        (k.val + 1) (j.val + 1) (by omega)
      omega
    let tr := actualFrozenGaussianSeedState hT U j A r s a n
      (idealNoiseSlice τ hcap ξ)
    actualFrozenQuery A r s n tr = idealDecisionAt hT U A r ξ a τnext := by
  dsimp only
  let τ := idealStageStart hT U A r ξ a (k.val + 1)
  let τnext := idealStageStart hT U A r ξ a (j.val + 1)
  have hle : τ ≤ τnext :=
    idealStageStart_mono_target hT U A r ξ a
      (k.val + 1) (j.val + 1) (by omega)
  have hstart : τ ≤ N := le_trans hle hnext
  let n := τnext - τ
  have hadd : τ + n = τnext := by omega
  have hcap : τ + n ≤ N := by omega
  have hbefore : τ + n ≤ τnext := by omega
  let s := idealStoppedPreHistory hT U k A r ξ a
  let tr := actualFrozenGaussianSeedState hT U j A r s a n
    (idealNoiseSlice τ hcap ξ)
  have hpath : tr = idealPadTranscript
      (idealStateAt hT U A r ξ a (τ + n)).transcript :=
    actualFrozenGaussianSeedState_eq_ideal_before_nextStart
      hT U k j hjk A r ξ a hstart n hcap hbefore
  have hs := idealStoppedPreHistory_eq_started_record
    hT U k A r ξ a hstart
  have hsStarted : s.started = true := by simp [s, hs]
  have hsTime : s.time = τ := by simp [s, hs, τ]
  have hsFirst : s.query = idealDecisionAt hT U A r ξ a s.time := by
    simp [s, hs]
  have hn : s.time + n ≤ N := by simpa only [hsTime] using hcap
  have htr : tr = idealPadTranscript
      (idealStateAt hT U A r ξ a (s.time + n)).transcript := by
    rw [hsTime]
    exact hpath
  have hquery := actualFrozenQuery_eq_idealDecisionAt_of_pad_le
    hT U A r ξ a s hsStarted hsFirst n hn tr htr
  have htime : s.time + n = τnext := by omega
  simpa only [htime] using hquery

theorem actualFrozenExitQuery_mem_prefixCap
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (k j : Fin T) (hjk : j.val = k.val + 1)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hnext : idealStageStart hT U A r ξ a (j.val + 1) ≤ N) :
    let τ := idealStageStart hT U A r ξ a (k.val + 1)
    let τnext := idealStageStart hT U A r ξ a (j.val + 1)
    let n := τnext - τ
    let s := idealStoppedPreHistory hT U k A r ξ a
    let hcap : τ + n ≤ N := by
      have hle := idealStageStart_mono_target hT U A r ξ a
        (k.val + 1) (j.val + 1) (by omega)
      omega
    softProjection (hardRadius T)
      (actualFrozenQuery A r s n
        (actualFrozenGaussianSeedState hT U j A r s a n
          (idealNoiseSlice τ hcap ξ))) ∈ prefixCapSet U j := by
  dsimp only
  have hquery := actualFrozenQuery_eq_ideal_exitQuery
    hT U k j hjk A r ξ a hnext
  rw [hquery]
  exact idealExitQuery_mem_prefixCap hT U j A r ξ a hnext

end

end HeavyTailedNoise
