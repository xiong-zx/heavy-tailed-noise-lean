import HeavyTailedNoise.Lower.Gated.IdealFrozenExitQuery

/-!
The virtual stage-zero start at time zero needs its own exit-query argument:
the first query may start stage one immediately, and this query has no prior
response. Its frozen continuation still matches the arbitrary algorithm.
-/

namespace HeavyTailedNoise

noncomputable section

theorem actualFrozenZeroExitQuery_mem_prefixCap
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hnext : idealStageStart hT U A r ξ a 1 ≤ N) :
    let j₀ : Fin T := ⟨0, hT⟩
    let s₀ := idealPreHistoryAtTime hT U A r ξ a 0
    let n := idealStageStart hT U A r ξ a 1
    let hcap : s₀.time + n ≤ N := by
      simpa [s₀, idealPreHistoryAtTime] using hnext
    softProjection (hardRadius T)
      (actualFrozenQuery A r s₀ n
        (actualFrozenGaussianSeedState hT U j₀ A r s₀ a n
          (idealNoiseSlice s₀.time hcap ξ))) ∈ prefixCapSet U j₀ := by
  dsimp only
  let j₀ : Fin T := ⟨0, hT⟩
  let s₀ := idealPreHistoryAtTime hT U A r ξ a 0
  let n := idealStageStart hT U A r ξ a 1
  have hsStarted : s₀.started = true := by simp [s₀, idealPreHistoryAtTime]
  have hsTime : s₀.time = 0 := by simp [s₀, idealPreHistoryAtTime]
  have hsFirst : s₀.query = idealDecisionAt hT U A r ξ a s₀.time := by
    simp [s₀, idealPreHistoryAtTime]
  have hsTranscript : s₀.transcript = idealPadTranscript
      (idealStateAt hT U A r ξ a s₀.time).transcript := by
    simp [s₀, idealPreHistoryAtTime]
  have hcap : s₀.time + n ≤ N := by simpa [hsTime, n] using hnext
  have hstage : ∀ u < n,
      idealAfterAt hT U A r ξ a (s₀.time + u) = j₀.val := by
    intro u hu
    have hbefore : u < idealStageStart hT U A r ξ a 1 := by
      simpa [n] using hu
    have huN : u ≤ N := by omega
    simpa [hsTime, j₀] using
      (idealAfterAt_eq_zero_before_firstStart
        hT U A r ξ a u hbefore huN)
  let tr := actualFrozenGaussianSeedState hT U j₀ A r s₀ a n
    (idealNoiseSlice s₀.time hcap ξ)
  have htr : tr = idealPadTranscript
      (idealStateAt hT U A r ξ a (s₀.time + n)).transcript :=
    actualFrozenGaussianSeedState_eq_idealPadTranscript
      hT U j₀ A r ξ a s₀ hsStarted hsFirst hsTranscript
      n hcap hstage
  have hquery := actualFrozenQuery_eq_idealDecisionAt_of_pad_le
    hT U A r ξ a s₀ hsStarted hsFirst n hcap tr htr
  have hquery' : actualFrozenQuery A r s₀ n tr =
      idealDecisionAt hT U A r ξ a n := by
    simpa only [hsTime, zero_add] using hquery
  rw [hquery']
  exact idealExitQuery_mem_prefixCap hT U j₀ A r ξ a hnext

end

end HeavyTailedNoise
