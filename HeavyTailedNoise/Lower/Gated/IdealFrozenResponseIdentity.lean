import HeavyTailedNoise.Lower.Gated.IdealFrozenQueryIdentity

/-!
On a response-bearing decision whose post-cap ideal stage remains the frozen
stage `j`, the frozen Gaussian mean and actual ideal response are identical.
-/

namespace HeavyTailedNoise

noncomputable section

lemma frozenStageHistoryMean_eq_idealResponseMean
    {d T : ℕ} (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    {H : Type*} [MeasurableSpace H]
    (q : ℕ → H → Point d) (u : ℕ) (h : H) :
    frozenStageHistoryMean U j q u h =
      idealResponseMean hT U j.val (q u h) := by
  have hidx : idealPrefixIndex hT j.val = j := by
    apply Fin.ext
    simp [idealPrefixIndex]
    omega
  simp [frozenStageHistoryMean, idealResponseMean, hidx]

theorem actualFrozenResponse_eq_idealResponse_on_stage
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (s : IdealPreResponseHistory d N)
    (hsStarted : s.started = true)
    (hsFirst : s.query = idealDecisionAt hT U A r ξ a s.time)
    (u : ℕ) (hn : s.time + u < N)
    (hstage : idealAfterAt hT U A r ξ a (s.time + u) = j.val)
    (tr : Transcript d N)
    (htr : tr = idealPadTranscript
      (idealStateAt hT U A r ξ a (s.time + u)).transcript) :
    frozenStageHistoryMean U j (actualFrozenQuery A r s) u tr +
        a • ξ ⟨s.time + u, hn⟩ =
      idealResponseMean hT U
        (idealAfterAt hT U A r ξ a (s.time + u))
        (idealDecisionAt hT U A r ξ a (s.time + u)) +
        a • idealNoiseAt ξ (s.time + u) := by
  rw [frozenStageHistoryMean_eq_idealResponseMean hT]
  rw [actualFrozenQuery_eq_idealDecisionAt_of_pad
    hT U A r ξ a s hsStarted hsFirst u hn tr htr]
  rw [hstage]
  simp [idealNoiseAt, hn]

end

end HeavyTailedNoise
