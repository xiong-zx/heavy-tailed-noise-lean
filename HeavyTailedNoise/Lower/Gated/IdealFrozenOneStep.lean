import HeavyTailedNoise.Lower.Gated.IdealFrozenResponseIdentity

/-!
One exact response-bearing transcript step: while the ideal post-cap stage
remains `j`, the actual frozen Gaussian update equals the padded next ideal
state. The statement retains every prior query and returned vector.
-/

namespace HeavyTailedNoise

noncomputable section

lemma idealStateAt_transcript_succ_eq
    {d T N n : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (hn : n < N) :
    (idealStateAt hT U A r ξ a (n + 1)).transcript =
      Fin.snoc (idealStateAt hT U A r ξ a n).transcript
        (idealDecisionAt hT U A r ξ a n,
          idealResponseMean hT U (idealAfterAt hT U A r ξ a n)
            (idealDecisionAt hT U A r ξ a n) +
          a • idealNoiseAt ξ n) := by
  simp [idealStateAt, idealStepState, idealAfterAt,
    idealDecisionAt, hn]

theorem actualFrozenUpdate_eq_idealPadTranscript_succ
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
    actualFrozenUpdate A r s u
      (tr, frozenStageHistoryMean U j (actualFrozenQuery A r s) u tr +
        a • ξ ⟨s.time + u, hn⟩) =
      idealPadTranscript
        (idealStateAt hT U A r ξ a (s.time + u + 1)).transcript := by
  have ha : actualFrozenActive s u := ⟨hsStarted, hn⟩
  have hquery := actualFrozenQuery_eq_idealDecisionAt_of_pad
    hT U A r ξ a s hsStarted hsFirst u hn tr htr
  have hresponse := actualFrozenResponse_eq_idealResponse_on_stage
    hT U j A r ξ a s hsStarted hsFirst u hn hstage tr htr
  let n := s.time + u
  let old := (idealStateAt hT U A r ξ a n).transcript
  let v : Point d × Point d :=
    (idealDecisionAt hT U A r ξ a n,
      idealResponseMean hT U (idealAfterAt hT U A r ξ a n)
        (idealDecisionAt hT U A r ξ a n) + a • idealNoiseAt ξ n)
  calc
    actualFrozenUpdate A r s u
        (tr, frozenStageHistoryMean U j (actualFrozenQuery A r s) u tr +
          a • ξ ⟨s.time + u, hn⟩) =
      Function.update tr ⟨n, hn⟩
        (actualFrozenQuery A r s u tr,
          frozenStageHistoryMean U j (actualFrozenQuery A r s) u tr +
            a • ξ ⟨s.time + u, hn⟩) := by
              simp [actualFrozenUpdate, ha, n]
    _ = Function.update (idealPadTranscript old) ⟨n, hn⟩ v := by
      rw [hresponse, hquery, htr]
    _ = idealPadTranscript (Fin.snoc old v) :=
      (idealPadTranscript_snoc_eq_update hn old v).symm
    _ = idealPadTranscript
        (idealStateAt hT U A r ξ a (s.time + u + 1)).transcript := by
      rw [idealStateAt_transcript_succ_eq hT U A r ξ a hn]

end

end HeavyTailedNoise
