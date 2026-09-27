import HeavyTailedNoise.Lower.Gated.IdealFrozenBeforeNextStart

/-!
The query identity extends through the algorithm's final arbitrary output at
time `N`. That final point is selected from the complete `N`-response history
and receives no further oracle response.
-/

namespace HeavyTailedNoise

noncomputable section

lemma idealPadTranscript_full {d N : ℕ}
    (tr : Transcript d N) : idealPadTranscript tr = tr := by
  classical
  funext i
  simp [idealPadTranscript, i.isLt]

theorem actualFrozenQuery_eq_idealDecisionAt_of_pad_le
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (s : IdealPreResponseHistory d N)
    (hsStarted : s.started = true)
    (hsFirst : s.query = idealDecisionAt hT U A r ξ a s.time)
    (u : ℕ) (hn : s.time + u ≤ N)
    (tr : Transcript d N)
    (htr : tr = idealPadTranscript
      (idealStateAt hT U A r ξ a (s.time + u)).transcript) :
    actualFrozenQuery A r s u tr =
      idealDecisionAt hT U A r ξ a (s.time + u) := by
  by_cases hlt : s.time + u < N
  · exact actualFrozenQuery_eq_idealDecisionAt_of_pad
      hT U A r ξ a s hsStarted hsFirst u hlt tr htr
  · have hEq : s.time + u = N := by omega
    rw [actualFrozenQuery_at_cap A r s u (by omega) tr]
    rw [htr, hEq, idealPadTranscript_full]
    simp [idealDecisionAt]

end

end HeavyTailedNoise
