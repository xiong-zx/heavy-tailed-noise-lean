import HeavyTailedNoise.Lower.Gated.IdealPaddedTranscript
import HeavyTailedNoise.Lower.Gated.ActualFrozenSeedLaw

/-!
From a genuine pre-response snapshot, the frozen continuation asks exactly
the original algorithm's next full-history question. The first query is the
already selected snapshot query; later queries use all returned pairs.
-/

namespace HeavyTailedNoise

noncomputable section

lemma actualFrozenPast_idealPadTranscript
    {d N : ℕ} (s : IdealPreResponseHistory d N)
    (u : ℕ) (hn : s.time + u < N)
    (tr : Transcript d (s.time + u)) :
    actualFrozenPast s u hn (idealPadTranscript tr) = tr := by
  classical
  funext i
  simp [actualFrozenPast, idealPadTranscript, i.isLt]

theorem actualFrozenQuery_eq_idealDecisionAt_of_pad
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (s : IdealPreResponseHistory d N)
    (hsStarted : s.started = true)
    (hsFirst : s.query = idealDecisionAt hT U A r ξ a s.time)
    (u : ℕ) (hn : s.time + u < N)
    (tr : Transcript d N)
    (htr : tr = idealPadTranscript
      (idealStateAt hT U A r ξ a (s.time + u)).transcript) :
    actualFrozenQuery A r s u tr =
      idealDecisionAt hT U A r ξ a (s.time + u) := by
  have ha : actualFrozenActive s u := ⟨hsStarted, hn⟩
  by_cases hu : u = 0
  · subst u
    rw [actualFrozenQuery_first A r s ha tr, hsFirst]
    simp
  · rw [actualFrozenQuery_later A r s u ha hu tr]
    have hrest : actualFrozenPast s u ha.2 tr =
        (idealStateAt hT U A r ξ a (s.time + u)).transcript := by
      rw [htr]
      exact actualFrozenPast_idealPadTranscript s u hn _
    rw [hrest]
    simp [idealDecisionAt, hn]

end

end HeavyTailedNoise
