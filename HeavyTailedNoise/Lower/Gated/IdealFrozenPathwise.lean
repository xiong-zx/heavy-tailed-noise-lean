import HeavyTailedNoise.Lower.Gated.IdealFrozenOneStep

/-!
Pathwise equality of the full frozen Gaussian transcript and the actual ideal
transcript until the ideal post-cap stage leaves the frozen stage. The
algorithm's arbitrary complete history is preserved at every step.
-/

namespace HeavyTailedNoise

noncomputable section

def idealNoiseSlice {d N n : ℕ}
    (t : ℕ) (hcap : t + n ≤ N)
    (ξ : Fin N → Point d) : Fin n → Point d :=
  fun i => ξ ⟨t + i.val, by omega⟩

theorem actualFrozenGaussianSeedState_eq_idealPadTranscript
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (s : IdealPreResponseHistory d N)
    (hsStarted : s.started = true)
    (hsFirst : s.query = idealDecisionAt hT U A r ξ a s.time)
    (hsTranscript : s.transcript = idealPadTranscript
      (idealStateAt hT U A r ξ a s.time).transcript)
    (n : ℕ) (hcap : s.time + n ≤ N)
    (hstage : ∀ u < n,
      idealAfterAt hT U A r ξ a (s.time + u) = j.val) :
    actualFrozenGaussianSeedState hT U j A r s a n
      (idealNoiseSlice s.time hcap ξ) =
      idealPadTranscript
        (idealStateAt hT U A r ξ a (s.time + n)).transcript := by
  induction n with
  | zero =>
      simpa [actualFrozenGaussianSeedState, gaussianSeedState]
        using hsTranscript
  | succ n ih =>
      have hcapPrev : s.time + n ≤ N := by omega
      have hn : s.time + n < N := by omega
      have hstagePrev : ∀ u < n,
          idealAfterAt hT U A r ξ a (s.time + u) = j.val := by
        intro u hu
        exact hstage u (by omega)
      have hstageN :
          idealAfterAt hT U A r ξ a (s.time + n) = j.val :=
        hstage n (by omega)
      have hprev := ih hcapPrev hstagePrev
      let old := actualFrozenGaussianSeedState hT U j A r s a n
        (idealNoiseSlice s.time hcapPrev ξ)
      have hstep :
          actualFrozenGaussianSeedState hT U j A r s a (n + 1)
              (idealNoiseSlice s.time hcap ξ) =
            actualFrozenUpdate A r s n
              (old,
                frozenStageHistoryMean U j (actualFrozenQuery A r s)
                  n old + a • ξ ⟨s.time + n, hn⟩) := by
        have hprefix :
            (fun i : Fin n =>
              idealNoiseSlice s.time hcap ξ i.castSucc) =
              idealNoiseSlice s.time hcapPrev ξ := by
          funext i
          rfl
        have hlast :
            idealNoiseSlice s.time hcap ξ (Fin.last n) =
              ξ ⟨s.time + n, hn⟩ := rfl
        change gaussianSeedState d s.transcript
            (frozenStageHistoryMean U j (actualFrozenQuery A r s))
            a (actualFrozenUpdate A r s) (n + 1)
            (idealNoiseSlice s.time hcap ξ) =
          actualFrozenUpdate A r s n
            (gaussianSeedState d s.transcript
              (frozenStageHistoryMean U j (actualFrozenQuery A r s))
              a (actualFrozenUpdate A r s) n
              (idealNoiseSlice s.time hcapPrev ξ),
             frozenStageHistoryMean U j (actualFrozenQuery A r s) n
               old + a • ξ ⟨s.time + n, hn⟩)
        rw [gaussianSeedState_succ, hprefix, hlast]
        rfl
      calc
        actualFrozenGaussianSeedState hT U j A r s a (n + 1)
            (idealNoiseSlice s.time hcap ξ) =
          actualFrozenUpdate A r s n
            (old, frozenStageHistoryMean U j (actualFrozenQuery A r s)
              n old + a • ξ ⟨s.time + n, hn⟩) := hstep
        _ = idealPadTranscript
            (idealStateAt hT U A r ξ a (s.time + (n + 1))).transcript := by
          have heq : s.time + n + 1 = s.time + (n + 1) := by omega
          rw [← heq]
          exact actualFrozenUpdate_eq_idealPadTranscript_succ
            hT U j A r ξ a s hsStarted hsFirst n hn hstageN
            old hprev

end

end HeavyTailedNoise
