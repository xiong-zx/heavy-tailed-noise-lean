import HeavyTailedNoise.Lower.Gated.IdealStoppedSnapshotFields

/-!
Instantiate the full-history frozen/ideal pathwise identity at the actual
bounded stage-start snapshot. The equality holds for every response before
the post-cap ideal stage leaves the frozen stage.
-/

namespace HeavyTailedNoise

noncomputable section

theorem actualFrozenGaussianSeedState_eq_stoppedIdealPad
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hstart : idealStageStart hT U A r ξ a (k.val + 1) ≤ N)
    (n : ℕ)
    (hcap : idealStageStart hT U A r ξ a (k.val + 1) + n ≤ N)
    (hstage : ∀ u < n,
      idealAfterAt hT U A r ξ a
        (idealStageStart hT U A r ξ a (k.val + 1) + u) = j.val) :
    actualFrozenGaussianSeedState hT U j A r
      (idealStoppedPreHistory hT U k A r ξ a) a n
      (idealNoiseSlice
        (idealStageStart hT U A r ξ a (k.val + 1)) hcap ξ) =
      idealPadTranscript
        (idealStateAt hT U A r ξ a
          (idealStageStart hT U A r ξ a (k.val + 1) + n)).transcript := by
  let τ := idealStageStart hT U A r ξ a (k.val + 1)
  let s := idealStoppedPreHistory hT U k A r ξ a
  have hs := idealStoppedPreHistory_eq_started_record
    hT U k A r ξ a hstart
  have hsStarted : s.started = true := by simp [s, hs]
  have hsTime : s.time = τ := by simp [s, hs, τ]
  have hsFirst : s.query = idealDecisionAt hT U A r ξ a s.time := by
    simp [s, hs]
  have hsTranscript : s.transcript = idealPadTranscript
      (idealStateAt hT U A r ξ a s.time).transcript := by
    rw [hsTime]
    simp [s, hs, τ]
  have hcapS : s.time + n ≤ N := by simpa only [hsTime] using hcap
  have hstageS : ∀ u < n,
      idealAfterAt hT U A r ξ a (s.time + u) = j.val := by
    intro u hu
    simpa only [hsTime] using hstage u hu
  have hpath := actualFrozenGaussianSeedState_eq_idealPadTranscript
    hT U j A r ξ a s hsStarted hsFirst hsTranscript
    n hcapS hstageS
  have hSlice : idealNoiseSlice s.time hcapS ξ =
      idealNoiseSlice τ hcap ξ := by
    funext i
    apply congrArg ξ
    apply Fin.ext
    simp [idealNoiseSlice, hsTime]
  have hTimeSum : s.time + n = τ + n := congrArg (· + n) hsTime
  change actualFrozenGaussianSeedState hT U j A r s a n
      (idealNoiseSlice τ hcap ξ) =
    idealPadTranscript (idealStateAt hT U A r ξ a (τ + n)).transcript
  calc
    actualFrozenGaussianSeedState hT U j A r s a n
        (idealNoiseSlice τ hcap ξ) =
      actualFrozenGaussianSeedState hT U j A r s a n
        (idealNoiseSlice s.time hcapS ξ) := by rw [hSlice]
    _ = idealPadTranscript
        (idealStateAt hT U A r ξ a (s.time + n)).transcript := hpath
    _ = idealPadTranscript
        (idealStateAt hT U A r ξ a (τ + n)).transcript := by rw [hTimeSum]

end

end HeavyTailedNoise
