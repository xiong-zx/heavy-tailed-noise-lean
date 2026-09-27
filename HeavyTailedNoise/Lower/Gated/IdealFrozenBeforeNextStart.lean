import HeavyTailedNoise.Lower.Gated.IdealStageBetweenStarts

/-!
The actual frozen Gaussian continuation and ideal full transcript agree on
every response slot before the next stage starts. The exiting query is chosen
from that common history before its response can differ.
-/

namespace HeavyTailedNoise

noncomputable section

theorem actualFrozenGaussianSeedState_eq_ideal_before_nextStart
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (k j : Fin T) (hjk : j.val = k.val + 1)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hstart : idealStageStart hT U A r ξ a (k.val + 1) ≤ N)
    (n : ℕ)
    (hcap : idealStageStart hT U A r ξ a (k.val + 1) + n ≤ N)
    (hbefore : idealStageStart hT U A r ξ a (k.val + 1) + n ≤
      idealStageStart hT U A r ξ a (j.val + 1)) :
    actualFrozenGaussianSeedState hT U j A r
      (idealStoppedPreHistory hT U k A r ξ a) a n
      (idealNoiseSlice
        (idealStageStart hT U A r ξ a (k.val + 1)) hcap ξ) =
      idealPadTranscript
        (idealStateAt hT U A r ξ a
          (idealStageStart hT U A r ξ a (k.val + 1) + n)).transcript := by
  have hjpos : 0 < j.val := by omega
  have hstartJ : idealStageStart hT U A r ξ a j.val ≤ N := by
    simpa only [hjk] using hstart
  have hstage : ∀ u < n,
      idealAfterAt hT U A r ξ a
        (idealStageStart hT U A r ξ a (k.val + 1) + u) = j.val := by
    intro u hu
    have hlo : idealStageStart hT U A r ξ a j.val ≤
        idealStageStart hT U A r ξ a (k.val + 1) + u := by
      rw [hjk]
      omega
    have hhi : idealStageStart hT U A r ξ a (k.val + 1) + u <
        idealStageStart hT U A r ξ a (j.val + 1) := by omega
    have htN : idealStageStart hT U A r ξ a (k.val + 1) + u ≤ N := by
      omega
    exact idealAfterAt_eq_stage_betweenStarts
      hT U A r ξ a j.val _ hjpos hstartJ hlo hhi htN
  exact actualFrozenGaussianSeedState_eq_stoppedIdealPad
    hT U k j A r ξ a hstart n hcap hstage

end

end HeavyTailedNoise
