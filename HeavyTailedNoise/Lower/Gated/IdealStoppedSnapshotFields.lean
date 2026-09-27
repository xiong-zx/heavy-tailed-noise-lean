import HeavyTailedNoise.Lower.Gated.IdealFrozenPathwise

/-!
Exact fields of the actual pre-response stage-start record on a started path.
The query at time `N` remains a response-free output decision.
-/

namespace HeavyTailedNoise

noncomputable section

theorem idealStoppedPreHistory_eq_started_record
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hstart : idealStageStart hT U A r ξ a (k.val + 1) ≤ N) :
    idealStoppedPreHistory hT U k A r ξ a =
      ⟨true, idealStageStart hT U A r ξ a (k.val + 1),
        idealPadTranscript
          (idealStateAt hT U A r ξ a
            (idealStageStart hT U A r ξ a (k.val + 1))).transcript,
        idealDecisionAt hT U A r ξ a
          (idealStageStart hT U A r ξ a (k.val + 1))⟩ := by
  simp [idealStoppedPreHistory, idealPreHistoryAtTime, hstart]

end

end HeavyTailedNoise
