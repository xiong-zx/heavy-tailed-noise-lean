import HeavyTailedNoise.Lower.Gated.HardStationarity
import HeavyTailedNoise.Lower.Gated.RealIdealStoppedCoupling
import HeavyTailedNoise.Lower.Gated.LowerBoundCouplingAssembly

/-!
The final ideal decision is response-free. A small unscaled gradient there
forces completion or a prefix accident at that decision, for an arbitrary
full-history algorithm and output point.
-/

namespace HeavyTailedNoise

noncomputable section

theorem idealOutput_small_gradient_implies_completion_or_accident
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hg : ‖gradient (hardPotential U)
      (idealDecisionAt hT U A r ξ a N)‖ < (1 / 40 : ℝ)) :
    idealCompleted hT U A r ξ a ∨ idealPrefixAccidentAt hT U A r ξ a N := by
  classical
  let stage := (idealStateAt hT U A r ξ a N).stage
  let x := idealDecisionAt hT U A r ξ a N
  let last : Fin T := ⟨T - 1, by omega⟩
  have hlast : last.val + 1 = T := by dsimp [last]; omega
  have hcap : softProjection (hardRadius T) x ∈ prefixCapSet U last :=
    mem_final_prefixCapSet_of_small_gradient hU hT last hlast x hg
  have hcoords := (hardPotential_stationarity_decoding hU hT x hg).1
  by_cases hdone : T ≤ stage
  · left
    apply (idealCompleted_iff_final_stage_reached hT U A r ξ a).2
    change T ≤ idealStageAfter U stage x
    exact hdone.trans (idealStage_le_after U stage x)
  · have hstage : stage < T := by omega
    by_cases hfinal : stage = T - 1
    · have hhit : idealCapHit U stage x := by
        refine ⟨hstage, ?_⟩
        simpa only [hfinal, last] using hcap
      left
      apply (idealCompleted_iff_final_stage_reached hT U A r ξ a).2
      change T ≤ idealStageAfter U stage x
      simp only [idealStageAfter, hhit, ite_true]
      omega
    · right
      have hindex : idealPrefixIndex hT stage < last := by
        change min stage (T - 1) < T - 1
        omega
      change softProjection (hardRadius T) x ∈
        prefixAccidentSet U (idealPrefixIndex hT stage)
      refine ⟨last, hindex, ?_⟩
      linarith [hcoords last]

end

end HeavyTailedNoise
