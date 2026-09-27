import HeavyTailedNoise.Lower.Gated.IdealInitialShortStageHalf
import HeavyTailedNoise.Lower.Gated.IdealPositiveStageLatestCondExp
import HeavyTailedNoise.Lower.Gated.ActualStageConditionalHalfTransfer
import HeavyTailedNoise.Lower.Gated.IdealCompletionTail

/-!
The actual ideal completion tail under one preselected full-frame Haar law
and the original N Gaussian coordinates, for each fixed arbitrary private
tape.  The initial ordinary mean and positive-stage latest conditional means
are supplied by the checked actual-experiment theorems.  Actual trace/support
localization transfers the latter to the cumulative filtration.  Concrete
adaptation, Bernoulli centering, Azuma, and stage counting are then composed.

All premises are public parameter/dimension inequalities and the fixed
response budget.  No initial mean, conditional-half, conditional-law, trace,
or expected-stopping-time premise is left to the caller.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

set_option autoImplicit false

theorem idealHaar_completion_probability_bound
    {d T N : ℕ} {S : ℝ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hdim : 2 * T ≤ d) (hS : 0 < S)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / (16 * 300 ^ 2)))
    (hdimlog : 21400 * (1 + Real.log (2 * (gatedStageLength d T S : ℝ))) ≤
      ((d - T : ℕ) : ℝ))
    (hbudget : 4 * N ≤ T * gatedStageLength d T S)
    (A : RandomAlgorithm d N Private) (r : Private) :
    (((preselectedOrthonormalFrameLaw d T (by omega)).prod
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d))).real
      {z : IdealAccidentSample d T N |
        idealCompleted hT z.1.1 A r z.2 ((S / 80) / Real.sqrt d)}) ≤
      Real.exp (-(T : ℝ) / 32) := by
  have hTd : T ≤ d := by omega
  have hd : 0 < d := by omega
  let n₀ := gatedStageLength d T S
  let a := (S / 80) / Real.sqrt d
  let P := (preselectedOrthonormalFrameLaw d T hTd).prod
    (Measure.pi (fun _ : Fin N => standardGaussianLaw d))
  let U : IdealAccidentSample d T N → Fin T → Point d := fun z => z.1.1
  let ξ : IdealAccidentSample d T N → Fin N → Point d := Prod.snd
  have hU : Measurable U := measurable_subtype_coe.comp measurable_fst
  have hξ : Measurable ξ := measurable_snd
  have hn₂ : 2 ≤ n₀ := gatedStageLength_ge_two hd hdim hlarge
  have hnpos : 0 < n₀ := by omega
  have hfirst := idealInitialShortStage_mean_half_actual_parameters
    hT hdim hS hlarge hdimlog A r
  have hhalf : ∀ i < T - 1, ∀ᵐ z ∂P,
      P[(fun z => idealShortStageIndicator hT (U z) A r (ξ z) a n₀ (i + 1)) |
        idealStageFiltration hT A r a U ξ hU hξ i] z ≤ (1 : ℝ) / 2 := by
    intro i hi
    let k : Fin T := ⟨i, by omega⟩
    have hk : k.val + 1 < T := by dsimp [k]; omega
    have hk₂ : k.val + 1 + 1 ≤ T := by dsimp [k]; omega
    have hlatest := idealPositiveStage_latestShortPrefix_condExp_half
      hT hdim hS hlarge hdimlog k hk₂ A r
    have hactive : ∀ᵐ z ∂P, z ∈ idealLatestStageActive hT A r a U ξ k →
        P[(fun z => idealShortStageIndicator hT (U z) A r (ξ z) a n₀ (k.val + 1)) |
          MeasurableSpace.comap (idealLatestShortPrefixData hT A r a U ξ k) inferInstance] z ≤
            (1 : ℝ) / 2 := by
      filter_upwards [hlatest] with z hz
      intro _
      exact hz
    have hc := actualStage_cumulative_half_of_active_shortPrefix_half
      P hT A r a U ξ hU hξ k hk n₀ hactive
    simpa only [k] using hc
  exact idealCompleted_Haar_tail_of_cumulative_half hT hTd A r a n₀ hnpos hbudget
    hfirst hhalf

end

end HeavyTailedNoise
