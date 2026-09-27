import HeavyTailedNoise.Lower.Gated.ActualStageLatestEncoding
import HeavyTailedNoise.Lower.Gated.ConditionalHalfLocalization

/-!
Actual transfer from the latest conditional half bound to the cumulative
stage filtration.  Integrability, sigma-algebra inclusions, active-event
measurability, trace recovery, and zero off the active branch are discharged
from the concrete ideal process.  Only the latest active half bound remains
a stochastic premise.  Finite measures suffice; no standard Borel assumption
is imposed on Ω or Private.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

set_option autoImplicit false

theorem idealShortStageIndicator_mem_Icc
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (m i : ℕ) :
    idealShortStageIndicator hT U A r ξ a m i ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold idealShortStageIndicator
  split_ifs <;> norm_num [Set.mem_Icc]

theorem integrable_idealShortStageIndicator
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) (m i : ℕ) :
    Integrable (fun ω => idealShortStageIndicator hT (U ω) A r (ξ ω) a m i) μ := by
  have hs := (idealShortStageIndicator_stronglyAdapted hT A r a U ξ hU hξ m i).mono
    ((idealStageFiltration hT A r a U ξ hU hξ).le i)
  exact Integrable.of_mem_Icc 0 1 hs.measurable.aemeasurable
    (Filter.Eventually.of_forall (fun ω => idealShortStageIndicator_mem_Icc hT (U ω) A r (ξ ω) a m i))

theorem idealNextShortStageIndicator_zero_off_latest_active
    {d T N : ℕ} {Private Ω : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (k : Fin T) (hk : k.val + 1 < T) (m : ℕ) (ω : Ω)
    (hoff : ω ∉ idealLatestStageActive hT A r a U ξ k) :
    idealShortStageIndicator hT (U ω) A r (ξ ω) a m (k.val + 1) = 0 := by
  have hi : idealPrefixIndex hT k.val = k := by
    apply Fin.ext
    simp only [idealPrefixIndex]
    omega
  have hnot : ¬ (idealStoppedPreHistory hT (U ω) k A r (ξ ω) a).started = true := by
    simpa only [idealLatestStageActive, Set.mem_ofPred_eq, idealStageObservation,
      hi, idealPreResponseTuple] using hoff
  have hs : (idealStoppedPreHistory hT (U ω) k A r (ξ ω) a).started = false := by
    cases hflag : (idealStoppedPreHistory hT (U ω) k A r (ξ ω) a).started with
    | false => rfl
    | true => exact False.elim (hnot hflag)
  exact idealNextShortStageIndicator_eq_zero_of_latest_never_started
    hT (U ω) k hk A r (ξ ω) a m hs

/-- The concrete transfer has no trace, integrability, or support premises.
Its only stochastic hypothesis is the latest conditional mean bound on active. -/
theorem actualStage_cumulative_half_of_active_latest_half
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) (k : Fin T) (hk : k.val + 1 < T) (m : ℕ)
    (hhalf : ∀ᵐ ω ∂μ, ω ∈ idealLatestStageActive hT A r a U ξ k →
      μ[(fun η => idealShortStageIndicator hT (U η) A r (ξ η) a m (k.val + 1)) |
        idealLatestObservationSigma hT A r a U ξ k] ω ≤ (1 : ℝ) / 2) :
    ∀ᵐ ω ∂μ,
      μ[(fun η => idealShortStageIndicator hT (U η) A r (ξ η) a m (k.val + 1)) |
        idealStageFiltration hT A r a U ξ hU hξ k.val] ω ≤ (1 : ℝ) / 2 := by
  exact condExp_cumulative_le_half_of_active_latest_half μ
    (idealLatestObservationSigma hT A r a U ξ k)
    (idealStageFiltration hT A r a U ξ hU hξ k.val)
    (idealLatestObservationSigma_le_cumulative hT A r a U ξ hU hξ k)
    (idealStageFiltration_le_ambient hT A r a U ξ hU hξ k)
    (idealLatestStageActive hT A r a U ξ k)
    (measurableSet_idealLatestStageActive hT A r a U ξ k)
    (fun B hB => idealStageFiltration_trace_latest_on_started hT A r a U ξ hU hξ k B hB)
    (fun η => idealShortStageIndicator hT (U η) A r (ξ η) a m (k.val + 1))
    (integrable_idealShortStageIndicator μ hT A r a U ξ hU hξ m (k.val + 1))
    (Filter.Eventually.of_forall (fun ω =>
      idealNextShortStageIndicator_zero_off_latest_active hT A r a U ξ k hk m ω)) hhalf

/-- Kernel-data form of the same concrete transfer, using the proved source
sigma-algebra equality for the short prefix and actual stopped tuple. -/
theorem actualStage_cumulative_half_of_active_shortPrefix_half
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) (k : Fin T) (hk : k.val + 1 < T) (m : ℕ)
    (hhalf : ∀ᵐ ω ∂μ, ω ∈ idealLatestStageActive hT A r a U ξ k →
      μ[(fun η => idealShortStageIndicator hT (U η) A r (ξ η) a m (k.val + 1)) |
        MeasurableSpace.comap (idealLatestShortPrefixData hT A r a U ξ k) inferInstance] ω ≤
          (1 : ℝ) / 2) :
    ∀ᵐ ω ∂μ,
      μ[(fun η => idealShortStageIndicator hT (U η) A r (ξ η) a m (k.val + 1)) |
        idealStageFiltration hT A r a U ξ hU hξ k.val] ω ≤ (1 : ℝ) / 2 := by
  apply actualStage_cumulative_half_of_active_latest_half μ hT A r a U ξ hU hξ k hk m
  simpa only [idealLatestObservationSigma_eq_shortPrefixData] using hhalf

end

end HeavyTailedNoise
