import HeavyTailedNoise.Probability.BoundedFibers
import HeavyTailedNoise.Lower.Gated.IdealRandomStartTail

/-!
Finite measure decomposition over every possible stage-start time, including
the `N+1` never-started sentinel. No expected stopping-time budget is used.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem idealExtendedNoiseLaw_eq_sum_stageStart_restrict
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d) =
      Measure.sum (fun t : Fin (N + 2) =>
        (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).restrict
          {ξ | idealExtendedStageStart hT U k A r a ξ = t.val}) := by
  apply measure_eq_sum_restrict_bounded_nat_fibers
    (hτ := measurable_idealExtendedStageStart hT U k A r a)
  intro ξ
  have hb := idealStageStart_le_succ hT U A r
    (idealExtendedNoiseTake ξ) a (k.val + 1)
  change idealStageStart hT U A r (idealExtendedNoiseTake ξ) a
    (k.val + 1) < N + 2
  omega

end

end HeavyTailedNoise
