import HeavyTailedNoise.Probability.GaussianAdaptiveSeedLaw
import HeavyTailedNoise.Lower.Gated.ActualFrozenKernelAssembly

/-!
The actual full-history frozen Gaussian response chain, driven by one fresh
standard Gaussian vector in each auxiliary slot, has exactly the adaptive
Markov law used by the checked KL bound. Slots beyond the hard response cap
remain unobserved because `actualFrozenUpdate` ignores their responses.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

def actualFrozenGaussianSeedState
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ)
    (n : ℕ) (ξ : Fin n → Point d) : Transcript d N :=
  gaussianSeedState d s.transcript
    (frozenStageHistoryMean U j (actualFrozenQuery A r s))
    a (actualFrozenUpdate A r s) n ξ

theorem actualFrozenGaussianSeedState_law
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => standardGaussianLaw d)).map
      (actualFrozenGaussianSeedState hT U j A r s a n) =
      adaptiveGaussianLaw d (Measure.dirac s.transcript)
        (actualFrozenStageKernel hT U j A r s a)
        (actualFrozenUpdate A r s) n := by
  have h := gaussianSeedState_law_eq_adaptiveGaussianLaw
    d s.transcript
    (frozenStageHistoryMean U j (actualFrozenQuery A r s))
    (fun t => measurable_frozenStageHistoryMean hT U j
      (actualFrozenQuery A r s)
      (measurable_actualFrozenQuery A r s) t)
    a (actualFrozenUpdate A r s)
    (measurable_actualFrozenUpdate A r s) n
  change
    (Measure.pi (fun _ : Fin n => standardGaussianLaw d)).map
      (gaussianSeedState d s.transcript
        (frozenStageHistoryMean U j (actualFrozenQuery A r s))
        a (actualFrozenUpdate A r s) n) =
      adaptiveGaussianLaw d (Measure.dirac s.transcript)
        (fun t => gaussianMeanKernel d
          (frozenStageHistoryMean U j (actualFrozenQuery A r s) t)
          (measurable_frozenStageHistoryMean hT U j
            (actualFrozenQuery A r s)
            (measurable_actualFrozenQuery A r s) t) a)
        (actualFrozenUpdate A r s) n
  exact h

end

end HeavyTailedNoise
