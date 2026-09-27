import HeavyTailedNoise.Lower.Gated.ActualFrozenQueryRule
import HeavyTailedNoise.Lower.Gated.FrozenStageKernelAssembly

/-!
The checked fixed-horizon Gaussian KL bound instantiated with the actual
full-history query rule after a fixed stopped pre-response snapshot. The
identification of this Markov law with the conditional ideal-process law is
the next, separate obligation.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

def actualFrozenStageKernel
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ) :
    ℕ → Kernel (Transcript d N) (Point d) :=
  frozenStageHistoryKernel hT U j (actualFrozenQuery A r s)
    (measurable_actualFrozenQuery A r s) a

theorem actualFrozen_adaptiveGaussianLaw_klDiv_le
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hd : 0 < d) (hT : 0 < T)
    {U V : Fin T → Point d} (hU : Orthonormal ℝ U)
    (hV : Orthonormal ℝ V) (j : Fin T)
    (hpre : ∀ i, i < j → U i = V i)
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (n : ℕ) :
    klDiv
      (adaptiveGaussianLaw d (Measure.dirac s.transcript)
        (actualFrozenStageKernel hT U j A r s (σ₀ / Real.sqrt d))
        (actualFrozenUpdate A r s) n)
      (adaptiveGaussianLaw d (Measure.dirac s.transcript)
        (actualFrozenStageKernel hT V j A r s (σ₀ / Real.sqrt d))
        (actualFrozenUpdate A r s) n) ≤
      (n : ENNReal) * ENNReal.ofReal
        ((d : ℝ) * (300 : ℝ) ^ 2 / (2 * σ₀ ^ 2)) := by
  exact frozenStage_adaptiveGaussianLaw_klDiv_le hd hT hU hV j hpre
    σ₀ hσ₀ (actualFrozenQuery A r s)
    (measurable_actualFrozenQuery A r s)
    (Measure.dirac s.transcript) (actualFrozenUpdate A r s)
    (measurable_actualFrozenUpdate A r s) n

end

end HeavyTailedNoise
