import HeavyTailedNoise.Probability.GaussianKL

namespace HeavyTailedNoise
open MeasureTheory ProbabilityTheory
noncomputable section

/-- A history-measurable actual Gaussian response kernel with the mean chosen
from the full history. -/
def gaussianMeanKernel {H : Type*} [MeasurableSpace H]
    (d : ℕ) (m : H → Point d) (hm : Measurable m) (a : ℝ) :
    Kernel H (Point d) :=
  (Kernel.prod (Kernel.deterministic m hm)
    (Kernel.const H (standardGaussianLaw d))).map
      (fun p : Point d × Point d => p.1 + a • p.2)

lemma gaussianMeanKernel_apply {H : Type*} [MeasurableSpace H]
    (d : ℕ) (m : H → Point d) (hm : Measurable m)
    (a : ℝ) (h : H) :
    gaussianMeanKernel d m hm a h = gaussianResponseLaw d (m h) a := by
  unfold gaussianMeanKernel gaussianResponseLaw
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.deterministic_apply hm, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma gaussianMeanKernel_markov {H : Type*} [MeasurableSpace H]
    (d : ℕ) (m : H → Point d) (hm : Measurable m) (a : ℝ) :
    IsMarkovKernel (gaussianMeanKernel d m hm a) := by
  unfold gaussianMeanKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)


end
end HeavyTailedNoise
