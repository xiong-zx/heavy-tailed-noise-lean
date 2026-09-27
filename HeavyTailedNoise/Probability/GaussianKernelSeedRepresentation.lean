import HeavyTailedNoise.Probability.GaussianMeanKernel

/-!
One-step equality between an adaptive Gaussian kernel transition and an
explicit independent standard-Gaussian seed passed through the same measurable
state update. This is a probability-law identity, not an alternative oracle.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem gaussianMeanKernel_compProd_update_eq_seed_map
    {H : Type*} [MeasurableSpace H]
    (d : ℕ) (P : Measure H) [IsProbabilityMeasure P]
    (m : H → Point d) (hm : Measurable m) (a : ℝ)
    (update : H × Point d → H) (hUpdate : Measurable update) :
    ((P ⊗ₘ gaussianMeanKernel d m hm a).map update) =
      (P.prod (standardGaussianLaw d)).map
        (fun z : H × Point d => update (z.1, m z.1 + a • z.2)) := by
  letI : IsMarkovKernel (gaussianMeanKernel d m hm a) :=
    gaussianMeanKernel_markov d m hm a
  let f : H × Point d → H :=
    fun z => update (z.1, m z.1 + a • z.2)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  ext s hs
  rw [Measure.map_apply hUpdate hs, Measure.map_apply hf hs]
  rw [Measure.compProd_apply (hUpdate hs), Measure.prod_apply (hf hs)]
  apply lintegral_congr
  intro h
  have hsection : MeasurableSet
      (Prod.mk h ⁻¹' (update ⁻¹' s)) :=
    (hUpdate hs).preimage (measurable_const.prodMk measurable_id)
  rw [gaussianMeanKernel_apply, gaussianResponseLaw]
  rw [Measure.map_apply (by fun_prop : Measurable
    (fun ξ : Point d => m h + a • ξ)) hsection]
  rfl

end

end HeavyTailedNoise
