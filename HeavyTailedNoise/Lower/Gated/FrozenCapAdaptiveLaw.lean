import HeavyTailedNoise.Lower.Gated.FrozenCapFinalEventEquivalence

/-!
The probability of the pathwise frozen cap event under an explicit iid
Gaussian seed tape is exactly the probability of the measurable final-state
event under the adaptive Gaussian law already controlled by KL.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem frozenCapHit_seedLaw_eq_adaptiveLaw
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ) :
    (Measure.pi (fun _ : Fin m => standardGaussianLaw d))
      {ζ | frozenPrefixCapHitWithin hT U j A r s a ζ} =
      (adaptiveGaussianLaw d (Measure.dirac s.transcript)
        (actualFrozenStageKernel hT U j A r s a)
        (actualFrozenUpdate A r s) m)
        (frozenFinalCapHit (m := m) hT U j A r s) := by
  have hrun : Measurable
      (actualFrozenGaussianSeedState hT U j A r s a m) := by
    exact measurable_gaussianSeedState d s.transcript
      (frozenStageHistoryMean U j (actualFrozenQuery A r s))
      (fun t => measurable_frozenStageHistoryMean hT U j
        (actualFrozenQuery A r s)
        (measurable_actualFrozenQuery A r s) t)
      a (actualFrozenUpdate A r s)
      (measurable_actualFrozenUpdate A r s) m
  have hcap := measurableSet_frozenFinalCapHit
    (m := m) hT U j A r s
  have hset : {ζ : Fin m → Point d |
      frozenPrefixCapHitWithin hT U j A r s a ζ} =
      (actualFrozenGaussianSeedState hT U j A r s a m) ⁻¹'
        frozenFinalCapHit (m := m) hT U j A r s := by
    ext ζ
    exact frozenPrefixCapHitWithin_iff_finalCapHit hT U j A r s a ζ
  rw [hset]
  rw [← Measure.map_apply hrun hcap]
  rw [actualFrozenGaussianSeedState_law]

end

end HeavyTailedNoise
