import HeavyTailedNoise.Lower.Gated.NextDirectionPrefixFrame
import HeavyTailedNoise.Lower.Gated.ActualFrozenKernelAssembly

/-!
At a fixed revealed orthonormal prefix, any two valid candidate next Haar
directions induce frozen full-history Gaussian transcript laws with the same
checked 300-contrast KL bound. Only the next direction is varied; later frame
columns are not part of this information experiment.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

theorem nextDirection_prefixGradient_diameter_le_300
    {d T : ℕ} (hTd : T ≤ d) (j : Fin T)
    (v : Fin j.val → Point d) (θ θ' : Point d)
    (hθ : Orthonormal ℝ (Fin.snoc v θ))
    (hθ' : Orthonormal ℝ (Fin.snoc v θ'))
    (x : Point d) :
    ‖gradient (prefixHardPotential (nextDirectionPrefixFrame j v θ) j) x -
      gradient (prefixHardPotential (nextDirectionPrefixFrame j v θ') j) x‖ ≤ 300 := by
  apply norm_gradient_prefixHardPotential_sub_le_300_of_prefix hTd j
  · simpa only [framePrefix_nextDirectionPrefixFrame] using hθ
  · simpa only [framePrefix_nextDirectionPrefixFrame] using hθ'
  · exact nextDirectionPrefixFrame_eq_before j v θ θ'

theorem nextDirection_adaptiveGaussianLaw_klDiv_le
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hd : 0 < d) (hT : 0 < T) (hTd : T ≤ d)
    (j : Fin T) (v : Fin j.val → Point d)
    (θ θ' : Point d)
    (hθ : Orthonormal ℝ (Fin.snoc v θ))
    (hθ' : Orthonormal ℝ (Fin.snoc v θ'))
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (n : ℕ) :
    klDiv
      (adaptiveGaussianLaw d (Measure.dirac s.transcript)
        (actualFrozenStageKernel hT
          (nextDirectionPrefixFrame j v θ) j A r s
          (σ₀ / Real.sqrt d))
        (actualFrozenUpdate A r s) n)
      (adaptiveGaussianLaw d (Measure.dirac s.transcript)
        (actualFrozenStageKernel hT
          (nextDirectionPrefixFrame j v θ') j A r s
          (σ₀ / Real.sqrt d))
        (actualFrozenUpdate A r s) n) ≤
      (n : ENNReal) * ENNReal.ofReal
        ((d : ℝ) * (300 : ℝ) ^ 2 / (2 * σ₀ ^ 2)) := by
  let Uθ := nextDirectionPrefixFrame j v θ
  let Uθ' := nextDirectionPrefixFrame j v θ'
  let q := actualFrozenQuery A r s
  have hq : ∀ t, Measurable (q t) :=
    measurable_actualFrozenQuery A r s
  have hdiam (t : ℕ) (h : Transcript d N) :
      ‖frozenStageHistoryMean Uθ j q t h -
        frozenStageHistoryMean Uθ' j q t h‖ ≤ 300 := by
    exact nextDirection_prefixGradient_diameter_le_300
      hTd j v θ θ' hθ hθ' (q t h)
  exact adaptiveGaussianLaw_klDiv_le d hd σ₀ hσ₀ 300
    (Measure.dirac s.transcript)
    (actualFrozenStageKernel hT Uθ j A r s (σ₀ / Real.sqrt d))
    (actualFrozenStageKernel hT Uθ' j A r s (σ₀ / Real.sqrt d))
    (fun t => frozenStageHistoryKernel_markov hT Uθ j q hq
      (σ₀ / Real.sqrt d) t)
    (fun t => frozenStageHistoryKernel_markov hT Uθ' j q hq
      (σ₀ / Real.sqrt d) t)
    (frozenStageHistoryMean Uθ j q)
    (frozenStageHistoryMean Uθ' j q)
    (fun t h => frozenStageHistoryKernel_apply hT Uθ j q hq
      (σ₀ / Real.sqrt d) t h)
    (fun t h => frozenStageHistoryKernel_apply hT Uθ' j q hq
      (σ₀ / Real.sqrt d) t h)
    hdiam (actualFrozenUpdate A r s)
    (measurable_actualFrozenUpdate A r s) n

end

end HeavyTailedNoise
