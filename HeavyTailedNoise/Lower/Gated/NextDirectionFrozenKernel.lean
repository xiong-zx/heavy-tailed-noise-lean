import HeavyTailedNoise.Probability.ParametricGaussianSeedRecursion
import HeavyTailedNoise.Lower.Gated.ConditionalNextDirectionKL
import HeavyTailedNoise.Lower.Gated.ActualFrozenSeedLaw

/-!
The jointly measurable Markov kernel from one candidate next direction to the
actual frozen final full-history transcript. Its pointwise law is exactly the
already checked `adaptiveGaussianLaw`; no algorithm sees the direction or
Gaussian seed.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem measurable_joint_nextDirectionFrozenState
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T) (v : Fin j.val → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ) :
    Measurable (fun z : Point d × (Fin m → Point d) =>
      actualFrozenGaussianSeedState hT
        (nextDirectionPrefixFrame j v z.1) j A r s a m z.2) := by
  let mean : Point d → ℕ → Transcript d N → Point d :=
    fun θ t h => frozenStageHistoryMean
      (nextDirectionPrefixFrame j v θ) j (actualFrozenQuery A r s) t h
  have hm (t : ℕ) : Measurable
      (fun z : Point d × Transcript d N => mean z.1 t z.2) := by
    exact measurable_frozenPrefixMean_comp hT j
      (fun z : Point d × Transcript d N =>
        nextDirectionPrefixFrame j v z.1)
      ((measurable_nextDirectionPrefixFrame j v).comp measurable_fst)
      (fun z => actualFrozenQuery A r s t z.2)
      ((measurable_actualFrozenQuery A r s t).comp measurable_snd)
  have hjoint := measurable_joint_gaussianSeedState d s.transcript
    mean hm a (actualFrozenUpdate A r s)
    (measurable_actualFrozenUpdate A r s) m
  change Measurable (fun z : Point d × (Fin m → Point d) =>
    gaussianSeedState d s.transcript (mean z.1) a
      (actualFrozenUpdate A r s) m z.2)
  exact hjoint

def nextDirectionFrozenKernel
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T) (v : Fin j.val → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ) :
    Kernel (Point d) (Transcript d N) :=
  (Kernel.prod
    (Kernel.deterministic (id : Point d → Point d) measurable_id)
    (Kernel.const (Point d)
      (Measure.pi (fun _ : Fin m => standardGaussianLaw d)))).map
    (fun z : Point d × (Fin m → Point d) =>
      actualFrozenGaussianSeedState hT
        (nextDirectionPrefixFrame j v z.1) j A r s a m z.2)

instance nextDirectionFrozenKernel_markov
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T) (v : Fin j.val → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ) :
    IsMarkovKernel (nextDirectionFrozenKernel (m := m) hT j v A r s a) := by
  unfold nextDirectionFrozenKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_joint_nextDirectionFrozenState hT j v A r s a)

theorem nextDirectionFrozenKernel_apply
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T) (v : Fin j.val → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ) (θ : Point d) :
    nextDirectionFrozenKernel (m := m) hT j v A r s a θ =
      (Measure.pi (fun _ : Fin m => standardGaussianLaw d)).map
        (actualFrozenGaussianSeedState hT
          (nextDirectionPrefixFrame j v θ) j A r s a m) := by
  unfold nextDirectionFrozenKernel
  rw [Kernel.map_apply _
    (measurable_joint_nextDirectionFrozenState hT j v A r s a),
    Kernel.prod_apply,
    Kernel.deterministic_apply measurable_id,
    Kernel.const_apply, Measure.dirac_prod]
  change ((Measure.pi (fun _ : Fin m => standardGaussianLaw d)).map
      (fun z : Fin m → Point d => (θ, z))).map
        (fun z : Point d × (Fin m → Point d) =>
          actualFrozenGaussianSeedState hT
            (nextDirectionPrefixFrame j v z.1) j A r s a m z.2) = _
  rw [Measure.map_map
    (measurable_joint_nextDirectionFrozenState hT j v A r s a)
    (by fun_prop : Measurable (fun z : Fin m → Point d => (θ, z)))]
  rfl

theorem nextDirectionFrozenKernel_eq_adaptiveGaussianLaw
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T) (v : Fin j.val → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ) (θ : Point d) :
    nextDirectionFrozenKernel (m := m) hT j v A r s a θ =
      adaptiveGaussianLaw d (Measure.dirac s.transcript)
        (actualFrozenStageKernel hT
          (nextDirectionPrefixFrame j v θ) j A r s a)
        (actualFrozenUpdate A r s) m := by
  rw [nextDirectionFrozenKernel_apply]
  exact actualFrozenGaussianSeedState_law hT
    (nextDirectionPrefixFrame j v θ) j A r s a m

end

end HeavyTailedNoise
