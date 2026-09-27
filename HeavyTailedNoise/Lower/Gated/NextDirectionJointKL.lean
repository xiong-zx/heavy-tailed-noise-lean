import HeavyTailedNoise.Lower.Gated.NextDirectionValidSupport
import HeavyTailedNoise.Probability.GaussianKLMixture
import HeavyTailedNoise.Lower.Gated.FrozenHaarReferenceCap

/-!
At one fixed valid revealed prefix and stopped pre-response snapshot, the
next-direction Haar law and the full-history frozen transcript form a jointly
measurable Markov experiment. A fixed valid reference direction gives a
direction-independent reference transcript law and the checked Gaussian KL
and Haar cap bounds on the same experiment.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

def repairedNextDirectionFrozenKernel
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T) (v : Fin j.val → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ)
    (θ₀ : Point d) : Kernel (Point d) (Transcript d N) :=
  (nextDirectionFrozenKernel (m := m) hT j v A r s a).comap
    (repairNextDirection v θ₀) (measurable_repairNextDirection v θ₀)

instance repairedNextDirectionFrozenKernel_markov
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T) (v : Fin j.val → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ)
    (θ₀ : Point d) :
    IsMarkovKernel (repairedNextDirectionFrozenKernel
      (m := m) hT j v A r s a θ₀) := by
  unfold repairedNextDirectionFrozenKernel
  infer_instance

lemma repairedNextDirectionFrozenKernel_apply
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T) (v : Fin j.val → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ)
    (θ₀ θ : Point d) :
    repairedNextDirectionFrozenKernel
      (m := m) hT j v A r s a θ₀ θ =
      nextDirectionFrozenKernel (m := m) hT j v A r s a
        (repairNextDirection v θ₀ θ) := by
  rfl

theorem repairedNextDirectionFrozenKernel_ae_eq_original
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T) (v : Fin j.val → Point d)
    (hjd : j.val < d) (hv : Orthonormal ℝ v)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (a : ℝ) (θ₀ : Point d) :
    (fun θ => repairedNextDirectionFrozenKernel
      (m := m) hT j v A r s a θ₀ θ) =ᵐ[frameNextKernel d j.val v]
      nextDirectionFrozenKernel (m := m) hT j v A r s a := by
  filter_upwards [repairNextDirection_ae_eq_self hjd v hv θ₀] with θ hθ
  simpa only [repairedNextDirectionFrozenKernel_apply, hθ, id_eq]

def nextDirectionFinalCapEvent
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (v : Fin j → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) :
    Set (Point d × Transcript d N) :=
  {p | ∃ i : Fin (m + 1),
    p.1 ∈ fixedPrefixCap v
      (frozenFinalQueryList (m := m) hT A r s p.2 i)}

theorem nextDirection_jointKL_le
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hd : 0 < d) (hT : 0 < T) (hTd : T ≤ d)
    (j : Fin T) (v : Fin j.val → Point d)
    (θ₀ : Point d) (hθ₀ : Orthonormal ℝ (Fin.snoc v θ₀))
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) :
    let K := repairedNextDirectionFrozenKernel
      (m := m) hT j v A r s (σ₀ / Real.sqrt d) θ₀
    let R := nextDirectionFrozenKernel (m := m)
      hT j v A r s (σ₀ / Real.sqrt d) θ₀
    klDiv ((frameNextKernel d j.val v) ⊗ₘ K)
      ((frameNextKernel d j.val v).prod R) ≤
      (m : ENNReal) * ENNReal.ofReal
        ((d : ℝ) * (300 : ℝ) ^ 2 / (2 * σ₀ ^ 2)) := by
  dsimp only
  let K := repairedNextDirectionFrozenKernel
    (m := m) hT j v A r s (σ₀ / Real.sqrt d) θ₀
  let R := nextDirectionFrozenKernel (m := m)
    hT j v A r s (σ₀ / Real.sqrt d) θ₀
  apply mixture_reference_klDiv_le
    (frameNextKernel d j.val v) K R _
  intro θ
  have hθ : Orthonormal ℝ
      (Fin.snoc v (repairNextDirection v θ₀ θ)) :=
    repairNextDirection_valid v θ₀ θ hθ₀
  change klDiv
      (repairedNextDirectionFrozenKernel
        (m := m) hT j v A r s (σ₀ / Real.sqrt d) θ₀ θ)
      (nextDirectionFrozenKernel
        (m := m) hT j v A r s (σ₀ / Real.sqrt d) θ₀) ≤ _
  rw [repairedNextDirectionFrozenKernel_apply,
    nextDirectionFrozenKernel_eq_adaptiveGaussianLaw,
    nextDirectionFrozenKernel_eq_adaptiveGaussianLaw]
  exact nextDirection_adaptiveGaussianLaw_klDiv_le
    hd hT hTd j v (repairNextDirection v θ₀ θ) θ₀
    hθ hθ₀ σ₀ hσ₀ A r s m

theorem nextDirection_referenceProduct_cap_bound
    {d T N m budget : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T) (v : Fin j.val → Point d)
    (hv : Orthonormal ℝ v) (hjd : j.val < d)
    (hDim : 16022 ≤ d - j.val)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N)
    (θ₀ : Point d)
    (σ₀ : ℝ) (hlen : m + 1 ≤ budget + 2) :
    let R := nextDirectionFrozenKernel (m := m)
      hT j v A r s (σ₀ / Real.sqrt d) θ₀
    ((frameNextKernel d j.val v).prod R).real
      (nextDirectionFinalCapEvent (m := m) hT v A r s) ≤
      2 * (budget + 2 : ℕ) *
        Real.exp (-((d - j.val : ℕ) : ℝ) * haarCapAngleSq / 2) := by
  dsimp only [nextDirectionFinalCapEvent]
  exact fixedPrefixCap_reference_product_union hjd v hv hDim
    (nextDirectionFrozenKernel (m := m) hT j v A r s
      (σ₀ / Real.sqrt d) θ₀)
    (frozenFinalQueryList hT A r s)
    (measurable_frozenFinalQueryList hT A r s) hlen

end

end HeavyTailedNoise
