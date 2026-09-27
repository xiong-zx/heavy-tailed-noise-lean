import HeavyTailedNoise.Lower.Gated.IdealStageFiltration
import HeavyTailedNoise.Lower.Gated.IdealQueryJointMeas

/-!
Concrete completion concentration for the ideal strict-K=1 protocol.
The actual cumulative filtration supplies strong adaptedness; the actual
short-completed-stage indicators are `{0,1}` valued; deterministic stage
counting supplies the completion-to-count inclusion. Centering and all MGF
and domination inputs are discharged by `StageBernoulliCentering`.

Only the initial ordinary mean and subsequent cumulative conditional means
bounded by `1/2` remain probability inputs. Private randomness is fixed, with
no standard Borel assumption on its measurable space. The actual Haar-frame
and finite Gaussian-tape sample space is proved standard Borel using the
already checked measurability of the orthonormal-frame set.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem idealShortStageIndicator_zero_or_one
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (m i : ℕ) :
    idealShortStageIndicator hT U A r ξ a m i = 0 ∨
      idealShortStageIndicator hT U A r ξ a m i = 1 := by
  classical
  unfold idealShortStageIndicator
  split_ifs <;> simp

/-- Completion under the fixed response budget forces the threshold of the
actual indicator sum, including the arbitrary output at decision `N`. -/
theorem idealCompleted_implies_short_indicator_sum_threshold
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (m : ℕ)
    (hm : 0 < m) (hbudget : 4 * N ≤ T * m)
    (hcomplete : idealCompleted hT U A r ξ a) :
    3 * (T : ℝ) / 4 ≤
      ∑ i ∈ Finset.range T, idealShortStageIndicator hT U A r ξ a m i := by
  classical
  have hc := idealCompleted_forces_many_short_stages hT U A r ξ a m hm hbudget hcomplete
  have hcReal : 3 * (T : ℝ) ≤
      4 * ((Finset.univ.filter fun j : Fin T =>
        idealShortCompletedStage hT U A r ξ a m j).card : ℝ) := by
    exact_mod_cast hc
  rw [idealShortStageIndicator_sum]
  linarith

/-- Exact concrete composition. No abstract centered process, adaptedness,
subgaussian-MGF, or domination assumption is left to the caller. -/
theorem idealCompleted_tail_of_cumulative_half
    {d T N : ℕ} {Private Ω : Type*} [MeasurableSpace Private]
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ)
    (m : ℕ) (hm : 0 < m) (hbudget : 4 * N ≤ T * m)
    (hfirst : (∫ ω, idealShortStageIndicator hT (U ω) A r (ξ ω) a m 0 ∂μ) ≤
      (1 : ℝ) / 2)
    (hhalf : ∀ i < T - 1, ∀ᵐ ω ∂μ,
      μ[fun ω => idealShortStageIndicator hT (U ω) A r (ξ ω) a m (i + 1) |
        idealStageFiltration hT A r a U ξ hU hξ i] ω ≤ (1 : ℝ) / 2) :
    μ.real {ω | idealCompleted hT (U ω) A r (ξ ω) a} ≤
      Real.exp (-(T : ℝ) / 32) := by
  let X : ℕ → Ω → ℝ := fun i ω => idealShortStageIndicator hT (U ω) A r (ξ ω) a m i
  let ℱ := idealStageFiltration hT A r a U ξ hU hξ
  have hadapt : StronglyAdapted ℱ X :=
    idealShortStageIndicator_stronglyAdapted hT A r a U ξ hU hξ m
  have hind : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 ∨ X i ω = 1 := by
    intro i
    exact Filter.Eventually.of_forall (fun ω =>
      idealShortStageIndicator_zero_or_one hT (U ω) A r (ξ ω) a m i)
  have hcount := stage_indicator_count_tail_of_condExp_half
    μ ℱ X T hadapt hind hfirst hhalf
  have hsubset : {ω | idealCompleted hT (U ω) A r (ξ ω) a} ⊆
      {ω | 3 * (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, X i ω} := by
    intro ω hcomplete
    exact idealCompleted_implies_short_indicator_sum_threshold
      hT (U ω) A r (ξ ω) a m hm hbudget hcomplete
  exact (measureReal_mono hsubset).trans hcount

/-- The actual frame/tape space is standard Borel. This uses the existing
measurable orthonormality predicate and standard product/pi instances. -/
theorem standardBorel_idealAccidentSample (d T N : ℕ) :
    StandardBorelSpace (IdealAccidentSample d T N) := by
  let : StandardBorelSpace {U : Fin T → Point d // Orthonormal ℝ U} :=
    (measurableSet_orthonormal_fin d T).standardBorel
  infer_instance

/-- The concrete Haar and original `N`-Gaussian-tape completion tail, with
the sample-space standard Borel obligation discharged and private `r` fixed.
The only stochastic inputs are the two actual indicator mean bounds. -/
theorem idealCompleted_Haar_tail_of_cumulative_half
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hTd : T ≤ d)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (m : ℕ) (hm : 0 < m) (hbudget : 4 * N ≤ T * m)
    (hfirst : (∫ z : IdealAccidentSample d T N,
      idealShortStageIndicator hT z.1.1 A r z.2 a m 0
        ∂(preselectedOrthonormalFrameLaw d T hTd).prod
          (Measure.pi (fun _ : Fin N => standardGaussianLaw d))) ≤ (1 : ℝ) / 2)
    (hhalf : ∀ i < T - 1,
      ∀ᵐ z : IdealAccidentSample d T N ∂(preselectedOrthonormalFrameLaw d T hTd).prod
        (Measure.pi (fun _ : Fin N => standardGaussianLaw d)),
        condExp (idealStageFiltration hT A r a
            (fun z : IdealAccidentSample d T N => z.1.1) Prod.snd
            (measurable_subtype_coe.comp measurable_fst) measurable_snd i)
          ((preselectedOrthonormalFrameLaw d T hTd).prod
            (Measure.pi (fun _ : Fin N => standardGaussianLaw d)))
          (fun z => idealShortStageIndicator hT z.1.1 A r z.2 a m (i + 1)) z ≤ (1 : ℝ) / 2) :
    (((preselectedOrthonormalFrameLaw d T hTd).prod
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d))).real
      {z : IdealAccidentSample d T N | idealCompleted hT z.1.1 A r z.2 a}) ≤
      Real.exp (-(T : ℝ) / 32) := by
  let : StandardBorelSpace (IdealAccidentSample d T N) := standardBorel_idealAccidentSample d T N
  exact idealCompleted_tail_of_cumulative_half
    ((preselectedOrthonormalFrameLaw d T hTd).prod
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d)))
    hT A r a (fun z : IdealAccidentSample d T N => z.1.1) Prod.snd
    (measurable_subtype_coe.comp measurable_fst) measurable_snd
    m hm hbudget hfirst hhalf

end

end HeavyTailedNoise
