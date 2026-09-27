import HeavyTailedNoise.Probability.GaussianKLMixture
import HeavyTailedNoise.Probability.StageCounting
import HeavyTailedNoise.Probability.StageAzuma
import HeavyTailedNoise.Probability.RiskThreshold
import HeavyTailedNoise.Model.Distributional

/-!
Conditional integration of the fixed-response KL, pinhole, stage count,
concentration, and expected-risk steps. The actual stopped Haar construction
must still identify the conditional prior and response kernels, verify the
reference cap estimate, and supply the stopped-history centering/coupling
premises below. Private randomness is fixed during the standard-Borel
concentration argument and may then be averaged over an arbitrary seed space.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

namespace HeavyTailedNoise

/-- A uniform `n₀`-response KL bound, a fixed independent reference, and a
uniform cap estimate make every conditional short-stage event at most one half.
The prior, kernel, and reference may depend on a stopped prefix `s`; `n₀` is a
deterministic response cap. -/
theorem stage_short_probability_half
    {Prefix Direction History : Type*}
    [MeasurableSpace Direction] [MeasurableSpace History]
    [MeasurableSpace.CountableOrCountablyGenerated Direction History]
    (T n₀ : ℕ)
    (π : ℕ → Prefix → Measure Direction)
    (K : ℕ → Prefix → Kernel Direction History)
    (R : ℕ → Prefix → Measure History)
    (E : ℕ → Prefix → Set (Direction × History))
    (hπ : ∀ i s, IsProbabilityMeasure (π i s))
    (hK : ∀ i s, IsMarkovKernel (K i s))
    (hR : ∀ i s, IsProbabilityMeasure (R i s))
    (hE : ∀ i < T, ∀ s, MeasurableSet (E i s))
    (c : ENNReal)
    (hconditionalKL : ∀ i < T, ∀ s θ,
      klDiv (K i s θ) (R i s) ≤ (n₀ : ENNReal) * c)
    (I qcap : ℝ) (hI : 0 ≤ I)
    (hKLbudget : (n₀ : ENNReal) * c ≤ ENNReal.ofReal I)
    (hqcap₀ : 0 < qcap) (hqcap₁ : qcap < 1)
    (hcap : ∀ i < T, ∀ s,
      (((π i s).prod (R i s)) (E i s)).toReal ≤ qcap)
    (hlogBudget : I + Real.log 2 ≤
      (1 / 2 : ℝ) * Real.log qcap⁻¹) :
    ∀ i < T, ∀ s,
      (((π i s) ⊗ₘ K i s) (E i s)).toReal ≤ 1 / 2 := by
  intro i hi s
  letI : IsProbabilityMeasure (π i s) := hπ i s
  letI : IsMarkovKernel (K i s) := hK i s
  letI : IsProbabilityMeasure (R i s) := hR i s
  have hJointKL : klDiv ((π i s) ⊗ₘ K i s) ((π i s).prod (R i s)) ≤
      ENNReal.ofReal I := by
    exact (mixture_reference_klDiv_le (π i s) (K i s) (R i s)
      ((n₀ : ENNReal) * c) (hconditionalKL i hi s)).trans hKLbudget
  exact pinhole_half_of_referenceKL_cap_or_zero
    ((π i s) ⊗ₘ K i s) ((π i s).prod (R i s))
    (E i s) (hE i hi s) I qcap hI hqcap₀ hqcap₁
    (hcap i hi s) hJointKL hlogBudget

/-- Under a completed-run budget, deterministic stage counting forces the
real short-stage indicator sum above three quarters of the stage count. -/
theorem completion_forces_short_indicator_sum
    {Ω : Type*} (T n₀ : ℕ) (hn₀ : 0 < n₀)
    (length : Ω → Fin T → ℕ) (X : ℕ → Ω → ℝ)
    (complete : Set Ω)
    (hbudget : ∀ ω ∈ complete,
      4 * (∑ j, length ω j) ≤ T * n₀)
    (hindicator : ∀ ω,
      (∑ i ∈ Finset.range T, X i ω) =
        ((Finset.univ.filter fun j : Fin T => length ω j ≤ n₀).card : ℝ)) :
    complete ⊆
      {ω | 3 * (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, X i ω} := by
  intro ω hω
  have hcount := many_short_stages_of_budget hn₀ (length ω) (hbudget ω hω)
  have hcountReal : 3 * (T : ℝ) ≤
      4 * ((Finset.univ.filter fun j : Fin T => length ω j ≤ n₀).card : ℝ) := by
    exact_mod_cast hcount
  change 3 * (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, X i ω
  rw [hindicator ω]
  linarith

/-- A pointwise stopped-prefix pinhole bound yields the domination used by
the finite-horizon Azuma theorem. `hcenter` is the exact conditional-mean
identification still owed by the concrete stopped protocol; it is stated for
each fixed private tape, so `Ω` need not contain arbitrary private seeds. -/
theorem completion_tail_of_stage_pinhole
    {Ω Prefix EventSpace : Type*}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    [MeasurableSpace EventSpace]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (T n₀ : ℕ) (hn₀ : 0 < n₀)
    (length : Ω → Fin T → ℕ) (X Y : ℕ → Ω → ℝ)
    (complete : Set Ω)
    (hbudget : ∀ ω ∈ complete,
      4 * (∑ j, length ω j) ≤ T * n₀)
    (hindicator : ∀ ω,
      (∑ i ∈ Finset.range T, X i ω) =
        ((Finset.univ.filter fun j : Fin T => length ω j ≤ n₀).card : ℝ))
    (Pstage : ℕ → Prefix → Measure EventSpace)
    (Estage : ℕ → Prefix → Set EventSpace)
    (stoppedPrefix : ℕ → Ω → Prefix)
    (hshort : ∀ i < T, ∀ s,
      (Pstage i s (Estage i s)).toReal ≤ 1 / 2)
    (hcenter : ∀ i < T, ∀ ω,
      X i ω ≤ (Pstage i (stoppedPrefix i ω)
        (Estage i (stoppedPrefix i ω))).toReal + Y i ω)
    (h_adapted : StronglyAdapted ℱ Y)
    (h₀ : HasSubgaussianMGF (Y 0) 1 μ)
    (h_cond : ∀ i < T - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) 1 μ) :
    μ.real complete ≤ Real.exp (-(T : ℝ) / 32) := by
  have hdom : ∀ i < T, ∀ ω,
      X i ω ≤ (1 : ℝ) / 2 + Y i ω := by
    intro i hi ω
    exact (hcenter i hi ω).trans
      (add_le_add_left (hshort i hi (stoppedPrefix i ω)) _)
  exact (measureReal_mono
    (completion_forces_short_indicator_sum T n₀ hn₀ length X complete
      hbudget hindicator)).trans
    (stage_count_tail_of_subgaussian_domination μ ℱ X Y T
      h_adapted h₀ h_cond hdom)

/-- Direct composition of the fixed-`n₀` mixture/pinhole bound with
deterministic stage counting and Azuma for a fixed private tape. The actual
stopped-prefix construction must provide `hconditionalKL`, `hcap`, and
`hcenter`; no expected-stopping-time budget is used. -/
theorem completion_tail_of_stage_reference
    {Ω Prefix Direction History : Type*}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    [MeasurableSpace Direction] [MeasurableSpace History]
    [MeasurableSpace.CountableOrCountablyGenerated Direction History]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (T n₀ : ℕ) (hn₀ : 0 < n₀)
    (length : Ω → Fin T → ℕ) (X Y : ℕ → Ω → ℝ)
    (complete : Set Ω)
    (hbudget : ∀ ω ∈ complete,
      4 * (∑ j, length ω j) ≤ T * n₀)
    (hindicator : ∀ ω,
      (∑ i ∈ Finset.range T, X i ω) =
        ((Finset.univ.filter fun j : Fin T => length ω j ≤ n₀).card : ℝ))
    (π : ℕ → Prefix → Measure Direction)
    (K : ℕ → Prefix → Kernel Direction History)
    (R : ℕ → Prefix → Measure History)
    (E : ℕ → Prefix → Set (Direction × History))
    (hπ : ∀ i s, IsProbabilityMeasure (π i s))
    (hK : ∀ i s, IsMarkovKernel (K i s))
    (hR : ∀ i s, IsProbabilityMeasure (R i s))
    (hE : ∀ i < T, ∀ s, MeasurableSet (E i s))
    (c : ENNReal)
    (hconditionalKL : ∀ i < T, ∀ s θ,
      klDiv (K i s θ) (R i s) ≤ (n₀ : ENNReal) * c)
    (I qcap : ℝ) (hI : 0 ≤ I)
    (hKLbudget : (n₀ : ENNReal) * c ≤ ENNReal.ofReal I)
    (hqcap₀ : 0 < qcap) (hqcap₁ : qcap < 1)
    (hcap : ∀ i < T, ∀ s,
      (((π i s).prod (R i s)) (E i s)).toReal ≤ qcap)
    (hlogBudget : I + Real.log 2 ≤
      (1 / 2 : ℝ) * Real.log qcap⁻¹)
    (stoppedPrefix : ℕ → Ω → Prefix)
    (hcenter : ∀ i < T, ∀ ω,
      X i ω ≤ (((π i (stoppedPrefix i ω)) ⊗ₘ
        K i (stoppedPrefix i ω))
        (E i (stoppedPrefix i ω))).toReal + Y i ω)
    (h_adapted : StronglyAdapted ℱ Y)
    (h₀ : HasSubgaussianMGF (Y 0) 1 μ)
    (h_cond : ∀ i < T - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) 1 μ) :
    μ.real complete ≤ Real.exp (-(T : ℝ) / 32) := by
  have hshort := stage_short_probability_half T n₀ π K R E
    hπ hK hR hE c hconditionalKL I qcap hI hKLbudget
    hqcap₀ hqcap₁ hcap hlogBudget
  exact completion_tail_of_stage_pinhole μ ℱ T n₀ hn₀
    length X Y complete hbudget hindicator
    (fun i s => (π i s) ⊗ₘ K i s) E stoppedPrefix
    hshort hcenter h_adapted h₀ h_cond

/-- Concentration can be proved after fixing each private tape and then
averaged over any private seed law. In particular, this statement imposes no
standard-Borel condition on the private seed space. -/
theorem private_averaged_completion_tail
    {Private Ω : Type*}
    [MeasurableSpace Private] [MeasurableSpace Ω]
    (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (law : Private → Measure Ω)
    (hLawProb : ∀ r, IsProbabilityMeasure (law r))
    (complete : Private → Set Ω) (T : ℕ)
    (hpoint : ∀ r,
      (law r).real (complete r) ≤ Real.exp (-(T : ℝ) / 32)) :
    (∫⁻ r, law r (complete r) ∂ρ) ≤
      ENNReal.ofReal (Real.exp (-(T : ℝ) / 32)) := by
  apply private_randomized_event_bound ρ law complete _
  intro r
  letI : IsProbabilityMeasure (law r) := hLawProb r
  rw [← ENNReal.ofReal_toReal (measure_ne_top (law r) (complete r))]
  exact ENNReal.ofReal_le_ofReal (hpoint r)

/-- Identify the outer private-seed average with the actual full joint law.
The equality is a measurable-kernel/Tonelli obligation of the stopped
protocol, rather than a restriction on the private randomness space. -/
theorem joint_completion_tail_of_private_average
    {Private Ω Joint : Type*}
    [MeasurableSpace Private] [MeasurableSpace Ω]
    [MeasurableSpace Joint]
    (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (law : Private → Measure Ω)
    (hLawProb : ∀ r, IsProbabilityMeasure (law r))
    (complete : Private → Set Ω) (T : ℕ)
    (hpoint : ∀ r,
      (law r).real (complete r) ≤ Real.exp (-(T : ℝ) / 32))
    (μJoint : Measure Joint) (completeJoint : Set Joint)
    (hJointLaw : μJoint completeJoint =
      ∫⁻ r, law r (complete r) ∂ρ) :
    μJoint.real completeJoint ≤ Real.exp (-(T : ℝ) / 32) := by
  have hbound := private_averaged_completion_tail ρ law hLawProb complete T hpoint
  rw [measureReal_def, hJointLaw]
  have hfinite : ENNReal.ofReal (Real.exp (-(T : ℝ) / 32)) ≠ ∞ := by simp
  have hreal := ENNReal.toReal_mono hfinite hbound
  simpa [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))] using hreal

/-- A concentration bound for completing every stage, together with a bound
on exceptional trajectories, gives a strict fixed-prior average-risk bound.
`hRiskIdentity` is the exact Tonelli/coupling identification between the
joint trajectory law and the original algorithm's risk. -/
theorem fixed_prior_averageRisk_of_stage_events
    {Ω Frame Seed Private : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Frame]
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {d N : ℕ} {p q Δ σ Lbar : ℝ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (μFrame : Measure Frame) [IsProbabilityMeasure μFrame]
    (instanceAt : Frame → Admissible d Seed p q Δ σ Lbar)
    (A : RandomAlgorithm d N Private)
    (f : Ω → ENNReal) (hf : Measurable f)
    (a : ENNReal) (ha0 : a ≠ 0) (hatop : a ≠ ∞)
    (T : ℕ) (complete accident : Set Ω) (δ : ℝ)
    (hcomplete : μ.real complete ≤ Real.exp (-(T : ℝ) / 32))
    (haccident : μ.real accident ≤ δ)
    (hsmall : Real.exp (-(T : ℝ) / 32) + δ < 1 / 2)
    (hlow : {ω | f ω < a} ⊆ complete ∪ accident)
    (hRiskIdentity :
      (∫⁻ ω, f ω ∂μ) = ∫⁻ U, risk (instanceAt U) A ∂μFrame) :
    a * (1 / 2 : ENNReal) <
      ∫⁻ U, risk (instanceAt U) A ∂μFrame := by
  have hlowMeas : MeasurableSet {ω | f ω < a} :=
    measurableSet_lt hf measurable_const
  have hlowProb : μ.real {ω | f ω < a} < 1 / 2 := by
    calc
      μ.real {ω | f ω < a} ≤ μ.real (complete ∪ accident) :=
        measureReal_mono hlow
      _ ≤ μ.real complete + μ.real accident :=
        measureReal_union_le _ _
      _ ≤ Real.exp (-(T : ℝ) / 32) + δ :=
        add_le_add hcomplete haccident
      _ < 1 / 2 := hsmall
  have hgoodSet : {ω | a ≤ f ω} = {ω | f ω < a}ᶜ := by
    ext ω
    simp
  have hgoodReal : (1 / 2 : ℝ) < μ.real {ω | a ≤ f ω} := by
    rw [hgoodSet, probReal_compl_eq_one_sub hlowMeas]
    linarith
  have hgood : (1 / 2 : ENNReal) < μ {ω | a ≤ f ω} := by
    apply (ENNReal.toReal_lt_toReal (by norm_num)
      (measure_ne_top μ {ω | a ≤ f ω})).mp
    simpa [measureReal_def] using hgoodReal
  rw [← hRiskIdentity]
  exact lintegral_gt_half_threshold μ f hf.aemeasurable ha0 hatop hgood

/-- Fixed-prior average risk for an arbitrary private-randomized algorithm,
using per-private-tape stage concentration. The private tape is integrated
under `A.privateLaw`; no regularity assumption is made on `Private` beyond its
measurable space. -/
theorem fixed_prior_averageRisk_of_private_stage_tails
    {Private Ω Joint Frame Seed : Type*}
    [MeasurableSpace Private] [MeasurableSpace Ω]
    [MeasurableSpace Joint] [MeasurableSpace Frame]
    [MeasurableSpace Seed]
    {d N : ℕ} {p q Δ σ Lbar : ℝ}
    (μFrame : Measure Frame) [IsProbabilityMeasure μFrame]
    (instanceAt : Frame → Admissible d Seed p q Δ σ Lbar)
    (A : RandomAlgorithm d N Private)
    (law : Private → Measure Ω)
    (hLawProb : ∀ r, IsProbabilityMeasure (law r))
    (complete : Private → Set Ω) (T : ℕ)
    (hpoint : ∀ r,
      (law r).real (complete r) ≤ Real.exp (-(T : ℝ) / 32))
    (μJoint : Measure Joint) [IsProbabilityMeasure μJoint]
    (completeJoint accident : Set Joint)
    (hJointLaw : μJoint completeJoint =
      ∫⁻ r, law r (complete r) ∂A.privateLaw)
    (f : Joint → ENNReal) (hf : Measurable f)
    (a : ENNReal) (ha0 : a ≠ 0) (hatop : a ≠ ∞)
    (δ : ℝ) (haccident : μJoint.real accident ≤ δ)
    (hsmall : Real.exp (-(T : ℝ) / 32) + δ < 1 / 2)
    (hlow : {ω | f ω < a} ⊆ completeJoint ∪ accident)
    (hRiskIdentity :
      (∫⁻ ω, f ω ∂μJoint) =
        ∫⁻ U, risk (instanceAt U) A ∂μFrame) :
    a * (1 / 2 : ENNReal) <
      ∫⁻ U, risk (instanceAt U) A ∂μFrame := by
  letI : IsProbabilityMeasure A.privateLaw := A.private_probability
  have hcomplete := joint_completion_tail_of_private_average
    A.privateLaw law hLawProb complete T hpoint μJoint completeJoint hJointLaw
  exact fixed_prior_averageRisk_of_stage_events μJoint μFrame instanceAt A
    f hf a ha0 hatop T completeJoint accident δ hcomplete
    haccident hsmall hlow hRiskIdentity

/-- Once the threshold is calibrated to `ε`, the same fixed prior contains a
deterministic orientation that is bad for the given full-history randomized
algorithm. The orientation is selected after the algorithm rule, not after its
private seed or oracle samples. -/
theorem bad_orientation_of_stage_average
    {Frame Seed Private : Type*}
    [MeasurableSpace Frame] [MeasurableSpace Seed]
    [MeasurableSpace Private]
    {d N : ℕ} {p q Δ σ Lbar ε : ℝ}
    (μFrame : Measure Frame) [IsProbabilityMeasure μFrame]
    (instanceAt : Frame → Admissible d Seed p q Δ σ Lbar)
    (A : RandomAlgorithm d N Private)
    (a : ENNReal) (hscale : ENNReal.ofReal ε = a * (1 / 2 : ENNReal))
    (haverage : a * (1 / 2 : ENNReal) <
      ∫⁻ U, risk (instanceAt U) A ∂μFrame) :
    ∃ U : Frame, ENNReal.ofReal ε < risk (instanceAt U) A := by
  apply bad_orientation_of_average μFrame instanceAt A
  simpa [hscale] using haverage

end HeavyTailedNoise
