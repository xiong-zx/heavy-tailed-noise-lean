import HeavyTailedNoise.Probability.StageAzumaAE

/-!
Construct the centered increments required by the existing Azuma interface.
The initial term is centered by its ordinary expectation. A later term is
centered by its expectation conditional on the *previous* filtration level.
Centering an already adapted term by its own filtration level would not give
the required stage-count domination.

All success-probability bounds are explicit theorem parameters. The ordinary
centering, adaptedness, and domination lemmas do not require a standard Borel
space. Only the conditional-MGF/Azuma interfaces inherit mathlib's assumption
on the probability space `Ω`. In an application the private tape can be fixed
outside `Ω`; no standard Borel assumption is imposed on its measurable space.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- The one authoritative centered process for the Azuma indexing convention.
`X 0` is the first stage indicator; `X (i+1)` is observed at level `ℱ (i+1)`
and its predictable mean is taken at level `ℱ i`. -/
def stageBernoulliCentered
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun ω => X 0 ω - ∫ η, X 0 η ∂μ
  | i + 1 => fun ω => X (i + 1) ω - μ[X (i + 1) | ℱ i] ω

/-- A conditional mean bound supplies the initial ordinary mean bound after
integration. This lemma allows an arbitrary initial conditioning sigma-algebra.
-/
theorem integral_le_half_of_condExp_le_half
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (X : Ω → ℝ)
    (hhalf : ∀ᵐ ω ∂μ, μ[X | m] ω ≤ (1 : ℝ) / 2) :
    (∫ ω, X ω ∂μ) ≤ (1 : ℝ) / 2 := by
  calc
    (∫ ω, X ω ∂μ) = ∫ ω, μ[X | m] ω ∂μ := (integral_condExp hm).symm
    _ ≤ ∫ _ : Ω, (1 : ℝ) / 2 ∂μ :=
      integral_mono_ae integrable_condExp (integrable_const _) hhalf
    _ = (1 : ℝ) / 2 := by simp

/-- Ordinary centering of a `[0,1]` variable is subgaussian with the coarse
parameter `1`. No topological assumption on the probability space is needed.
-/
theorem bounded_centered_hasSubgaussianMGF_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) :
    HasSubgaussianMGF (fun ω => X ω - ∫ η, X η ∂μ) 1 μ := by
  have hwide : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [hb] with ω hω
    exact ⟨by linarith [hω.1], hω.2⟩
  have hcoef : ((‖(1 : ℝ) - (-1 : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) = 1 := by
    norm_num
  simpa only [hcoef] using
    hasSubgaussianMGF_of_mem_Icc hX hwide

/-- Subtracting the predictable means preserves strong adaptedness, including
the separately centered initial term. -/
theorem stageBernoulliCentered_stronglyAdapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (hX : StronglyAdapted ℱ X) :
    StronglyAdapted ℱ (stageBernoulliCentered μ ℱ X) := by
  intro i
  cases i with
  | zero =>
    exact (hX 0).sub stronglyMeasurable_const
  | succ i =>
    have hM : StronglyMeasurable[ℱ i] (μ[X (i + 1) | ℱ i]) :=
      stronglyMeasurable_condExp
    exact (hX (i + 1)).sub (hM.mono (ℱ.mono (Nat.le_succ i)))

/-- The first centered term supplies the unconditional MGF input of Azuma. -/
theorem stageBernoulliCentered_initial_subgaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (hX : StronglyAdapted ℱ X)
    (hb : ∀ᵐ ω ∂μ, X 0 ω ∈ Set.Icc (0 : ℝ) 1) :
    HasSubgaussianMGF (stageBernoulliCentered μ ℱ X 0) 1 μ := by
  exact bounded_centered_hasSubgaussianMGF_one μ (X 0)
    (hX.stronglyMeasurable.measurable.aemeasurable) hb

/-- Later centered terms supply conditional MGF inputs at the preceding
filtration level. The existing checked conditional Hoeffding bridge is reused.
-/
theorem stageBernoulliCentered_successor_condSubgaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (hX : StronglyAdapted ℱ X) (i : ℕ)
    (hb : ∀ᵐ ω ∂μ, X (i + 1) ω ∈ Set.Icc (0 : ℝ) 1) :
    HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
      (stageBernoulliCentered μ ℱ X (i + 1)) 1 μ := by
  exact bounded_centered_hasCondSubgaussianMGF μ (ℱ i) (ℱ.le i)
    (X (i + 1)) (hX.stronglyMeasurable.measurable) hb

/-- The exact mean assumptions needed by the Azuma indexing imply a.e.
stage-count domination. Conditional expectation versions need not agree
pointwise on null sets. -/
theorem stageBernoulliCentered_ae_domination
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ)
    (hfirst : (∫ ω, X 0 ω ∂μ) ≤ (1 : ℝ) / 2)
    (hhalf : ∀ i < T - 1,
      ∀ᵐ ω ∂μ, μ[X (i + 1) | ℱ i] ω ≤ (1 : ℝ) / 2) :
    ∀ i < T, ∀ᵐ ω ∂μ,
      X i ω ≤ (1 : ℝ) / 2 + stageBernoulliCentered μ ℱ X i ω := by
  intro i hi
  cases i with
  | zero =>
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp [stageBernoulliCentered]
      linarith)
  | succ i =>
    filter_upwards [hhalf i (by omega)] with ω hω
    dsimp [stageBernoulliCentered]
    linarith

/-- All inputs of `stage_count_tail_of_subgaussian_domination_ae` are
constructed from an adapted bounded process and its explicit mean bounds.
-/
theorem stageBernoulliCentered_azuma_inputs
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ)
    (hX : StronglyAdapted ℱ X)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hfirst : (∫ ω, X 0 ω ∂μ) ≤ (1 : ℝ) / 2)
    (hhalf : ∀ i < T - 1,
      ∀ᵐ ω ∂μ, μ[X (i + 1) | ℱ i] ω ≤ (1 : ℝ) / 2) :
    StronglyAdapted ℱ (stageBernoulliCentered μ ℱ X) ∧
    HasSubgaussianMGF (stageBernoulliCentered μ ℱ X 0) 1 μ ∧
    (∀ i < T - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
      (stageBernoulliCentered μ ℱ X (i + 1)) 1 μ) ∧
    (∀ i < T, ∀ᵐ ω ∂μ,
      X i ω ≤ (1 : ℝ) / 2 + stageBernoulliCentered μ ℱ X i ω) := by
  exact ⟨stageBernoulliCentered_stronglyAdapted μ ℱ X hX,
    stageBernoulliCentered_initial_subgaussian μ ℱ X hX (hb 0),
    fun i _ => stageBernoulliCentered_successor_condSubgaussian μ ℱ X hX i (hb _),
    stageBernoulliCentered_ae_domination μ ℱ X T hfirst hhalf⟩

/-- An adapted `{0,1}` stage-indicator process inherits the exact existing
Azuma tail, once its initial and subsequent conditional means are bounded.
These bounds are supplied hypotheses, not claims about the actual experiment.
-/
theorem stage_indicator_count_tail_of_condExp_half
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ)
    (hX : StronglyAdapted ℱ X)
    (hind : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 ∨ X i ω = 1)
    (hfirst : (∫ ω, X 0 ω ∂μ) ≤ (1 : ℝ) / 2)
    (hhalf : ∀ i < T - 1,
      ∀ᵐ ω ∂μ, μ[X (i + 1) | ℱ i] ω ≤ (1 : ℝ) / 2) :
    μ.real {ω | 3 * (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, X i ω} ≤
      Real.exp (-(T : ℝ) / 32) := by
  have hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    filter_upwards [hind i] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  obtain ⟨hadapt, hzero, hcond, hdom⟩ :=
    stageBernoulliCentered_azuma_inputs μ ℱ X T hX hb hfirst hhalf
  exact stage_count_tail_of_subgaussian_domination_ae
    μ ℱ X (stageBernoulliCentered μ ℱ X) T hadapt hzero hcond hdom

end

end HeavyTailedNoise
