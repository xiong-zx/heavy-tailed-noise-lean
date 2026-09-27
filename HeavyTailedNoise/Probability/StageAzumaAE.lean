import HeavyTailedNoise.Probability.StageAzuma

/-!
An a.e. version of the stage-count domination step. Conditional expectations
and conditional stage-success bounds are naturally valid a.e.; a pointwise
domination premise is unnecessarily strong.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem stage_count_tail_of_subgaussian_domination_ae
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X Y : ℕ → Ω → ℝ) (T : ℕ)
    (h_adapted : StronglyAdapted ℱ Y)
    (h₀ : HasSubgaussianMGF (Y 0) 1 μ)
    (h_cond : ∀ i < T - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) 1 μ)
    (h_dom : ∀ i < T, ∀ᵐ ω ∂μ, X i ω ≤ (1 : ℝ) / 2 + Y i ω) :
    μ.real {ω | 3 * (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, X i ω} ≤
      Real.exp (-(T : ℝ) / 32) := by
  have hterms :
      ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range T,
        X i ω ≤ (1 : ℝ) / 2 + Y i ω := by
    apply (Finset.eventually_all (Finset.range T)).2
    intro i hi
    exact h_dom i (Finset.mem_range.mp hi)
  have hsum : ∀ᵐ ω ∂μ,
      (∑ i ∈ Finset.range T, X i ω) ≤
        (T : ℝ) / 2 + ∑ i ∈ Finset.range T, Y i ω := by
    filter_upwards [hterms] with ω hω
    calc
      (∑ i ∈ Finset.range T, X i ω) ≤
          ∑ i ∈ Finset.range T, ((1 : ℝ) / 2 + Y i ω) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hω i hi
      _ = (T : ℝ) / 2 + ∑ i ∈ Finset.range T, Y i ω := by
        simp [Finset.sum_add_distrib, div_eq_mul_inv]
  have hsubset :
      {ω | 3 * (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, X i ω} ≤ᵐ[μ]
      {ω | (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, Y i ω} := by
    filter_upwards [hsum] with ω hsumω
    intro hω
    linarith
  have hmeasure :
      μ.real {ω | 3 * (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, X i ω} ≤
      μ.real {ω | (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, Y i ω} := by
    exact ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsubset)
  exact hmeasure.trans (centered_stage_sum_tail μ ℱ Y T h_adapted h₀ h_cond)

/-- A conditional success probability bound supplies the a.e. pointwise
domination for the centered indicator, without choosing versions globally. -/
theorem stage_indicator_ae_domination_of_condExp_half
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ)
    (hhalf : ∀ i < T, ∀ᵐ ω ∂μ, μ[X i | ℱ i] ω ≤ (1 : ℝ) / 2) :
    ∀ i < T, ∀ᵐ ω ∂μ,
      X i ω ≤ (1 : ℝ) / 2 + (X i ω - μ[X i | ℱ i] ω) := by
  intro i hi
  filter_upwards [hhalf i hi] with ω hω
  linarith

end

end HeavyTailedNoise
