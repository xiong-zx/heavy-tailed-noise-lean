import HeavyTailedNoise.Model.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
A finite-horizon Azuma estimate and the conditional Hoeffding bridge for bounded increments.
The concentration theorems use mathlib's `StandardBorelSpace` assumption. Applying them to
arbitrary private-randomness spaces requires a separate conditioning argument.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace HeavyTailedNoise

theorem centered_stage_sum_tail
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ) (T : ℕ)
    (h_adapted : StronglyAdapted ℱ Y)
    (h₀ : HasSubgaussianMGF (Y 0) 1 μ)
    (h_cond : ∀ i < T - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) 1 μ) :
    μ.real {ω | (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, Y i ω} ≤
      Real.exp (-(T : ℝ) / 32) := by
  have htail := measure_sum_ge_le_of_hasCondSubgaussianMGF
    (Y := Y) (cY := fun _ => 1) (ℱ := ℱ)
    h_adapted h₀ T h_cond (ε := (T : ℝ) / 4) (by positivity)
  have hs : (∑ i ∈ Finset.range T, (1 : ℝ≥0)) = (T : ℝ≥0) := by simp
  rw [hs] at htail
  by_cases hT : T = 0
  · subst T
    simpa using htail
  · have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT
    have hexp : -((T : ℝ) / 4) ^ 2 / (2 * (T : ℝ)) = -(T : ℝ) / 32 := by
      field_simp
      ring
    simpa [hexp] using htail

/-- A stage count dominated by centered subgaussian increments inherits the Azuma tail. -/
theorem stage_count_tail_of_subgaussian_domination
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X Y : ℕ → Ω → ℝ) (T : ℕ)
    (h_adapted : StronglyAdapted ℱ Y)
    (h₀ : HasSubgaussianMGF (Y 0) 1 μ)
    (h_cond : ∀ i < T - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) 1 μ)
    (h_dom : ∀ i < T, ∀ ω, X i ω ≤ (1 : ℝ) / 2 + Y i ω) :
    μ.real {ω | 3 * (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, X i ω} ≤
      Real.exp (-(T : ℝ) / 32) := by
  have hsum (ω : Ω) :
      (∑ i ∈ Finset.range T, X i ω) ≤
        (T : ℝ) / 2 + ∑ i ∈ Finset.range T, Y i ω := by
    calc
      (∑ i ∈ Finset.range T, X i ω) ≤
          ∑ i ∈ Finset.range T, ((1 : ℝ) / 2 + Y i ω) := by
        apply Finset.sum_le_sum
        intro i hi
        exact h_dom i (Finset.mem_range.mp hi) ω
      _ = (T : ℝ) / 2 + ∑ i ∈ Finset.range T, Y i ω := by
        simp [Finset.sum_add_distrib, div_eq_mul_inv]
  have hsubset :
      {ω | 3 * (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, X i ω} ⊆
      {ω | (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, Y i ω} := by
    intro ω hω
    dsimp at hω ⊢
    linarith [hsum ω]
  exact (measureReal_mono hsubset).trans
    (centered_stage_sum_tail μ ℱ Y T h_adapted h₀ h_cond)


/-- Centering a `[0,1]` random variable by its conditional mean yields a
conditionally subgaussian increment. The parameter `1` uses the coarse
interval `[-1,1]`; no fiberwise constancy of the conditional mean is needed. -/
theorem bounded_centered_hasCondSubgaussianMGF
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (X : Ω → ℝ)
    (hX : @Measurable Ω ℝ mΩ _ X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) :
    HasCondSubgaussianMGF m hm
      (fun ω => X ω - μ[X | m] ω) 1 μ := by
  letI : MeasurableSpace Ω := mΩ
  let M : Ω → ℝ := μ[X | m]
  let Y : Ω → ℝ := fun ω => X ω - M ω
  have hXaem : AEMeasurable[mΩ] X μ := hX.aemeasurable (μ := μ)
  have hXint : Integrable X μ := Integrable.of_mem_Icc 0 1 hXaem hb
  have hMstrong : StronglyMeasurable[m] M := stronglyMeasurable_condExp
  have hMambient : @Measurable Ω ℝ mΩ _ M := (hMstrong.mono hm).measurable
  have hYmeas : @Measurable Ω ℝ mΩ _ Y := hX.sub hMambient
  have hMint : Integrable M μ := integrable_condExp
  have hYint : Integrable Y μ := hXint.sub hMint
  have hM0 : ∀ᵐ ω ∂μ, 0 ≤ M ω :=
    condExp_nonneg (hb.mono fun ω hω => hω.1)
  have hM1 : ∀ᵐ ω ∂μ, M ω ≤ 1 :=
    condExp_le_nonneg_const (by norm_num) (hb.mono fun ω hω => hω.2)
  have hYbound : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [hb, hM0, hM1] with ω hXω hM0ω hM1ω
    change -1 ≤ X ω - M ω ∧ X ω - M ω ≤ 1
    rcases hXω with ⟨hX0, hX1⟩
    constructor <;> linarith
  have hMcond : μ[M | m] = M :=
    condExp_of_stronglyMeasurable hm hMstrong hMint
  have hYcond : μ[Y | m] =ᵐ[μ] (fun _ => 0) := by
    have hsub := condExp_sub hXint hMint m
    filter_upwards [hsub] with ω hsubω
    change μ[X - M | m] ω = 0
    rw [hsubω, hMcond]
    simp [M]
  have hYcondTrim : μ[Y | m] =ᵐ[μ.trim hm] (fun _ => 0) :=
    (stronglyMeasurable_condExp.ae_eq_trim_iff hm stronglyMeasurable_zero).2 hYcond
  have hYkernelMean :
      ∀ᵐ ω' ∂μ.trim hm, (∫ ω, Y ω ∂condExpKernel μ m ω') = 0 := by
    filter_upwards [condExp_ae_eq_trim_integral_condExpKernel hm hYint,
      hYcondTrim] with ω' heq hz
    rw [← heq, hz]
  have hYkernelBound :
      ∀ᵐ ω' ∂μ.trim hm, ∀ᵐ ω ∂condExpKernel μ m ω',
        Y ω ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← condExpKernel_comp_trim (μ := μ) (m := m) hm] at hYbound
    exact Measure.ae_ae_of_ae_comp hYbound
  change Kernel.HasSubgaussianMGF Y 1 (condExpKernel μ m) (μ.trim hm)
  refine ⟨?_, ?_⟩
  · intro t
    rw [condExpKernel_comp_trim hm]
    have hYaem : AEMeasurable[mΩ] Y μ := hYmeas.aemeasurable (μ := μ)
    exact integrable_exp_mul_of_mem_Icc hYaem hYbound
  · filter_upwards [hYkernelBound, hYkernelMean] with ω' hbd hmean
    intro t
    have hsg : HasSubgaussianMGF Y 1 (condExpKernel μ m ω') := by
      have hYaem : AEMeasurable[mΩ] Y (condExpKernel μ m ω') :=
        hYmeas.aemeasurable (μ := condExpKernel μ m ω')
      have hcoef : ((‖(1 : ℝ) - (-1 : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) = 1 := by
        norm_num
      simpa only [hcoef] using hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (X := Y) (a := (-1 : ℝ)) (b := (1 : ℝ))
        hYaem hbd hmean
    exact hsg.mgf_le t

end HeavyTailedNoise
