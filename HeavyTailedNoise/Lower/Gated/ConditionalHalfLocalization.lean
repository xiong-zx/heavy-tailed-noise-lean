import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
Transfer from a latest-observation sigma-algebra to a cumulative one when
their measurable sets have the same trace on an active event. An integrable
variable supported on that event has identical conditional expectations for
the two sigma-algebras.

The trace-reconstruction property is an explicit theorem parameter. The
ambient space is arbitrary and the measure is finite; neither the ambient
space nor any private-randomness component needs to be standard Borel.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

/-- Integrals of an a.e. active-supported function can be localized to the
intersection with the active event. -/
theorem setIntegral_eq_active_intersection
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Set Ω) (hB : MeasurableSet B) (X : Ω → ℝ)
    (hoff : ∀ᵐ ω ∂μ, ω ∉ A → X ω = 0) :
    (∫ ω in B, X ω ∂μ) = ∫ ω in B ∩ A, X ω ∂μ := by
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hB.nullMeasurableSet
    Set.inter_subset_left
  filter_upwards [hoff] with ω hω hdiff
  exact hω (fun hA => hdiff.2 ⟨hdiff.1, hA⟩)

/-- A conditional expectation vanishes off an event measurable in its
conditioning sigma-algebra whenever the original variable does. -/
theorem condExp_zero_off_measurable_active
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (A : Set Ω) (hA : MeasurableSet[m] A) (X : Ω → ℝ)
    (hoff : ∀ᵐ ω ∂μ, ω ∉ A → X ω = 0) :
    ∀ᵐ ω ∂μ, ω ∉ A → μ[X | m] ω = 0 := by
  let : MeasurableSpace Ω := mΩ
  have hAc : MeasurableSet Aᶜ := (hm A hA).compl
  have hXrestrict : X =ᵐ[μ.restrict Aᶜ] 0 :=
    (ae_restrict_iff' hAc).2 hoff
  have hYrestrict : μ[X | m] =ᵐ[μ.restrict Aᶜ] 0 :=
    condExp_ae_eq_restrict_zero hA.compl hXrestrict
  exact (ae_restrict_iff' hAc).1 hYrestrict

/-- The measurable trace on the active event determines the conditional
expectation of any integrable variable vanishing off that event. -/
theorem condExp_cumulative_eq_latest_of_active_trace
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (mLatest mCum : MeasurableSpace Ω)
    (hle : mLatest ≤ mCum) (hCum : mCum ≤ mΩ)
    (A : Set Ω) (hA : MeasurableSet[mLatest] A)
    (htrace : ∀ B : Set Ω, MeasurableSet[mCum] B →
      ∃ C : Set Ω, MeasurableSet[mLatest] C ∧ B ∩ A = C ∩ A)
    (X : Ω → ℝ) (hX : Integrable X μ)
    (hoff : ∀ᵐ ω ∂μ, ω ∉ A → X ω = 0) :
    μ[X | mCum] =ᵐ[μ] μ[X | mLatest] := by
  let : MeasurableSpace Ω := mΩ
  have hLatest : mLatest ≤ mΩ := hle.trans hCum
  let Y : Ω → ℝ := μ[X | mLatest]
  have hYint : Integrable Y μ := integrable_condExp
  have hYstrong : StronglyMeasurable[mLatest] Y := stronglyMeasurable_condExp
  have hYoff : ∀ᵐ ω ∂μ, ω ∉ A → Y ω = 0 :=
    condExp_zero_off_measurable_active μ mLatest hLatest A hA X hoff
  have hunique : Y =ᵐ[μ] μ[X | mCum] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hCum hX
    · intro B hB hfinite
      exact hYint.integrableOn
    · intro B hB hfinite
      obtain ⟨C, hC, hBA⟩ := htrace B hB
      have hBambient : MeasurableSet B := hCum B hB
      calc
        (∫ ω in B, Y ω ∂μ) = ∫ ω in B ∩ A, Y ω ∂μ :=
          setIntegral_eq_active_intersection μ A B hBambient Y hYoff
        _ = ∫ ω in C ∩ A, Y ω ∂μ := by rw [hBA]
        _ = ∫ ω in C ∩ A, X ω ∂μ :=
          setIntegral_condExp hLatest hX (hC.inter hA)
        _ = ∫ ω in B ∩ A, X ω ∂μ := by rw [hBA]
        _ = ∫ ω in B, X ω ∂μ :=
          (setIntegral_eq_active_intersection μ A B hBambient X hoff).symm
    · exact (hYstrong.mono hle).aestronglyMeasurable
  exact hunique.symm

/-- A global latest-observation half bound transfers to the cumulative
sigma-algebra under the same active-event trace hypotheses. -/
theorem condExp_cumulative_le_half_of_latest_half
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (mLatest mCum : MeasurableSpace Ω)
    (hle : mLatest ≤ mCum) (hCum : mCum ≤ mΩ)
    (A : Set Ω) (hA : MeasurableSet[mLatest] A)
    (htrace : ∀ B : Set Ω, MeasurableSet[mCum] B →
      ∃ C : Set Ω, MeasurableSet[mLatest] C ∧ B ∩ A = C ∩ A)
    (X : Ω → ℝ) (hX : Integrable X μ)
    (hoff : ∀ᵐ ω ∂μ, ω ∉ A → X ω = 0)
    (hhalf : ∀ᵐ ω ∂μ, μ[X | mLatest] ω ≤ (1 : ℝ) / 2) :
    ∀ᵐ ω ∂μ, μ[X | mCum] ω ≤ (1 : ℝ) / 2 := by
  let : MeasurableSpace Ω := mΩ
  have heq := condExp_cumulative_eq_latest_of_active_trace
    μ mLatest mCum hle hCum A hA htrace X hX hoff
  filter_upwards [heq, hhalf] with ω heqω hhalfω
  exact heqω.trans_le hhalfω

/-- An active-only latest half bound is sufficient: both conditional means
are zero a.e. off the active event, so the cumulative half bound is global. -/
theorem condExp_cumulative_le_half_of_active_latest_half
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (mLatest mCum : MeasurableSpace Ω)
    (hle : mLatest ≤ mCum) (hCum : mCum ≤ mΩ)
    (A : Set Ω) (hA : MeasurableSet[mLatest] A)
    (htrace : ∀ B : Set Ω, MeasurableSet[mCum] B →
      ∃ C : Set Ω, MeasurableSet[mLatest] C ∧ B ∩ A = C ∩ A)
    (X : Ω → ℝ) (hX : Integrable X μ)
    (hoff : ∀ᵐ ω ∂μ, ω ∉ A → X ω = 0)
    (hhalf : ∀ᵐ ω ∂μ, ω ∈ A → μ[X | mLatest] ω ≤ (1 : ℝ) / 2) :
    ∀ᵐ ω ∂μ, μ[X | mCum] ω ≤ (1 : ℝ) / 2 := by
  let : MeasurableSpace Ω := mΩ
  have heq := condExp_cumulative_eq_latest_of_active_trace
    μ mLatest mCum hle hCum A hA htrace X hX hoff
  have hYoff := condExp_zero_off_measurable_active
    μ mLatest (hle.trans hCum) A hA X hoff
  filter_upwards [heq, hhalf, hYoff] with ω heqω hhalfω hYoffω
  rw [heqω]
  by_cases hω : ω ∈ A
  · exact hhalfω hω
  · rw [hYoffω hω]
    norm_num

end

end HeavyTailedNoise
