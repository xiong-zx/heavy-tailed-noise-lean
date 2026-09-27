import HeavyTailedNoise.Probability.GaussianKLAdaptive
import HeavyTailedNoise.Probability.GaussianInformation

/-!
Information comparison for an unknown next direction. A fixed reference
response law is independent of that direction; it may depend on the already
fixed prefix and private tape. This file does not construct the conditional
Haar law or identify the stopped-stage response kernel.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

namespace HeavyTailedNoise

/-- KL of a parameter-dependent kernel against a kernel sharing the same
parameter law is the average conditional KL. This is the measure-level bridge
needed to pass from fixed-direction Gaussian transcript bounds to a mixture. -/
private theorem klDiv_compProd_eq_lintegral_conditional'
    {Θ H : Type*} [MeasurableSpace Θ] [MeasurableSpace H]
    [MeasurableSpace.CountableOrCountablyGenerated Θ H]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K L : Kernel Θ H) [IsMarkovKernel K] [IsMarkovKernel L]
    (hAC : ∀ θ, K θ ≪ L θ) :
    klDiv (π ⊗ₘ K) (π ⊗ₘ L) = ∫⁻ θ, klDiv (K θ) (L θ) ∂π := by
  have hJointAC : π ⊗ₘ K ≪ π ⊗ₘ L :=
    (Measure.absolutelyContinuous_compProd_right_iff).2 (ae_of_all _ hAC)
  have hf : Measurable (fun p : Θ × H =>
      ENNReal.ofReal (klFun (K.rnDeriv L p.1 p.2).toReal)) := by
    fun_prop
  rw [klDiv_eq_lintegral_klFun_of_ac hJointAC]
  calc
    (∫⁻ p, ENNReal.ofReal
        (klFun (((π ⊗ₘ K).rnDeriv (π ⊗ₘ L) p).toReal)) ∂(π ⊗ₘ L)) =
      ∫⁻ p, ENNReal.ofReal
        (klFun (K.rnDeriv L p.1 p.2).toReal) ∂(π ⊗ₘ L) := by
          apply lintegral_congr_ae
          filter_upwards [rnDeriv_measure_compProd_right π K L] with p hp
          rw [hp]
    _ = ∫⁻ θ, ∫⁻ h, ENNReal.ofReal
          (klFun (K.rnDeriv L θ h).toReal) ∂(L θ) ∂π := by
          rw [Measure.lintegral_compProd hf]
    _ = ∫⁻ θ, klDiv (K θ) (L θ) ∂π := by
          apply lintegral_congr
          intro θ
          calc
            (∫⁻ h, ENNReal.ofReal
                (klFun (K.rnDeriv L θ h).toReal) ∂(L θ)) =
              ∫⁻ h, ENNReal.ofReal
                (klFun (((K θ).rnDeriv (L θ) h).toReal)) ∂(L θ) := by
                  apply lintegral_congr_ae
                  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure
                    (κ := K) (η := L) (a := θ)] with h hh
                  rw [hh]
            _ = klDiv (K θ) (L θ) :=
              (klDiv_eq_lintegral_klFun_of_ac (hAC θ)).symm

/-- A uniform conditional KL bound controls the joint law of an unknown
direction and a response history against an independent reference history.
The reference is fixed before the direction is drawn. -/
theorem mixture_reference_klDiv_le
    {Θ H : Type*} [MeasurableSpace Θ] [MeasurableSpace H]
    [MeasurableSpace.CountableOrCountablyGenerated Θ H]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ H) [IsMarkovKernel K]
    (R : Measure H) [IsProbabilityMeasure R]
    (B : ENNReal) (hKL : ∀ θ, klDiv (K θ) R ≤ B) :
    klDiv (π ⊗ₘ K) (π.prod R) ≤ B := by
  by_cases hB : B = ∞
  · simp [hB]
  · letI : IsMarkovKernel (Kernel.const Θ R) := inferInstance
    have hAC (θ : Θ) : K θ ≪ (Kernel.const Θ R) θ := by
      change K θ ≪ R
      have hfinite : klDiv (K θ) R ≠ ∞ :=
        ne_top_of_le_ne_top hB (hKL θ)
      exact (klDiv_ne_top_iff.mp hfinite).1
    rw [← Measure.compProd_const]
    rw [klDiv_compProd_eq_lintegral_conditional' π K (Kernel.const Θ R) hAC]
    calc
      (∫⁻ θ, klDiv (K θ) ((Kernel.const Θ R) θ) ∂π) ≤
          ∫⁻ _ : Θ, B ∂π := by
            apply lintegral_mono
            intro θ
            simpa using hKL θ
      _ = B := by simp

/-- The fixed-horizon Gaussian chain bound can be averaged over an unknown
next direction. `H` may hold the full response history. A private tape may be
fixed as an external parameter in every kernel and then averaged separately.
The premises `hK` and `hR` identify the jointly measurable direction kernel
and the direction-independent reference with their actual adaptive laws. -/
theorem adaptive_unknownDirection_referenceKL_le
    {Θ H : Type*} [MeasurableSpace Θ] [MeasurableSpace H]
    [MeasurableSpace.CountableOrCountablyGenerated Θ H]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ H) [IsMarkovKernel K]
    (R : Measure H) [IsProbabilityMeasure R]
    (d : ℕ) [MeasurableSpace.CountableOrCountablyGenerated H (Point d)]
    (hd : 0 < d) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (C : ℝ)
    (P₀ : Measure H) [IsProbabilityMeasure P₀]
    (κ : Θ → ℕ → Kernel H (Point d))
    (η : ℕ → Kernel H (Point d))
    (hκMarkov : ∀ θ t, IsMarkovKernel (κ θ t))
    (hηMarkov : ∀ t, IsMarkovKernel (η t))
    (m : Θ → ℕ → H → Point d) (n : ℕ → H → Point d)
    (hκLaw : ∀ θ t h, κ θ t h =
      gaussianResponseLaw d (m θ t h) (σ₀ / Real.sqrt d))
    (hηLaw : ∀ t h, η t h =
      gaussianResponseLaw d (n t h) (σ₀ / Real.sqrt d))
    (hdiam : ∀ θ t h, ‖m θ t h - n t h‖ ≤ C)
    (update : ℕ → H × Point d → H)
    (hUpdate : ∀ t, Measurable (update t)) (N : ℕ)
    (hK : ∀ θ, K θ = adaptiveGaussianLaw d P₀ (κ θ) update N)
    (hR : R = adaptiveGaussianLaw d P₀ η update N) :
    klDiv (π ⊗ₘ K) (π.prod R) ≤
      (N : ENNReal) * ENNReal.ofReal ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2)) := by
  apply mixture_reference_klDiv_le π K R _
  intro θ
  rw [hK θ, hR]
  exact adaptiveGaussianLaw_klDiv_le d hd σ₀ hσ₀ C P₀
    (κ θ) η (hκMarkov θ) hηMarkov (m θ) n
    (hκLaw θ) hηLaw (hdiam θ) update hUpdate N

/-- The two-point statistic recording whether a transcript event occurred. -/
def eventBit {Ω : Type*} (E : Set Ω) (ω : Ω) : Bool := by
  classical
  exact if ω ∈ E then true else false

theorem measurable_eventBit {Ω : Type*} [MeasurableSpace Ω]
    {E : Set Ω} (hE : MeasurableSet E) : Measurable (eventBit E) := by
  classical
  change Measurable (fun ω => if ω ∈ E then true else false)
  exact Measurable.ite hE measurable_const measurable_const

theorem eventBit_true_mass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {E : Set Ω} (hE : MeasurableSet E) :
    (P.map (eventBit E)) {true} = P E := by
  classical
  rw [Measure.map_apply (measurable_eventBit hE) (measurableSet_singleton true)]
  congr 1
  ext ω
  simp [eventBit]

theorem eventBit_false_mass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {E : Set Ω} (hE : MeasurableSet E) :
    (P.map (eventBit E)) {false} = P Eᶜ := by
  classical
  rw [Measure.map_apply (measurable_eventBit hE) (measurableSet_singleton false)]
  congr 1
  ext ω
  simp [eventBit]

private theorem rnDeriv_bool_atom (μ ν : Measure Bool)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hAC : μ ≪ ν)
    (b : Bool) (hν0 : ν {b} ≠ 0) :
    (μ.rnDeriv ν b).toReal = (μ {b}).toReal / (ν {b}).toReal := by
  have h := congrArg (fun ξ : Measure Bool => ξ {b})
    (Measure.withDensity_rnDeriv_eq μ ν hAC)
  rw [withDensity_apply _ (measurableSet_singleton b),
    lintegral_singleton] at h
  have hrn : μ.rnDeriv ν b = μ {b} / ν {b} :=
    (ENNReal.eq_div_iff hν0 (measure_ne_top ν {b})).2 (by simpa [mul_comm] using h)
  rw [hrn, ENNReal.toReal_div]

private theorem binaryScore_eq_weighted_log {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    binaryKLScore p q =
      p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  by_cases hpz : p = 0
  · subst p
    simp [binaryKLScore, Real.binEntropy]
  by_cases hpo : p = 1
  · subst p
    simp [binaryKLScore, Real.binEntropy]
  have hpp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
  have hpl : p < 1 := lt_of_le_of_ne hp1 hpo
  have h1p : 0 < 1 - p := sub_pos.mpr hpl
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  rw [Real.log_div hpp.ne' hq0.ne', Real.log_div h1p.ne' h1q.ne']
  simp only [binaryKLScore, Real.binEntropy, Real.log_inv]
  ring

private theorem bool_klDiv_eq_binaryScore
    (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hAC : μ ≪ ν) (hνT : ν {true} ≠ 0) (hνF : ν {false} ≠ 0) :
    (klDiv μ ν).toReal =
      binaryKLScore (μ {true}).toReal (ν {true}).toReal := by
  have hInt : Integrable (llr μ ν) μ := by
    simpa using (IntegrableOn.of_finite (s := Set.univ)
      (μ := μ) (f := llr μ ν) Set.finite_univ)
  have hmass : μ Set.univ = ν Set.univ := by
    calc
      μ Set.univ = 1 := measure_univ
      _ = ν Set.univ := measure_univ.symm
  have hcomp : ({true} : Set Bool)ᶜ = {false} := by
    ext b
    cases b <;> simp
  have hμF : (μ {false}).toReal = 1 - (μ {true}).toReal := by
    have h := measureReal_compl (μ := μ) (s := ({true} : Set Bool))
      (measurableSet_singleton true)
    rw [hcomp] at h
    rw [probReal_univ] at h
    simpa [measureReal_def] using h
  have hνFreal : (ν {false}).toReal = 1 - (ν {true}).toReal := by
    have h := measureReal_compl (μ := ν) (s := ({true} : Set Bool))
      (measurableSet_singleton true)
    rw [hcomp] at h
    rw [probReal_univ] at h
    simpa [measureReal_def] using h
  have hp0 : 0 ≤ (μ {true}).toReal := ENNReal.toReal_nonneg
  have hp1 : (μ {true}).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (prob_le_one : μ {true} ≤ 1)
  have hq0 : 0 < (ν {true}).toReal :=
    ENNReal.toReal_pos hνT (measure_ne_top ν {true})
  have hqF : 0 < (ν {false}).toReal :=
    ENNReal.toReal_pos hνF (measure_ne_top ν {false})
  have hq1 : (ν {true}).toReal < 1 := by linarith
  rw [toReal_klDiv_of_measure_eq hAC hmass, integral_fintype hInt]
  simp only [Fintype.sum_bool, smul_eq_mul, llr_def, measureReal_def]
  rw [rnDeriv_bool_atom μ ν hAC false hνF,
    rnDeriv_bool_atom μ ν hAC true hνT, hμF, hνFreal]
  exact (binaryScore_eq_weighted_log hp0 hp1 hq0 hq1).symm


/-- Data processing through the event bit gives the complete binary event KL
inequality. The two-point KL value is evaluated above from its atomic density. -/
theorem binaryEventScore_le_klDiv
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set Ω) (hE : MeasurableSet E)
    (hq₀ : 0 < (Q E).toReal) (hq₁ : (Q E).toReal < 1)
    (hfinite : klDiv P Q ≠ ∞) :
    binaryKLScore (P E).toReal (Q E).toReal ≤
      (klDiv P Q).toReal := by
  have hAC : P ≪ Q := (klDiv_ne_top_iff.mp hfinite).1
  have hQF : 0 < (Q Eᶜ).toReal := by
    have h := probReal_compl_eq_one_sub (μ := Q) hE
    have h' : (Q Eᶜ).toReal = 1 - (Q E).toReal := by
      simpa [measureReal_def] using h
    rw [h']
    linarith
  have hνT : (Q.map (eventBit E)) {true} ≠ 0 := by
    rw [eventBit_true_mass Q hE]
    exact (ENNReal.toReal_pos_iff.mp hq₀).1.ne'
  have hνF : (Q.map (eventBit E)) {false} ≠ 0 := by
    rw [eventBit_false_mass Q hE]
    exact (ENNReal.toReal_pos_iff.mp hQF).1.ne'
  have hEval := bool_klDiv_eq_binaryScore
    (P.map (eventBit E)) (Q.map (eventBit E))
    (hAC.map (measurable_eventBit hE)) hνT hνF
  rw [eventBit_true_mass P hE, eventBit_true_mass Q hE] at hEval
  rw [← hEval]
  exact ENNReal.toReal_mono hfinite
    (klDiv_map_le P Q (measurable_eventBit hE))

/-- The pinhole estimate for any two probability laws with finite KL. -/
theorem pinhole_of_referenceKL
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set Ω) (hE : MeasurableSet E) (I : ℝ) (hI : 0 ≤ I)
    (hq₀ : 0 < (Q E).toReal) (hq₁ : (Q E).toReal < 1)
    (hKL : klDiv P Q ≤ ENNReal.ofReal I) :
    (P E).toReal ≤
      (I + Real.log 2) / Real.log (Q E).toReal⁻¹ := by
  have hp : (P E).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one : P E ≤ 1)
  have hKLreal : (klDiv P Q).toReal ≤ I := by
    simpa [ENNReal.toReal_ofReal hI] using
      ENNReal.toReal_mono (by simp : ENNReal.ofReal I ≠ ∞) hKL
  have hfinite : klDiv P Q ≠ ∞ :=
    ne_top_of_le_ne_top (by simp : ENNReal.ofReal I ≠ ∞) hKL
  have hbinary := binaryEventScore_le_klDiv P Q E hE hq₀ hq₁ hfinite
  exact pinhole_of_binaryKLScore_le hp hq₀ hq₁ (hbinary.trans hKLreal)

/-- Apply the pinhole step to the same independent reference law used in
`mixture_reference_klDiv_le`. The event may inspect the entire direction and
response transcript. -/
theorem unknownDirection_pinhole_of_referenceKL
    {Θ H : Type*} [MeasurableSpace Θ] [MeasurableSpace H]
    (π : Measure Θ) [IsProbabilityMeasure π]
    (K : Kernel Θ H) [IsMarkovKernel K]
    (R : Measure H) [IsProbabilityMeasure R]
    (E : Set (Θ × H)) (hE : MeasurableSet E) (I : ℝ) (hI : 0 ≤ I)
    (hq₀ : 0 < ((π.prod R) E).toReal)
    (hq₁ : ((π.prod R) E).toReal < 1)
    (hKL : klDiv (π ⊗ₘ K) (π.prod R) ≤ ENNReal.ofReal I) :
    ((π ⊗ₘ K) E).toReal ≤
      (I + Real.log 2) / Real.log ((π.prod R) E).toReal⁻¹ :=
  pinhole_of_referenceKL (π ⊗ₘ K) (π.prod R) E hE I hI hq₀ hq₁ hKL

/-- The quantitative pinhole conclusion used by a stage argument: a rare
event under an independent reference law and a small joint KL make its true
probability at most one half. The cap estimate enters only through `hqcap`.
The Bernoulli reduction and two-point KL evaluation are proved above. -/
theorem pinhole_half_of_referenceKL_cap
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set Ω) (hE : MeasurableSet E) (I qcap : ℝ) (hI : 0 ≤ I)
    (hq₀ : 0 < (Q E).toReal)
    (hqcap₀ : 0 < qcap) (hqcap₁ : qcap < 1)
    (hqcap : (Q E).toReal ≤ qcap)
    (hKL : klDiv P Q ≤ ENNReal.ofReal I)
    (hbudget : I + Real.log 2 ≤ (1 / 2 : ℝ) * Real.log qcap⁻¹) :
    (P E).toReal ≤ 1 / 2 := by
  have hq₁ : (Q E).toReal < 1 := lt_of_le_of_lt hqcap hqcap₁
  have hlogpos : 0 < Real.log (Q E).toReal⁻¹ :=
    Real.log_pos ((one_lt_inv₀ hq₀).2 hq₁)
  have hlogle : Real.log qcap⁻¹ ≤ Real.log (Q E).toReal⁻¹ :=
    Real.log_le_log (inv_pos.mpr hqcap₀) (inv_anti₀ hq₀ hqcap)
  have hp := pinhole_of_referenceKL P Q E hE I hI hq₀ hq₁ hKL
  have hmul : (P E).toReal * Real.log (Q E).toReal⁻¹ ≤
      I + Real.log 2 := (le_div_iff₀ hlogpos).mp hp
  have hhalf : I + Real.log 2 ≤
      (1 / 2 : ℝ) * Real.log (Q E).toReal⁻¹ :=
    hbudget.trans (mul_le_mul_of_nonneg_left hlogle (by norm_num))
  exact (mul_le_mul_iff_right₀ hlogpos).mp
    (by simpa [mul_comm] using hmul.trans hhalf)

/-- The same half-probability bound includes the case in which the independent
reference event has probability zero. Finite KL then gives absolute
continuity, so the true event is null as well. -/
theorem pinhole_half_of_referenceKL_cap_or_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set Ω) (hE : MeasurableSet E) (I qcap : ℝ) (hI : 0 ≤ I)
    (hqcap₀ : 0 < qcap) (hqcap₁ : qcap < 1)
    (hqcap : (Q E).toReal ≤ qcap)
    (hKL : klDiv P Q ≤ ENNReal.ofReal I)
    (hbudget : I + Real.log 2 ≤ (1 / 2 : ℝ) * Real.log qcap⁻¹) :
    (P E).toReal ≤ 1 / 2 := by
  by_cases hq : Q E = 0
  · have hfinite : klDiv P Q ≠ ∞ :=
      ne_top_of_le_ne_top (by simp : ENNReal.ofReal I ≠ ∞) hKL
    have hP : P E = 0 := (klDiv_ne_top_iff.mp hfinite).1 hq
    simp [hP]
  · have hq₀ : 0 < (Q E).toReal :=
      ENNReal.toReal_pos hq (measure_ne_top Q E)
    exact pinhole_half_of_referenceKL_cap P Q E hE I qcap hI
      hq₀ hqcap₀ hqcap₁ hqcap hKL hbudget

/-- A uniform conditional event bound survives averaging over an arbitrary
private seed space. No countable-generation condition is placed on `Private`.
The pointwise laws can be the direction/response joint laws above, indexed by
the realized private tape. -/
theorem private_randomized_event_bound
    {Private Ω : Type*} [MeasurableSpace Private] [MeasurableSpace Ω]
    (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (P : Private → Measure Ω) (E : Private → Set Ω) (B : ENNReal)
    (hpoint : ∀ r, P r (E r) ≤ B) :
    (∫⁻ r, P r (E r) ∂ρ) ≤ B := by
  calc
    (∫⁻ r, P r (E r) ∂ρ) ≤ ∫⁻ _ : Private, B ∂ρ :=
      lintegral_mono hpoint
    _ = B := by simp

/-- A per-private-seed pinhole estimate gives the same bound after averaging
over any private seed law, without restrictions on the private seed space. -/
theorem private_randomized_event_half
    {Private Ω : Type*} [MeasurableSpace Private] [MeasurableSpace Ω]
    (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (P : Private → Measure Ω)
    (hP : ∀ r, IsProbabilityMeasure (P r))
    (E : Private → Set Ω)
    (hpoint : ∀ r, (P r (E r)).toReal ≤ 1 / 2) :
    (∫⁻ r, P r (E r) ∂ρ) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  apply private_randomized_event_bound ρ P E _
  intro r
  letI : IsProbabilityMeasure (P r) := hP r
  rw [← ENNReal.ofReal_toReal (measure_ne_top (P r) (E r))]
  exact ENNReal.ofReal_le_ofReal (hpoint r)

end HeavyTailedNoise
