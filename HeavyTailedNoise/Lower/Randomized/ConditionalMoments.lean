import HeavyTailedNoise.Lower.Randomized.StoppedPosterior

/-!
Directional second moments from the actual stopped posterior's common
residual-reflection invariance. The finite basis is selected at one fixed
record; no measurable basis selection and no conditional-Haar premise occur.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace HeavyTailedNoise.RandomizedLift

def observationSpan {d n : ℕ} (v : Fin n → Point d) : Submodule ℝ (Point d) :=
  Submodule.span ℝ (Set.range v)

theorem observedResidual_eq_self_of_mem {d n : ℕ} (v : Fin n → Point d)
    {w : Point d} (hw : w ∈ (observationSpan v)ᗮ) : observedResidual v w = w := by
  rw [observedResidual_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr hw

/-- A total normalized residual: a dependent new observation has direction zero. -/
def observedDirection {d n : ℕ} (v : Fin n → Point d) (q : Point d) : Point d :=
  ‖observedResidual v q‖⁻¹ • observedResidual v q

@[fun_prop] theorem measurable_observedDirection (d n : ℕ) :
    Measurable (fun p : (Fin n → Point d) × Point d => observedDirection p.1 p.2) := by
  unfold observedDirection
  exact (measurable_observedResidual d n).norm.inv.smul (measurable_observedResidual d n)

theorem observedDirection_mem_orthogonal {d n : ℕ} (v : Fin n → Point d)
    (q : Point d) : observedDirection v q ∈ (observationSpan v)ᗮ :=
  (observationSpan v)ᗮ.smul_mem _ (observedResidual_mem_orthogonal v q)

theorem observedDirection_zero {d n : ℕ} (v : Fin n → Point d) (q : Point d)
    (h : observedResidual v q = 0) : observedDirection v q = 0 := by
  simp [observedDirection, h]

theorem norm_observedDirection {d n : ℕ} (v : Fin n → Point d) (q : Point d)
    (h : observedResidual v q ≠ 0) : ‖observedDirection v q‖ = 1 := by
  rw [observedDirection, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)

theorem norm_observedDirection_le_one {d n : ℕ} (v : Fin n → Point d)
    (q : Point d) : ‖observedDirection v q‖ ≤ 1 := by
  by_cases h : observedResidual v q = 0
  · simp [observedDirection_zero v q h]
  · exact (norm_observedDirection v q h).le

theorem observationComplement_finrank_lower {d n : ℕ} (v : Fin n → Point d) :
    d ≤ n + Module.finrank ℝ (observationSpan v)ᗮ := by
  have hS : Module.finrank ℝ (observationSpan v) ≤ n := by
    have h := finrank_range_le_card (R := ℝ) v
    change Module.finrank ℝ (observationSpan v) ≤ Fintype.card (Fin n) at h
    simpa only [Fintype.card_fin] using h
  have hE : Module.finrank ℝ (Point d) = d := by
    simpa [Point] using finrank_euclideanSpace_fin (𝕜 := ℝ) (n := d)
  have hs := (observationSpan v).finrank_add_finrank_orthogonal
  rw [hE] at hs
  omega

theorem observationComplement_finrank_pos {d n : ℕ} (v : Fin n → Point d)
    (hd : n < d) : 0 < Module.finrank ℝ (observationSpan v)ᗮ := by
  have h := observationComplement_finrank_lower v
  omega

/-- Compact-support domination is proved from the actual norm bound. -/
theorem integrable_frame_inner_sq {d T : ℕ}
    (μ : Measure (Fin T → Point d)) [IsFiniteMeasure μ] (i : Fin T) (w : Point d)
    (hnorm : ∀ᵐ U ∂μ, ‖U i‖ ≤ 1) :
    Integrable (fun U => (inner ℝ (U i) w) ^ 2) μ := by
  apply (integrable_const (‖w‖ ^ 2)).mono'
    (((continuous_apply i).inner continuous_const).pow 2).aestronglyMeasurable
  filter_upwards [hnorm] with U hU
  have hi : |inner ℝ (U i) w| ≤ ‖w‖ :=
    (abs_real_inner_le_norm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right hU (norm_nonneg w))
  change |(inner ℝ (U i) w) ^ 2| ≤ ‖w‖ ^ 2
  rw [abs_of_nonneg (sq_nonneg (inner ℝ (U i) w))]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg w)).mpr hi

/-- A single Householder swap equates any two unit directional moments. -/
theorem frame_directional_second_moment_eq {d T : ℕ}
    (μ : Measure (Fin T → Point d)) (i : Fin T) (w e : Point d)
    (hnorm : ‖w‖ = ‖e‖)
    (hinv : μ.map (frameAction (householder (w - e))) = μ) :
    (∫ U, (inner ℝ (U i) e) ^ 2 ∂μ) =
      ∫ U, (inner ℝ (U i) w) ^ 2 ∂μ := by
  have hswap : householder (w - e) w = e := by
    simpa [householder] using Submodule.reflection_sub hnorm
  calc
    _ = ∫ U, (inner ℝ (U i) e) ^ 2 ∂μ.map (frameAction (householder (w - e))) := by
      rw [hinv]
    _ = ∫ U, (inner ℝ ((frameAction (householder (w - e)) U) i) e) ^ 2 ∂μ :=
      integral_map (measurable_frameAction _).aemeasurable
        (((continuous_apply i).inner continuous_const).pow 2).aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun U => by
        simp only [frameAction]
        calc
          _ = (inner ℝ ((householder (w - e)) (U i)) ((householder (w - e)) w)) ^ 2 := by
            rw [hswap]
          _ = _ := by rw [(householder (w - e)).inner_map_map])

/-- Pure finite-measure geometry: equal moments plus Bessel bound the trace.
There is no conditional-law hypothesis in this ordinary probability lemma. -/
theorem invariant_frame_card_mul_second_moment_le {d T : ℕ}
    (μ : Measure (Fin T → Point d)) [IsProbabilityMeasure μ]
    (S : Submodule ℝ (Point d)) (i : Fin T)
    (hnorm : ∀ᵐ U ∂μ, ‖U i‖ ≤ 1)
    (hinv : ∀ a ∈ Sᗮ, μ.map (frameAction (householder a)) = μ)
    (w : Point d) (hw : w ∈ Sᗮ) (hunit : ‖w‖ = 1) :
    (Module.finrank ℝ Sᗮ : ℝ) *
      (∫ U, (inner ℝ (U i) w) ^ 2 ∂μ) ≤ 1 := by
  classical
  let m := Module.finrank ℝ Sᗮ
  let b : OrthonormalBasis (Fin m) ℝ Sᗮ := stdOrthonormalBasis ℝ Sᗮ
  let e : Fin m → Point d := fun a => (b a : Point d)
  have he : Orthonormal ℝ e := b.orthonormal.comp_linearIsometry (Sᗮ).subtypeₗᵢ
  have hint (a : Fin m) : Integrable (fun U => (inner ℝ (U i) (e a)) ^ 2) μ :=
    integrable_frame_inner_sq μ i (e a) hnorm
  have heq (a : Fin m) :
      (∫ U, (inner ℝ (U i) (e a)) ^ 2 ∂μ) =
        ∫ U, (inner ℝ (U i) w) ^ 2 ∂μ := by
    apply frame_directional_second_moment_eq μ i w (e a)
    · exact hunit.trans (he.norm_eq_one a).symm
    · exact hinv (w - e a) (Sᗮ.sub_mem hw (b a).property)
  have hsum : (∑ a : Fin m, ∫ U, (inner ℝ (U i) (e a)) ^ 2 ∂μ) ≤ 1 := by
    rw [← integral_finsetSum Finset.univ (fun a _ => hint a)]
    calc
      _ ≤ ∫ _ : Fin T → Point d, (1 : ℝ) ∂μ := by
        apply integral_mono_ae
          (integrable_finsetSum Finset.univ (fun a _ => hint a)) (integrable_const _)
        filter_upwards [hnorm] with U hU
        have hbessel : (∑ a : Fin m, (inner ℝ (U i) (e a)) ^ 2) ≤ ‖U i‖ ^ 2 := by
          simpa only [Real.norm_eq_abs, sq_abs, real_inner_comm] using
            he.sum_inner_products_le (s := Finset.univ) (U i)
        exact hbessel.trans (by nlinarith [norm_nonneg (U i)])
      _ = 1 := by simp
  simpa only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, m] using hsum

theorem invariant_frame_directional_second_moment_le {d T : ℕ}
    (μ : Measure (Fin T → Point d)) [IsProbabilityMeasure μ]
    (S : Submodule ℝ (Point d)) (i : Fin T)
    (hnorm : ∀ᵐ U ∂μ, ‖U i‖ ≤ 1)
    (hinv : ∀ a ∈ Sᗮ, μ.map (frameAction (householder a)) = μ)
    (hpos : 0 < Module.finrank ℝ Sᗮ) (w : Point d)
    (hw : w ∈ Sᗮ) (hunit : ‖w‖ = 1) :
    (∫ U, (inner ℝ (U i) w) ^ 2 ∂μ) ≤
      1 / (Module.finrank ℝ Sᗮ : ℝ) := by
  have hm : (0 : ℝ) < Module.finrank ℝ Sᗮ := by exact_mod_cast hpos
  apply (le_div_iff₀ hm).mpr
  simpa only [mul_comm] using
    invariant_frame_card_mul_second_moment_le μ S i hnorm hinv w hw hunit

section ActualExperiment

variable {d N j k : ℕ} {Private : Type*} [MeasurableSpace Private]
variable (A : RandomAlgorithm d N Private) (r : Private)
variable {R : ℝ} (hR : 0 < R) (η : ℝ) (θ : unitInterval) (tape : ℕ → Bool)
variable (hT : j + k ≤ d)

/-- Actual conditional moment; every stochastic input is discharged by the
actual posterior theorems. All unit directions share the same AE record set. -/
theorem actualStoppedPosterior_directional_second_moment (t : ℕ) (hd : j + t < d) :
    ∀ᵐ c ∂actualStoppedRecordLaw A r hR η θ tape hT t,
      ∀ (i : Fin (j + k)) (w : Point d),
        w ∈ (observationSpan (recordObservationList t c))ᗮ → ‖w‖ = 1 →
        (∫ U, (inner ℝ (U i) w) ^ 2 ∂actualStoppedPosterior A r hR η θ tape hT t c) ≤
          1 / (Module.finrank ℝ (observationSpan (recordObservationList t c))ᗮ : ℝ) := by
  filter_upwards [actualStoppedPosterior_orthonormal A r hR η θ tape hT t,
    actualStoppedPosterior_residual_reflections A r hR η θ tape hT t] with c horth hinv
  intro i w hw hunit
  apply invariant_frame_directional_second_moment_le
    (actualStoppedPosterior A r hR η θ tape hT t c)
    (observationSpan (recordObservationList t c)) i
    (horth.mono (fun U hU => (hU.norm_eq_one i).le))
    _ (observationComplement_finrank_pos _ hd) w hw hunit
  intro a ha
  have hh := hinv a
  simpa only [recordReflection, observedResidual_eq_self_of_mem _ ha] using hh

/-- Normalized predictable observations, including zero residuals, satisfy
the actual posterior moment bound without an assumed covariance premise. -/
theorem actualStoppedPosterior_observedDirection_second_moment
    (t : ℕ) (hd : j + t < d) :
    ∀ᵐ c ∂actualStoppedRecordLaw A r hR η θ tape hT t,
      ∀ (i : Fin (j + k)) (q : Point d),
        (∫ U, (inner ℝ (U i) (observedDirection (recordObservationList t c) q)) ^ 2
          ∂actualStoppedPosterior A r hR η θ tape hT t c) ≤
          1 / (Module.finrank ℝ (observationSpan (recordObservationList t c))ᗮ : ℝ) := by
  filter_upwards [actualStoppedPosterior_directional_second_moment A r hR η θ tape hT t hd]
    with c hc
  intro i q
  by_cases h : observedResidual (recordObservationList t c) q = 0
  · simp only [observedDirection_zero _ _ h, inner_zero_right, zero_pow (by decide : 2 ≠ 0),
      integral_zero]
    positivity
  · exact hc i _ (observedDirection_mem_orthogonal _ _) (norm_observedDirection _ _ h)

section MomentComposition

attribute [local irreducible] observedDirection observedResidual

include hR in
/-- Integrating the literal record/frame disintegration gives the actual
prior moment for any measurable predictable observation, without a conditional
moment assumption. The basis used above never has to be chosen measurably. -/
theorem actualStopped_observedDirection_moment (t : ℕ) (hd : j + t < d)
    (q : StoppedRecord d (j + k) j t → Point d) (hq : Measurable q)
    (i : Fin (j + k)) :
    (∫⁻ u, ENNReal.ofReal ((inner ℝ (u.1 i)
      (observedDirection
        (recordObservationList t (actualStoppedRecord A r R η θ tape t u))
        (q (actualStoppedRecord A r R η θ tape t u)))) ^ 2)
      ∂preselectedOrthonormalFrameLaw d (j + k) hT) ≤
        ENNReal.ofReal (1 / ((d - (j + t) : ℕ) : ℝ)) := by
  let φ : StoppedRecord d (j + k) j t × (Fin (j + k) → Point d) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((inner ℝ (p.2 i)
      (observedDirection (recordObservationList t p.1) (q p.1))) ^ 2)
  let directionInput : StoppedRecord d (j + k) j t → (Fin (j + t) → Point d) × Point d :=
    fun c => (recordObservationList t c, q c)
  have hinput : Measurable directionInput :=
    (measurable_recordObservationList d (j + k) j t).prodMk hq
  have hcomposed := (measurable_observedDirection d (j + t)).comp hinput
  have hdir : Measurable (fun c : StoppedRecord d (j + k) j t =>
      observedDirection (recordObservationList t c) (q c)) := by
    simpa only [directionInput, Function.comp_def] using hcomposed
  have hφ : Measurable φ := ENNReal.measurable_ofReal.comp
    ((((measurable_pi_apply i).comp measurable_snd).inner
      (hdir.comp measurable_fst)).pow_const 2)
  have hm : Measurable (fun u : {U : Fin (j + k) → Point d // Orthonormal ℝ U} =>
      (actualStoppedRecord (j := j) (k := k) A r R η θ tape t u, u.1)) :=
    (measurable_actualStoppedRecord (j := j) (k := k) A r hR η θ tape t).prodMk
      measurable_subtype_coe
  change (∫⁻ u, φ (actualStoppedRecord A r R η θ tape t u, u.1)
    ∂preselectedOrthonormalFrameLaw d (j + k) hT) ≤ _
  rw [← lintegral_map hφ hm,
    actualStoppedRecord_joint A r hR η θ tape hT t,
    Measure.lintegral_compProd hφ]
  calc
    _ ≤ ∫⁻ _c, ENNReal.ofReal (1 / ((d - (j + t) : ℕ) : ℝ))
        ∂actualStoppedRecordLaw A r hR η θ tape hT t := by
      apply lintegral_mono_ae
      filter_upwards [actualStoppedPosterior_orthonormal A r hR η θ tape hT t,
        actualStoppedPosterior_observedDirection_second_moment A r hR η θ tape hT t hd]
        with c horth hmoment
      have hint := integrable_frame_inner_sq
        (actualStoppedPosterior A r hR η θ tape hT t c) i
        (observedDirection (recordObservationList t c) (q c))
        (horth.mono (fun U hU => (hU.norm_eq_one i).le))
      change (∫⁻ U, ENNReal.ofReal ((inner ℝ (U i)
        (observedDirection (recordObservationList t c) (q c))) ^ 2)
        ∂actualStoppedPosterior A r hR η θ tape hT t c) ≤ _
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun U => sq_nonneg _))]
      apply ENNReal.ofReal_le_ofReal
      apply (hmoment i (q c)).trans
      have hpos : (0 : ℝ) < ((d - (j + t) : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt hd
      have hrank : ((d - (j + t) : ℕ) : ℝ) ≤
          Module.finrank ℝ (observationSpan (recordObservationList t c))ᗮ := by
        have h := observationComplement_finrank_lower (recordObservationList t c)
        exact_mod_cast (show d - (j + t) ≤
          Module.finrank ℝ (observationSpan (recordObservationList t c))ᗮ by omega)
      exact one_div_le_one_div_of_le hpos hrank
    _ = _ := by simp

end MomentComposition

end ActualExperiment

end HeavyTailedNoise.RandomizedLift
