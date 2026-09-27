import HeavyTailedNoise.Model.Protocol
import HeavyTailedNoise.Model.Distributional

/-!
Arbitrary-output risk tools. A reflection preserves every shared-model
admissibility condition. Equality of responses on one constant seed tape
gives equality of the entire history and of the response-free output, for
every private realization and every measurable full-history algorithm.
-/

namespace HeavyTailedNoise.RandomizedLift

open MeasureTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false

/-- Reflection of an actual shared-model instance; no oracle model is changed. -/
def reflectAdmissible {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L) :
    Admissible d Seed p q Δ σ L where
  objective := {
    dimension_pos := I.objective.dimension_pos
    value := fun x => I.objective.value (-x)
    grad := fun x => -I.objective.grad (-x)
    hasGradientAt := fun x => by
      rw [hasGradientAt_iff_hasFDerivAt]
      have h := I.objective.hasGradientAt (-x)
      rw [hasGradientAt_iff_hasFDerivAt] at h
      apply (h.comp x (hasFDerivAt_id x).neg).congr_fderiv
      ext v
      simp [InnerProductSpace.toDual_apply_apply]
    continuous_grad := (I.objective.continuous_grad.comp continuous_neg).neg
    gap := fun x => by simpa using I.objective.gap (-x) }
  oracle := {
    law := I.oracle.law
    law_probability := I.oracle.law_probability
    response := fun x ξ => -I.oracle.response (-x) ξ
    measurable_response := (I.oracle.measurable_response.comp
      (measurable_fst.neg.prodMk measurable_snd)).neg }
  p_range := I.p_range
  q_range := I.q_range
  delta_pos := I.delta_pos
  sigma_nonneg := I.sigma_nonneg
  Lbar_pos := I.Lbar_pos
  integrable_response := fun x => (I.integrable_response (-x)).neg
  unbiased := fun x => by simpa only [integral_neg] using congrArg Neg.neg (I.unbiased (-x))
  centered_moment := fun x => by
    simpa only [neg_sub_neg, norm_sub_rev] using I.centered_moment (-x)
  same_seed_increment := fun x y => by
    simpa only [neg_sub_neg, norm_sub_rev] using I.same_seed_increment (-x) (-y)

/-- The start query is arbitrary. Induction uses only the shared response
at the current query and therefore retains the full observed history. -/
theorem runTranscript_constant_seed_eq {d N : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O₀ O₁ : GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (ξ₀ : Seed) (hresponse : ∀ x, O₀.response x ξ₀ = O₁.response x ξ₀)
    (r : Private) (n : ℕ) :
    runTranscript O₀ A r n (fun _ => ξ₀) =
      runTranscript O₁ A r n (fun _ => ξ₀) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [runTranscript] at *
      rw [ih, hresponse]

/-- A singleton tape lower bound, integrated over arbitrary independent
private randomness. Infinite risks are allowed. -/
theorem singleton_pairRisk_lower_bound {d N : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed] [MeasurableSpace Private]
    {p q Δ σ L C : ℝ}
    (I₀ I₁ : Admissible d Seed p q Δ σ L) (A : RandomAlgorithm d N Private)
    (ξ₀ : Seed) (hC : 0 ≤ C) (hlaw : I₀.oracle.law = I₁.oracle.law)
    (hresponse : ∀ x, I₀.oracle.response x ξ₀ = I₁.oracle.response x ξ₀)
    (hbarrier : ∀ x, C ≤ ‖I₀.objective.grad x‖ + ‖I₁.objective.grad x‖) :
    ENNReal.ofReal C * freshSeedLaw I₀.oracle N {fun _ => ξ₀} ≤
      risk I₀ A + risk I₁ A := by
  let μ := freshSeedLaw I₀.oracle N
  haveI : IsProbabilityMeasure μ := freshSeedLaw_probability I₀.oracle N
  haveI : IsProbabilityMeasure A.privateLaw := A.private_probability
  have hμ : freshSeedLaw I₁.oracle N = μ := by
    simp only [μ, freshSeedLaw, hlaw]
  let f₀ := fun z : Private × (Fin N → Seed) =>
    ENNReal.ofReal ‖I₀.objective.grad (A.output z.1 (runTranscript I₀.oracle A z.1 N z.2))‖
  let f₁ := fun z : Private × (Fin N → Seed) =>
    ENNReal.ofReal ‖I₁.objective.grad (A.output z.1 (runTranscript I₁.oracle A z.1 N z.2))‖
  have hf₀ : Measurable f₀ := measurable_riskValue I₀ A
  have hf₁ : Measurable f₁ := measurable_riskValue I₁ A
  have hpoint (r : Private) :
      ENNReal.ofReal C * μ {fun _ => ξ₀} ≤
        (∫⁻ seeds, f₀ (r, seeds) ∂μ) + ∫⁻ seeds, f₁ (r, seeds) ∂μ := by
    have hout := congrArg (A.output r)
      (runTranscript_constant_seed_eq I₀.oracle I₁.oracle A ξ₀ hresponse r N)
    have hb : ENNReal.ofReal C ≤ f₀ (r, fun _ => ξ₀) + f₁ (r, fun _ => ξ₀) := by
      dsimp [f₀, f₁]
      rw [← hout, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hbarrier _)
    calc
      _ ≤ (f₀ (r, fun _ => ξ₀) + f₁ (r, fun _ => ξ₀)) * μ {fun _ => ξ₀} :=
        mul_le_mul' hb le_rfl
      _ = (∫⁻ seeds in {fun _ => ξ₀}, f₀ (r, seeds) ∂μ) +
          ∫⁻ seeds in {fun _ => ξ₀}, f₁ (r, seeds) ∂μ := by
        rw [lintegral_singleton, lintegral_singleton, add_mul]
      _ ≤ (∫⁻ seeds, f₀ (r, seeds) ∂μ) + ∫⁻ seeds, f₁ (r, seeds) ∂μ :=
        add_le_add (setLIntegral_le_lintegral _ _) (setLIntegral_le_lintegral _ _)
  calc
    _ = ∫⁻ _ : Private, ENNReal.ofReal C * μ {fun _ => ξ₀} ∂A.privateLaw := by simp [μ]
    _ ≤ ∫⁻ r, (∫⁻ seeds, f₀ (r, seeds) ∂μ) +
        ∫⁻ seeds, f₁ (r, seeds) ∂μ ∂A.privateLaw := lintegral_mono hpoint
    _ = risk I₀ A + risk I₁ A := by
      rw [lintegral_add_left hf₀.lintegral_prod_right']
      simp only [risk, hμ]
      rfl

end
end HeavyTailedNoise.RandomizedLift
