import HeavyTailedNoise.Lower.Randomized.Stationarity
import HeavyTailedNoise.Model.Protocol
import HeavyTailedNoise.Lower.Gated.ScaledAlgorithmCoupling

/-!
Physical rescaling of the actual projected Bernoulli/Carmon family.
The only scalar premises of `scaledAdmissible` are its three numerical
budgets; PhysicalParameters discharges them from public parameters.
The existing public-scalar algorithm transformation is reused unchanged.
-/

namespace HeavyTailedNoise.RandomizedLift

open MeasureTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false

def scaledPotential {d T : ℕ} (U : Fin T → Point d) (R η a lam : ℝ)
    (x : Point d) : ℝ := a * lam * potential U R η (lam⁻¹ • x)

def scaledPopulationGradient {d T : ℕ} (U : Fin T → Point d) (R η a lam : ℝ)
    (x : Point d) : Point d := a • populationGradient U R η (lam⁻¹ • x)

def scaledResponse {d T : ℕ} (U : Fin T → Point d) (R η a lam : ℝ)
    (θ : unitInterval) (x : Point d) (D : Bool) : Point d :=
  a • response U R η θ (lam⁻¹ • x) D

theorem hasGradientAt_scaledPotential {d T : ℕ} (U : Fin T → Point d)
    {R lam : ℝ} (hR : 0 < R) (hlam : 0 < lam) (η a : ℝ) (x : Point d) :
    HasGradientAt (scaledPotential U R η a lam)
      (scaledPopulationGradient U R η a lam x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hm : HasFDerivAt (fun y : Point d => lam⁻¹ • y)
      (lam⁻¹ • ContinuousLinearMap.id ℝ (Point d)) x :=
    (hasFDerivAt_id x).const_smul lam⁻¹
  have h := ((hasGradientAt_potential U hR η (lam⁻¹ • x)).hasFDerivAt.comp x hm).const_smul (a * lam)
  convert h using 1
  · ext y
    rfl
  · ext v
    simp [scaledPopulationGradient, InnerProductSpace.toDual_apply_apply,
      real_inner_smul_left, real_inner_smul_right] <;>
      field_simp [hlam.ne'] <;> ring

theorem continuous_scaledPopulationGradient {d T : ℕ} (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) (η a lam : ℝ) :
    Continuous (scaledPopulationGradient U R η a lam) :=
  ((continuous_populationGradient U hR η).comp
    (continuous_id.const_smul lam⁻¹)).const_smul a

theorem scaledPotential_gap_le {d T : ℕ} (U : Fin T → Point d)
    (R lam : ℝ) {η a : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a) (hlam : 0 ≤ lam) (x : Point d) :
    scaledPotential U R η a lam 0 - scaledPotential U R η a lam x ≤
      a * lam * (12 * T) := by
  have h := mul_le_mul_of_nonneg_left
    (potential_gap_le_12T U R hη (lam⁻¹ • x)) (mul_nonneg ha hlam)
  simpa only [scaledPotential, smul_zero, mul_sub] using h

theorem measurable_scaledResponse {d T : ℕ} (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) (η a lam : ℝ) (θ : unitInterval) :
    Measurable (fun z : Point d × Bool => scaledResponse U R η a lam θ z.1 z.2) :=
  ((measurable_response U hR η θ).comp
    ((continuous_fst.const_smul lam⁻¹).measurable.prodMk measurable_snd)).const_smul a

def scaledOracle {d T : ℕ} (U : Fin T → Point d) {R : ℝ} (hR : 0 < R)
    (η a lam : ℝ) (θ : unitInterval) : GradientOracle d Bool where
  law := Fradin.bernoulliLaw θ
  law_probability := inferInstance
  response := scaledResponse U R η a lam θ
  measurable_response := measurable_scaledResponse U hR η a lam θ

theorem integral_scaledResponse {d T : ℕ} (U : Fin T → Point d)
    (R η a lam : ℝ) (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x : Point d) :
    (∫ D, scaledResponse U R η a lam θ x D ∂Fradin.bernoulliLaw θ) =
      scaledPopulationGradient U R η a lam x := by
  unfold scaledResponse scaledPopulationGradient
  rw [integral_smul, integral_response U R η θ hθ]

theorem integral_scaled_centered_rpow_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R a : ℝ} (hR : 0 < R) (ha : 0 ≤ a)
    (η lam : ℝ) (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (x : Point d) {p : ℝ} (hp : 1 ≤ p) :
    (∫ D, ‖scaledResponse U R η a lam θ x D -
      scaledPopulationGradient U R η a lam x‖ ^ p ∂Fradin.bernoulliLaw θ) ≤
      a ^ p * (2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) := by
  have hfun : (fun D => ‖scaledResponse U R η a lam θ x D -
      scaledPopulationGradient U R η a lam x‖ ^ p) =
      (fun D => a ^ p * ‖response U R η θ (lam⁻¹ • x) D -
        populationGradient U R η (lam⁻¹ • x)‖ ^ p) := by
    funext D
    rw [scaledResponse, scaledPopulationGradient, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha, Real.mul_rpow ha (norm_nonneg _)]
  rw [hfun, integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_centered_rpow_le hU hR η θ hθ _ hp) (Real.rpow_nonneg ha _)

theorem integral_scaled_increment_rpow_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) {a lam : ℝ}
    (ha : 0 ≤ a) (hlam : 0 < lam) (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (x y : Point d) {q : ℝ} (hq : 1 ≤ q) :
    (∫ D, ‖scaledResponse U (liftRadius T) (1/5) a lam θ x D -
      scaledResponse U (liftRadius T) (1/5) a lam θ y D‖ ^ q ∂Fradin.bernoulliLaw θ) ≤
      (a ^ q * (7000 : ℝ) ^ q * (lam⁻¹) ^ q / (θ : ℝ) ^ (q - 1)) * ‖x-y‖ ^ q := by
  have hfun : (fun D => ‖scaledResponse U (liftRadius T) (1/5) a lam θ x D -
      scaledResponse U (liftRadius T) (1/5) a lam θ y D‖ ^ q) =
      (fun D => a ^ q * ‖response U (liftRadius T) (1/5) θ (lam⁻¹ • x) D -
        response U (liftRadius T) (1/5) θ (lam⁻¹ • y) D‖ ^ q) := by
    funext D
    rw [scaledResponse, scaledResponse, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha, Real.mul_rpow ha (norm_nonneg _)]
  have hdist : ‖lam⁻¹ • x - lam⁻¹ • y‖ ^ q = (lam⁻¹) ^ q * ‖x-y‖ ^ q := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hlam.le),
      Real.mul_rpow (inv_nonneg.mpr hlam.le) (norm_nonneg _)]
  rw [hfun, integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (lift_integral_increment_rpow_le hU hT θ hθ (lam⁻¹ • x) (lam⁻¹ • y) hq)
    (Real.rpow_nonneg ha q)
  rw [hdist] at h
  convert h using 1 <;> ring

/-- Actual shared-model legality, with only three explicit scalar checks. -/
def scaledAdmissible {d T : ℕ} (hd : 0 < d) (U : Fin T → Point d)
    (hU : Orthonormal ℝ U) (hT : 0 < T) {p q Δ σ L a lam : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hL : 0 < L)
    (ha : 0 < a) (hlam : 0 < lam) (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (hgap : a * lam * (12 * T) ≤ Δ)
    (hmoment : a ^ p *
      (2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) ≤ σ ^ p)
    (hincrement : a ^ q * (7000 : ℝ) ^ q * (lam⁻¹) ^ q / (θ : ℝ) ^ (q - 1) ≤ L ^ q) :
    Admissible d Bool p q Δ σ L where
  objective := {
    dimension_pos := hd
    value := scaledPotential U (liftRadius T) (1/5) a lam
    grad := scaledPopulationGradient U (liftRadius T) (1/5) a lam
    hasGradientAt := hasGradientAt_scaledPotential U (liftRadius_pos hT) hlam (1/5) a
    continuous_grad := continuous_scaledPopulationGradient U (liftRadius_pos hT) (1/5) a lam
    gap := fun x => (scaledPotential_gap_le U (liftRadius T) lam
      (by norm_num : (0 : ℝ) ≤ 1/5) ha.le hlam.le x).trans hgap }
  oracle := scaledOracle U (liftRadius_pos hT) (1/5) a lam θ
  p_range := hp
  q_range := hq
  delta_pos := hΔ
  sigma_nonneg := hσ
  Lbar_pos := hL
  integrable_response := fun _ => Fradin.integrable_bernoulliLaw θ _
  unbiased := integral_scaledResponse U (liftRadius T) (1/5) a lam θ hθ
  centered_moment := by
    intro x
    change (∫⁻ D, ENNReal.ofReal (‖scaledResponse U (liftRadius T) (1/5) a lam θ x D -
      scaledPopulationGradient U (liftRadius T) (1/5) a lam x‖ ^ p)
      ∂Fradin.bernoulliLaw θ) ≤ ENNReal.ofReal (σ ^ p)
    rw [← ofReal_integral_eq_lintegral_ofReal (Fradin.integrable_bernoulliLaw θ _)
      (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) p))]
    exact ENNReal.ofReal_le_ofReal
      ((integral_scaled_centered_rpow_le hU (liftRadius_pos hT) ha.le (1/5) lam θ hθ x hp.1.le).trans hmoment)
  same_seed_increment := by
    intro x y
    change (∫⁻ D, ENNReal.ofReal (‖scaledResponse U (liftRadius T) (1/5) a lam θ x D -
      scaledResponse U (liftRadius T) (1/5) a lam θ y D‖ ^ q)
      ∂Fradin.bernoulliLaw θ) ≤ ENNReal.ofReal ((L * ‖x-y‖) ^ q)
    rw [← ofReal_integral_eq_lintegral_ofReal (Fradin.integrable_bernoulliLaw θ _)
      (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) q))]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (a ^ q * (7000 : ℝ) ^ q * (lam⁻¹) ^ q / (θ : ℝ) ^ (q - 1)) * ‖x-y‖ ^ q :=
        integral_scaled_increment_rpow_le hU hT ha.le hlam θ hθ x y hq
      _ ≤ L ^ q * ‖x-y‖ ^ q := mul_le_mul_of_nonneg_right hincrement
        (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (L * ‖x-y‖) ^ q := (Real.mul_rpow hL.le (norm_nonneg _)).symm

theorem scaledResponse_rescaling {d T : ℕ} (U : Fin T → Point d)
    (R η a : ℝ) {lam : ℝ} (hlam : 0 < lam) (θ : unitInterval) (y : Point d) (D : Bool) :
    scaledResponse U R η a lam θ (lam • y) D = a • response U R η θ y D := by
  simp [scaledResponse, smul_smul, hlam.ne']

theorem scaled_runOutput_identity {d T N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (U : Fin T → Point d) {R lam : ℝ}
    (hR : 0 < R) (hlam : 0 < lam) (η a : ℝ) (θ : unitInterval)
    (A : RandomAlgorithm d N Private) (r : Private) (seeds : Fin N → Bool) :
    (rescaledAlgorithm lam a A).output r
      (runTranscript (oracle U hR η θ) (rescaledAlgorithm lam a A) r N seeds) =
      lam⁻¹ • A.output r (runTranscript (scaledOracle U hR η a lam θ) A r N seeds) := by
  apply rescaledAlgorithm_output_identity hlam
  intro y D
  exact scaledResponse_rescaling U R η a hlam θ y D

/-- The same private law and the same finite fresh tape are used in both
experiments. This identity includes the arbitrary response-free output. -/
theorem scaled_actualOutput_risk_identity {d T N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (U : Fin T → Point d) {R a lam : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (hlam : 0 < lam) (η : ℝ) (θ : unitInterval)
    (A : RandomAlgorithm d N Private) :
    (∫⁻ r, ∫⁻ seeds, ENNReal.ofReal ‖scaledPopulationGradient U R η a lam
      (A.output r (runTranscript (scaledOracle U hR η a lam θ) A r N seeds))‖
      ∂freshSeedLaw (scaledOracle U hR η a lam θ) N ∂A.privateLaw) =
    ENNReal.ofReal a *
      ∫⁻ r, ∫⁻ seeds, ENNReal.ofReal ‖populationGradient U R η
        ((rescaledAlgorithm lam a A).output r
          (runTranscript (oracle U hR η θ) (rescaledAlgorithm lam a A) r N seeds))‖
        ∂freshSeedLaw (oracle U hR η θ) N ∂(rescaledAlgorithm lam a A).privateLaw := by
  have hpoint (r : Private) (seeds : Fin N → Bool) :
      ENNReal.ofReal ‖scaledPopulationGradient U R η a lam
        (A.output r (runTranscript (scaledOracle U hR η a lam θ) A r N seeds))‖ =
      ENNReal.ofReal a * ENNReal.ofReal ‖populationGradient U R η
        ((rescaledAlgorithm lam a A).output r
          (runTranscript (oracle U hR η θ) (rescaledAlgorithm lam a A) r N seeds))‖ := by
    rw [scaledPopulationGradient, ← scaled_runOutput_identity U hR hlam η a θ A r seeds,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, ENNReal.ofReal_mul ha]
  simp_rw [hpoint]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

theorem scaled_stationarity_barrier {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) {a : ℝ} (ha : 0 ≤ a)
    (lam : ℝ) (x : Point d)
    (hmissing : ∃ i : Fin T, |coordinates U (liftRadius T) (lam⁻¹ • x) i| < 1) :
    a / 2 ≤ ‖scaledPopulationGradient U (liftRadius T) (1/5) a lam x‖ := by
  have h := mul_le_mul_of_nonneg_left (lift_stationarity_barrier hU hT (lam⁻¹ • x) hmissing) ha
  simpa [scaledPopulationGradient, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
    div_eq_mul_inv] using h

end
end HeavyTailedNoise.RandomizedLift
