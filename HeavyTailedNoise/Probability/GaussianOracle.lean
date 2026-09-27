import HeavyTailedNoise.Model.Basic

/-!
Legality of the additive Gaussian gradient response.  The response is defined using the
standard Gaussian measure on the finite-dimensional Euclidean seed space.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace HeavyTailedNoise

/-- The final oracle's additive response, with a dimension-dependent scalar coefficient. -/
def gaussianResponse (d : ℕ) (grad : Point d → Point d) (a : ℝ)
    (x ξ : Point d) : Point d := grad x + a • ξ

/-- The standard Gaussian seed law is a probability measure. -/
noncomputable def standardGaussianLaw (d : ℕ) : Measure (Point d) :=
  ProbabilityTheory.stdGaussian (Point d)

instance (d : ℕ) : IsProbabilityMeasure (standardGaussianLaw d) := by
  unfold standardGaussianLaw
  infer_instance

instance (d : ℕ) : ProbabilityTheory.IsGaussian (standardGaussianLaw d) := by
  unfold standardGaussianLaw
  infer_instance

lemma measurable_gaussianResponse {d : ℕ} {grad : Point d → Point d}
    (hgrad : Continuous grad) (a : ℝ) :
    Measurable (fun z : Point d × Point d => gaussianResponse d grad a z.1 z.2) := by
  unfold gaussianResponse
  fun_prop

/-- The actual Gaussian law and the additive response form a jointly measurable oracle. -/
def gaussianOracle (d : ℕ) (grad : Point d → Point d)
    (hgrad : Continuous grad) (a : ℝ) : GradientOracle d (Point d) where
  law := standardGaussianLaw d
  law_probability := inferInstance
  response := gaussianResponse d grad a
  measurable_response := measurable_gaussianResponse hgrad a

lemma gaussianResponse_sub (d : ℕ) (grad : Point d → Point d) (a : ℝ)
    (x y ξ : Point d) :
    gaussianResponse d grad a x ξ - gaussianResponse d grad a y ξ = grad x - grad y := by
  unfold gaussianResponse
  abel

lemma integrable_gaussianResponse {d : ℕ} (grad : Point d → Point d) (a : ℝ)
    (x : Point d) :
    Integrable (gaussianResponse d grad a x) (standardGaussianLaw d) := by
  change Integrable (fun ξ : Point d => grad x + a • ξ) (standardGaussianLaw d)
  exact (integrable_const _).add (ProbabilityTheory.IsGaussian.integrable_id.smul a)

lemma integral_gaussianResponse {d : ℕ} (grad : Point d → Point d) (a : ℝ)
    (x : Point d) :
    (∫ ξ, gaussianResponse d grad a x ξ ∂standardGaussianLaw d) = grad x := by
  change (∫ ξ : Point d, grad x + a • ξ ∂standardGaussianLaw d) = grad x
  calc
    (∫ ξ : Point d, grad x + a • ξ ∂standardGaussianLaw d) =
        (∫ _ : Point d, grad x ∂standardGaussianLaw d) +
          (∫ ξ : Point d, a • ξ ∂standardGaussianLaw d) := by
            exact integral_add (integrable_const _)
              (ProbabilityTheory.IsGaussian.integrable_id.smul a)
    _ = grad x := by
      have hsmul : (∫ ξ : Point d, a • ξ ∂standardGaussianLaw d) = 0 := by
        calc
          (∫ ξ : Point d, a • ξ ∂standardGaussianLaw d) =
              a • (∫ ξ : Point d, ξ ∂standardGaussianLaw d) := by
                exact integral_smul a (fun ξ : Point d => ξ)
          _ = 0 := by simp [standardGaussianLaw]
      simp [hsmul]

lemma gaussianOracle_integrable {d : ℕ} (grad : Point d → Point d)
    (hgrad : Continuous grad) (a : ℝ) (x : Point d) :
    Integrable ((gaussianOracle d grad hgrad a).response x)
      (gaussianOracle d grad hgrad a).law :=
  integrable_gaussianResponse grad a x

lemma gaussianOracle_unbiased {d : ℕ} (grad : Point d → Point d)
    (hgrad : Continuous grad) (a : ℝ) (x : Point d) :
    (∫ ξ, (gaussianOracle d grad hgrad a).response x ξ
      ∂(gaussianOracle d grad hgrad a).law) = grad x :=
  integral_gaussianResponse grad a x

lemma gaussianOracle_same_seed_increment {d : ℕ} (grad : Point d → Point d)
    (hgrad : Continuous grad) (a Lbar q : ℝ) (hq : 0 ≤ q)
    (hLip : ∀ x y, ‖grad x - grad y‖ ≤ Lbar * ‖x - y‖)
    (x y : Point d) :
    (∫⁻ ξ, ENNReal.ofReal
      (‖(gaussianOracle d grad hgrad a).response x ξ -
        (gaussianOracle d grad hgrad a).response y ξ‖ ^ q)
      ∂(gaussianOracle d grad hgrad a).law) ≤
      ENNReal.ofReal ((Lbar * ‖x - y‖) ^ q) := by
  change (∫⁻ ξ : Point d,
    ENNReal.ofReal (‖gaussianResponse d grad a x ξ -
      gaussianResponse d grad a y ξ‖ ^ q) ∂standardGaussianLaw d) ≤ _
  simp_rw [gaussianResponse_sub]
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow (norm_nonneg _) (hLip x y) hq)

/-- Exact second moment of the standard Gaussian vector in `d` dimensions. -/
lemma standardGaussian_norm_sq_integral (d : ℕ) :
    (∫ ξ : Point d, ‖ξ‖ ^ 2 ∂standardGaussianLaw d) = (d : ℝ) := by
  let μ : Measure (Point d) := standardGaussianLaw d
  have h2 : MemLp (id : Point d → Point d) 2 μ :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hcoord (i : Fin d) : (∫ ξ : Point d, (ξ i) ^ 2 ∂μ) = 1 := by
    have hmean : (∫ ξ : Point d, ξ i ∂μ) = 0 := by
      have hi := MeasureTheory.eval_integral_piLp
        (f := id) (μ := μ) (fun j => h2.integrable (by norm_num) |>.eval_piLp j) i
      simpa [μ, standardGaussianLaw] using hi.symm
    have hv : ProbabilityTheory.variance (fun ξ : Point d => ξ i) μ = 1 := by
      simpa [μ, standardGaussianLaw, ProbabilityTheory.multivariateGaussian_zero_one] using
        (ProbabilityTheory.variance_eval_multivariateGaussian
          (μ := (0 : Point d)) (S := (1 : Matrix (Fin d) (Fin d) ℝ))
          Matrix.PosSemidef.one i)
    exact (ProbabilityTheory.variance_of_integral_eq_zero (by fun_prop) hmean).symm.trans hv
  have hcoord_int (i : Fin d) : Integrable (fun ξ : Point d => (ξ i) ^ 2) μ := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (h2.eval_piLp i).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  calc
    (∫ ξ : Point d, ‖ξ‖ ^ 2 ∂standardGaussianLaw d) =
        ∫ ξ : Point d, ∑ i : Fin d, (ξ i) ^ 2 ∂μ := by
          simp only [μ, EuclideanSpace.real_norm_sq_eq]
    _ = ∑ i : Fin d, (∫ ξ : Point d, (ξ i) ^ 2 ∂μ) := by
          exact integral_finsetSum _ (fun i _ => hcoord_int i)
    _ = (d : ℝ) := by simp [hcoord]

/-- The standard Gaussian has Euclidean `L²` norm exactly `√d`. -/
lemma standardGaussian_eLpNorm_two (d : ℕ) :
    eLpNorm (id : Point d → Point d) 2 (standardGaussianLaw d) =
      ENNReal.ofReal (Real.sqrt d) := by
  let μ : Measure (Point d) := standardGaussianLaw d
  have h2 : MemLp (id : Point d → Point d) 2 μ :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hInt : Integrable (fun ξ : Point d => ‖ξ‖ ^ 2) μ :=
    h2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hMoment : (∫⁻ ξ : Point d, ‖ξ‖ₑ ^ (2 : ℝ) ∂μ) =
      ENNReal.ofReal d := by
    calc
      (∫⁻ ξ : Point d, ‖ξ‖ₑ ^ (2 : ℝ) ∂μ) =
          ∫⁻ ξ : Point d, ENNReal.ofReal (‖ξ‖ ^ 2) ∂μ := by
            apply lintegral_congr
            intro ξ
            rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg
              (norm_nonneg ξ) (by norm_num : (0 : ℝ) ≤ 2)]
            rw [Real.rpow_two]
      _ = ENNReal.ofReal (∫ ξ : Point d, ‖ξ‖ ^ 2 ∂μ) := by
            exact (ofReal_integral_eq_lintegral_ofReal hInt
              (Filter.Eventually.of_forall (fun ξ => sq_nonneg ‖ξ‖))).symm
      _ = ENNReal.ofReal d := by
            rw [show μ = standardGaussianLaw d from rfl, standardGaussian_norm_sq_integral]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (by fun_prop)]
  change (∫⁻ ξ : Point d, ‖ξ‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) =
    ENNReal.ofReal (Real.sqrt d)
  rw [hMoment, ENNReal.ofReal_rpow_of_nonneg
    (Nat.cast_nonneg d) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [Real.sqrt_eq_rpow]

/-- The Gaussian noise with scale `σ/√d` satisfies the centered `p`-moment budget. -/
lemma standardGaussian_scaled_p_moment {d : ℕ} (hd : 0 < d)
    {p σ : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) :
    (∫⁻ ξ : Point d,
      ENNReal.ofReal (‖(σ / Real.sqrt d) • ξ‖ ^ p) ∂standardGaussianLaw d) ≤
      ENNReal.ofReal (σ ^ p) := by
  let μ : Measure (Point d) := standardGaussianLaw d
  let pn : NNReal := ⟨p, hp.le⟩
  have hpn : (pn : ℝ) = p := rfl
  have hpn_ne : pn ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast hp
  have hpn_le : (pn : ENNReal) ≤ 2 := by
    exact_mod_cast hp2
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have ha : 0 ≤ σ / Real.sqrt d := div_nonneg hσ hsqrt.le
  have hscale : ‖σ / Real.sqrt d‖ₑ * ENNReal.ofReal (Real.sqrt d) =
      ENNReal.ofReal σ := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ha,
      ← ENNReal.ofReal_mul ha]
    rw [div_mul_cancel₀ _ hsqrt.ne']
  have hLp : eLpNorm ((σ / Real.sqrt d) • (id : Point d → Point d)) pn μ ≤
      ENNReal.ofReal σ := by
    calc
      _ = ‖σ / Real.sqrt d‖ₑ * eLpNorm (id : Point d → Point d) pn μ :=
        eLpNorm_const_smul (σ / Real.sqrt d) id pn μ
      _ ≤ ‖σ / Real.sqrt d‖ₑ * eLpNorm (id : Point d → Point d) 2 μ := by
        gcongr
        exact eLpNorm_le_eLpNorm_of_exponent_le hpn_le
      _ = ENNReal.ofReal σ := by
        rw [show μ = standardGaussianLaw d from rfl, standardGaussian_eLpNorm_two]
        exact hscale
  have hmeas : AEStronglyMeasurable
      ((σ / Real.sqrt d) • (id : Point d → Point d)) μ := by fun_prop
  have hmoment : (∫⁻ ξ : Point d,
      ENNReal.ofReal (‖(σ / Real.sqrt d) • ξ‖ ^ p) ∂μ) =
      eLpNorm ((σ / Real.sqrt d) • (id : Point d → Point d)) pn μ ^ p := by
    calc
      _ = (∫⁻ ξ : Point d,
          ‖((σ / Real.sqrt d) • (id : Point d → Point d)) ξ‖ₑ ^ (pn : ℝ) ∂μ) := by
            apply lintegral_congr
            intro ξ
            simp only [hpn, Pi.smul_apply, id_eq]
            rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg
              (norm_nonneg _) hp.le]
      _ = eLpNorm ((σ / Real.sqrt d) • (id : Point d → Point d)) pn μ ^ p := by
            simpa only [hpn] using
              (eLpNorm_nnreal_pow_eq_lintegral (f :=
                ((σ / Real.sqrt d) • (id : Point d → Point d)))
                (μ := μ) (p := pn) hpn_ne hmeas).symm
  calc
    (∫⁻ ξ : Point d, ENNReal.ofReal (‖(σ / Real.sqrt d) • ξ‖ ^ p)
      ∂standardGaussianLaw d) =
        eLpNorm ((σ / Real.sqrt d) • (id : Point d → Point d)) pn μ ^ p := hmoment
    _ ≤ (ENNReal.ofReal σ) ^ p := ENNReal.rpow_le_rpow hLp hp.le
    _ = ENNReal.ofReal (σ ^ p) :=
      ENNReal.ofReal_rpow_of_nonneg hσ hp.le

/-- Legality of the final additive isotropic Gaussian oracle.  The only objective-side input
beyond `Objective` is its global gradient Lipschitz bound. -/
def gaussianAdmissible {d : ℕ} {p q Δ σ Lbar : ℝ}
    (obj : Objective d Δ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hLbar : 0 < Lbar)
    (hLip : ∀ x y, ‖obj.grad x - obj.grad y‖ ≤ Lbar * ‖x - y‖) :
    Admissible d (Point d) p q Δ σ Lbar where
  objective := obj
  oracle := gaussianOracle d obj.grad obj.continuous_grad (σ / Real.sqrt d)
  p_range := hp
  q_range := hq
  delta_pos := hΔ
  sigma_nonneg := hσ
  Lbar_pos := hLbar
  integrable_response := by
    intro x
    exact gaussianOracle_integrable obj.grad obj.continuous_grad _ x
  unbiased := by
    intro x
    exact gaussianOracle_unbiased obj.grad obj.continuous_grad _ x
  centered_moment := by
    intro x
    change (∫⁻ ξ : Point d,
      ENNReal.ofReal (‖gaussianResponse d obj.grad (σ / Real.sqrt d) x ξ -
        obj.grad x‖ ^ p) ∂standardGaussianLaw d) ≤ _
    have heq (ξ : Point d) :
        gaussianResponse d obj.grad (σ / Real.sqrt d) x ξ - obj.grad x =
          (σ / Real.sqrt d) • ξ := by
      unfold gaussianResponse
      abel
    simp_rw [heq]
    exact standardGaussian_scaled_p_moment obj.dimension_pos (by linarith [hp.1])
      hp.2 hσ
  same_seed_increment := by
    intro x y
    exact gaussianOracle_same_seed_increment obj.grad obj.continuous_grad
      (σ / Real.sqrt d) Lbar q (by linarith [hq]) hLip x y

end HeavyTailedNoise
