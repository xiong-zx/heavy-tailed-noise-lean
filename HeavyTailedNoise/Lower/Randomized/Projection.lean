import HeavyTailedNoise.Lower.Randomized.Basic

namespace HeavyTailedNoise.RandomizedLift

open MeasureTheory
open scoped ENNReal
noncomputable section

/-- A direct two-atom calculation, valid for every finite real exponent q≥1. -/
theorem bernoulli_integral_rpow_le {d : ℕ} (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (f : Bool → Point d) {C q : ℝ} (hC : 0 ≤ C) (hq : 1 ≤ q)
    (hf : ‖f false‖ ≤ C) (ht : ‖f true‖ ≤ C / θ) :
    (∫ D, ‖f D‖ ^ q ∂Fradin.bernoulliLaw θ) ≤
      (2 * C) ^ q / (θ : ℝ) ^ (q - 1) := by
  have hq0 : 0 ≤ q := by linarith
  have htpow : 0 < (θ : ℝ) ^ (q - 1) := Real.rpow_pos_of_pos hθ _
  have htpowle : (θ : ℝ) ^ (q - 1) ≤ 1 :=
    Real.rpow_le_one hθ.le θ.property.2 (by linarith)
  have htrue := Real.rpow_le_rpow (norm_nonneg _) ht hq0
  have hfalse := Real.rpow_le_rpow (norm_nonneg _) hf hq0
  have hident : (θ : ℝ) * (C / θ) ^ q = C ^ q / (θ : ℝ) ^ (q - 1) := by
    rw [Real.div_rpow hC hθ.le, Real.rpow_sub hθ, Real.rpow_one]
    field_simp [ne_of_gt hθ, ne_of_gt (Real.rpow_pos_of_pos hθ q)]
  have hsecond : (1 - (θ : ℝ)) * C ^ q ≤ C ^ q / (θ : ℝ) ^ (q - 1) := by
    apply (le_div_iff₀ htpow).mpr
    have hfac : (1 - (θ : ℝ)) * (θ : ℝ) ^ (q - 1) ≤ 1 := by
      exact (mul_le_mul (by linarith [θ.property.1] : 1 - (θ : ℝ) ≤ 1)
        htpowle (Real.rpow_nonneg hθ.le _) (by norm_num)).trans (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg hC q)
    nlinarith
  have h2q : (2 : ℝ) ≤ (2 : ℝ) ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq
  have hconstant : 2 * C ^ q ≤ (2 * C) ^ q := by
    rw [Real.mul_rpow (by norm_num) hC]
    exact mul_le_mul_of_nonneg_right h2q (Real.rpow_nonneg hC _)
  rw [Fradin.integral_bernoulliLaw]
  simp only [smul_eq_mul]
  calc
    _ ≤ (θ : ℝ) * (C / θ) ^ q + (1 - (θ : ℝ)) * C ^ q :=
      add_le_add (mul_le_mul_of_nonneg_left htrue hθ.le)
        (mul_le_mul_of_nonneg_left hfalse (sub_nonneg.mpr θ.property.2))
    _ ≤ 2 * (C ^ q / (θ : ℝ) ^ (q - 1)) := by rw [hident]; linarith
    _ = (2 * C ^ q) / (θ : ℝ) ^ (q - 1) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hconstant htpow.le

theorem norm_bernoulliResponse_false_le {T : ℕ} (θ : unitInterval) (z : Point T) :
    ‖Fradin.bernoulliResponse θ z false‖ ≤ 23 * Real.sqrt T + 23 := by
  have heq : Fradin.bernoulliResponse θ z false = carmonChainGradient z - Fradin.maskedGradient z := by
    simp [Fradin.bernoulliResponse, Fradin.noiseFactor, sub_eq_add_neg]
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add (norm_carmonChainGradient_le_23_sqrt z)
    (Fradin.norm_maskedGradient_le_23 z))

theorem norm_bernoulliResponse_true_le {T : ℕ} (θ : unitInterval)
    (hθ : 0 < (θ : ℝ)) (z : Point T) :
    ‖Fradin.bernoulliResponse θ z true‖ ≤ (23 * Real.sqrt T + 23) / θ := by
  have hn := Fradin.noiseFactor_true_nonneg θ hθ
  have hnoise : Fradin.noiseFactor θ true ≤ 1 / (θ : ℝ) := by
    rw [Fradin.noiseFactor_true_eq θ hθ]
    exact div_le_div_of_nonneg_right (by linarith [θ.property.1]) hθ.le
  have hG : 23 * Real.sqrt T ≤ (23 * Real.sqrt T) / (θ : ℝ) :=
    (le_div_iff₀ hθ).mpr (by nlinarith [θ.property.2, Real.sqrt_nonneg (T : ℝ)])
  calc
    _ ≤ ‖carmonChainGradient z‖ + ‖Fradin.noiseFactor θ true • Fradin.maskedGradient z‖ := norm_add_le _ _
    _ ≤ 23 * Real.sqrt T + (1 / (θ : ℝ)) * 23 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
      exact add_le_add (norm_carmonChainGradient_le_23_sqrt z)
        (mul_le_mul hnoise (Fradin.norm_maskedGradient_le_23 z) (norm_nonneg _) (by positivity))
    _ ≤ (23 * Real.sqrt T) / θ + 23 / θ := by
      exact add_le_add hG (by ring_nf; exact le_refl _)
    _ = (23 * Real.sqrt T + 23) / θ := by ring

/-- The Jacobian-variation term has an actual finite-q absolute oracle moment. -/
theorem integral_absolute_bernoulliResponse_rpow_le {T : ℕ} (θ : unitInterval)
    (hθ : 0 < (θ : ℝ)) (z : Point T) {q : ℝ} (hq : 1 ≤ q) :
    (∫ D, ‖Fradin.bernoulliResponse θ z D‖ ^ q ∂Fradin.bernoulliLaw θ) ≤
      (2 * (23 * Real.sqrt T + 23)) ^ q / (θ : ℝ) ^ (q - 1) :=
  bernoulli_integral_rpow_le θ hθ _ (by positivity) hq
    (norm_bernoulliResponse_false_le θ z) (norm_bernoulliResponse_true_le θ hθ z)

theorem absolute_bernoulliResponse_moment_le {T : ℕ} (θ : unitInterval)
    (hθ : 0 < (θ : ℝ)) (z : Point T) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ D, ENNReal.ofReal (‖Fradin.bernoulliResponse θ z D‖ ^ q) ∂Fradin.bernoulliLaw θ) ≤
      ENNReal.ofReal ((2 * (23 * Real.sqrt T + 23)) ^ q / (θ : ℝ) ^ (q - 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Fradin.integrable_bernoulliLaw θ _)
    (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) _))]
  exact ENNReal.ofReal_le_ofReal (integral_absolute_bernoulliResponse_rpow_le θ hθ z hq)

theorem norm_response_false_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (θ : unitInterval) (x : Point d) :
    ‖response U R η θ x false‖ ≤ 23 * Real.sqrt T + 23 + |η| * ‖x‖ := by
  exact (norm_add_le _ _).trans (by
    rw [norm_smul, Real.norm_eq_abs]
    exact add_le_add ((norm_transport_apply_le hU hR x _).trans
      (norm_bernoulliResponse_false_le θ _)) le_rfl)

theorem norm_response_true_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x : Point d) :
    ‖response U R η θ x true‖ ≤ (23 * Real.sqrt T + 23 + |η| * ‖x‖) / θ := by
  have hreg : |η| * ‖x‖ ≤ (|η| * ‖x‖) / (θ : ℝ) :=
    (le_div_iff₀ hθ).mpr (by nlinarith [θ.property.2, mul_nonneg (abs_nonneg η) (norm_nonneg x)])
  exact (norm_add_le _ _).trans (by
    rw [norm_smul, Real.norm_eq_abs]
    have hb := (norm_transport_apply_le hU hR x
      (Fradin.bernoulliResponse θ (coordinates U R x) true)).trans
        (norm_bernoulliResponse_true_le θ hθ (coordinates U R x))
    simpa only [add_div] using add_le_add hb hreg)

theorem integral_absolute_response_rpow_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x : Point d) {q : ℝ} (hq : 1 ≤ q) :
    (∫ D, ‖response U R η θ x D‖ ^ q ∂Fradin.bernoulliLaw θ) ≤
      (2 * (23 * Real.sqrt T + 23 + |η| * ‖x‖)) ^ q / (θ : ℝ) ^ (q - 1) :=
  bernoulli_integral_rpow_le θ hθ _ (by positivity) hq
    (norm_response_false_le hU hR η θ x) (norm_response_true_le hU hR η θ hθ x)

theorem absolute_response_moment_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x : Point d) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ D, ENNReal.ofReal (‖response U R η θ x D‖ ^ q) ∂Fradin.bernoulliLaw θ) ≤
      ENNReal.ofReal ((2 * (23 * Real.sqrt T + 23 + |η| * ‖x‖)) ^ q / (θ : ℝ) ^ (q - 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Fradin.integrable_bernoulliLaw θ _)
    (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) _))]
  exact ENNReal.ofReal_le_ofReal (integral_absolute_response_rpow_le hU hR η θ hθ x hq)

theorem norm_softProjection_sub_le {d : ℕ} {R : ℝ} (hR : 0 < R) (x y : Point d) :
    ‖softProjection R x - softProjection R y‖ ≤ ‖x - y‖ := by
  have hf := (contDiff_softProjection_two (d := d) hR).differentiable (by norm_num)
  have hl : LipschitzWith 1 (softProjection (d := d) R) :=
    lipschitzWith_of_nnnorm_fderiv_le hf (fun x => by exact_mod_cast norm_fderiv_softProjection_le_one hR x)
  simpa using hl.norm_sub_le x y

theorem norm_coordinates_sub_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (x y : Point d) :
    ‖coordinates U R x - coordinates U R y‖ ≤ ‖x - y‖ := by
  rw [coordinates_eq_adjoint, ← map_sub]
  calc
    _ ≤ ‖(frameEmbed U).adjoint‖ * ‖softProjection R x - softProjection R y‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x - y‖ := mul_le_mul (by simpa using norm_frameEmbed_le_one hU)
      (norm_softProjection_sub_le hR x y) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem norm_fderiv_softProjection_sub_le {d : ℕ} {R : ℝ} (hR : 0 < R)
    (x y : Point d) :
    ‖fderiv ℝ (softProjection R) x - fderiv ℝ (softProjection R) y‖ ≤ (6 / R) * ‖x - y‖ := by
  have hf : Differentiable ℝ (fderiv ℝ (softProjection (d := d) R)) :=
    ((contDiff_softProjection_two hR).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  let C : NNReal := ⟨6 / R, by positivity⟩
  have hl : LipschitzWith C (fderiv ℝ (softProjection (d := d) R)) :=
    lipschitzWith_of_nnnorm_fderiv_le hf (fun x => by
      exact_mod_cast norm_second_fderiv_softProjection_le_six_div_radius hR x)
  exact hl.norm_sub_le x y

theorem norm_transport_sub_apply_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R)
    (x y : Point d) (z : Point T) :
    ‖(transport U R x - transport U R y) z‖ ≤ (6 / R) * ‖x - y‖ * ‖z‖ := by
  have heq : transport U R x - transport U R y =
      (fderiv ℝ (softProjection R) x - fderiv ℝ (softProjection R) y).adjoint.comp (frameEmbed U) := by
    simp [transport, map_sub, ContinuousLinearMap.sub_comp]
  rw [heq, ContinuousLinearMap.comp_apply]
  calc
    _ ≤ ‖(fderiv ℝ (softProjection R) x - fderiv ℝ (softProjection R) y).adjoint‖ * ‖frameEmbed U z‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((6 / R) * ‖x - y‖) * ‖z‖ := by
      rw [norm_frameEmbed_apply hU]
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul_of_nonneg_right (norm_fderiv_softProjection_sub_le hR x y)
        (norm_nonneg z)

theorem response_increment_decomposition {d T : ℕ} (U : Fin T → Point d)
    (R η : ℝ) (θ : unitInterval) (x y : Point d) (D : Bool) :
    response U R η θ x D - response U R η θ y D =
      transport U R x (Fradin.bernoulliResponse θ (coordinates U R x) D -
        Fradin.bernoulliResponse θ (coordinates U R y) D) +
      (transport U R x - transport U R y) (Fradin.bernoulliResponse θ (coordinates U R y) D) +
      η • (x - y) := by
  simp only [response, map_sub, ContinuousLinearMap.sub_apply, smul_sub]
  abel

theorem norm_response_increment_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (θ : unitInterval) (x y : Point d) (D : Bool) :
    ‖response U R η θ x D - response U R η θ y D‖ ≤
      ‖Fradin.bernoulliResponse θ (coordinates U R x) D -
        Fradin.bernoulliResponse θ (coordinates U R y) D‖ +
      (6 / R) * ‖x - y‖ * ‖Fradin.bernoulliResponse θ (coordinates U R y) D‖ +
      |η| * ‖x - y‖ := by
  rw [response_increment_decomposition]
  exact (norm_add_le _ _).trans (by
    rw [norm_smul, Real.norm_eq_abs]
    exact add_le_add ((norm_add_le _ _).trans (add_le_add
      (norm_transport_apply_le hU hR x _)
      (norm_transport_sub_apply_le hU hR x y _))) le_rfl)

theorem norm_response_false_increment_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (θ : unitInterval) (x y : Point d) :
    ‖response U R η θ x false - response U R η θ y false‖ ≤
      ((6087 / 2 : ℝ) + (6 / R) * (23 * Real.sqrt T + 23) + |η|) * ‖x - y‖ := by
  have hg := (Fradin.bernoulliResponse_false_sub_bound hT θ
    (coordinates U R x) (coordinates U R y)).trans
      (mul_le_mul_of_nonneg_left (norm_coordinates_sub_le hU hR x y) (by norm_num))
  have hb := mul_le_mul_of_nonneg_left (norm_bernoulliResponse_false_le θ (coordinates U R y))
    (show 0 ≤ (6 / R) * ‖x-y‖ by positivity)
  exact (norm_response_increment_le hU hR η θ x y false).trans (by nlinarith)

theorem norm_response_true_increment_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x y : Point d) :
    ‖response U R η θ x true - response U R η θ y true‖ ≤
      (((6087 / 2 : ℝ) + (6 / R) * (23 * Real.sqrt T + 23) + |η|) * ‖x - y‖) / θ := by
  have hg := (Fradin.bernoulliResponse_true_sub_bound hT θ hθ
    (coordinates U R x) (coordinates U R y)).trans
      (mul_le_mul_of_nonneg_left (norm_coordinates_sub_le hU hR x y) (by positivity))
  have hb := mul_le_mul_of_nonneg_left (norm_bernoulliResponse_true_le θ hθ (coordinates U R y))
    (show 0 ≤ (6 / R) * ‖x-y‖ by positivity)
  have hreg : |η| * ‖x-y‖ ≤ (|η| * ‖x-y‖) / (θ : ℝ) :=
    (le_div_iff₀ hθ).mpr (by nlinarith [θ.property.2, mul_nonneg (abs_nonneg η) (norm_nonneg (x-y))])
  have heq :
      ((6087 / 2 : ℝ) / θ) * ‖x-y‖ + (6 / R) * ‖x-y‖ * ((23 * Real.sqrt T + 23) / θ) +
        (|η| * ‖x-y‖) / θ =
      (((6087 / 2 : ℝ) + (6 / R) * (23 * Real.sqrt T + 23) + |η|) * ‖x-y‖) / θ := by ring
  exact (norm_response_increment_le hU hR η θ x y true).trans (by rw [← heq]; linarith)

/-- Concrete transport theorem, instantiated with the actual Jacobian and Bernoulli formula. -/
theorem integral_increment_rpow_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x y : Point d) {q : ℝ} (hq : 1 ≤ q) :
    (∫ D, ‖response U R η θ x D - response U R η θ y D‖ ^ q ∂Fradin.bernoulliLaw θ) ≤
      (2 * ((6087 / 2 : ℝ) + (6 / R) * (23 * Real.sqrt T + 23) + |η|)) ^ q /
        (θ : ℝ) ^ (q - 1) * ‖x-y‖ ^ q := by
  have h := bernoulli_integral_rpow_le θ hθ
    (fun D => response U R η θ x D - response U R η θ y D)
    (by positivity) hq (norm_response_false_increment_le hU hT hR η θ x y)
      (norm_response_true_increment_le hU hT hR η θ hθ x y)
  convert h using 1
  rw [← mul_assoc (2 : ℝ), Real.mul_rpow (by positivity) (norm_nonneg _)]
  ring

def liftRadius (T : ℕ) : ℝ := 1000 * Real.sqrt T

theorem liftRadius_pos {T : ℕ} (hT : 0 < T) : 0 < liftRadius T := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  unfold liftRadius
  positivity

theorem lift_increment_constant_le {T : ℕ} (hT : 0 < T) :
    2 * ((6087 / 2 : ℝ) + (6 / liftRadius T) * (23 * Real.sqrt T + 23) + |(1 / 5 : ℝ)|) ≤ 7000 := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast Nat.succ_le_of_lt hT
  have hs : 1 ≤ Real.sqrt T := by
    have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ T)
    nlinarith [Real.sqrt_nonneg (T : ℝ)]
  have hR := liftRadius_pos hT
  have hquot : (6 / liftRadius T) * (23 * Real.sqrt T + 23) ≤ (276 / 1000 : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hR).mpr
    unfold liftRadius
    nlinarith
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1/5)]
  linarith

theorem lift_integral_increment_rpow_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (x y : Point d) {q : ℝ} (hq : 1 ≤ q) :
    (∫ D, ‖response U (liftRadius T) (1/5) θ x D - response U (liftRadius T) (1/5) θ y D‖ ^ q
      ∂Fradin.bernoulliLaw θ) ≤ (7000 : ℝ) ^ q / (θ : ℝ) ^ (q - 1) * ‖x-y‖ ^ q := by
  have hR : 0 < liftRadius T := liftRadius_pos hT
  have hC : 0 ≤ 2 * ((6087 / 2 : ℝ) +
      (6 / liftRadius T) * (23 * Real.sqrt T + 23) + |(1 / 5 : ℝ)|) := by positivity
  exact (integral_increment_rpow_le hU hT (liftRadius_pos hT) (1/5) θ hθ x y hq).trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow hC (lift_increment_constant_le hT) (by linarith))
      (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _))

theorem lift_same_seed_increment_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (x y : Point d) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ D, ENNReal.ofReal (‖response U (liftRadius T) (1/5) θ x D -
      response U (liftRadius T) (1/5) θ y D‖ ^ q) ∂Fradin.bernoulliLaw θ) ≤
      ENNReal.ofReal ((7000 : ℝ) ^ q / (θ : ℝ) ^ (q - 1) * ‖x-y‖ ^ q) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Fradin.integrable_bernoulliLaw θ _)
    (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) _))]
  exact ENNReal.ofReal_le_ofReal (lift_integral_increment_rpow_le hU hT θ hθ x y hq)

end
end HeavyTailedNoise.RandomizedLift
