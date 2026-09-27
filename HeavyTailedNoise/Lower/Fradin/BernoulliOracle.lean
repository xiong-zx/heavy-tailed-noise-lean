import HeavyTailedNoise.Analysis.CarmonChainProperties
import HeavyTailedNoise.Lower.Fradin.SmoothMask
import HeavyTailedNoise.Lower.Fradin.BernoulliNoise

/-!
The genuine smoothed Bernoulli gradient estimator of Fradin v2, B.3/C.2.
The population gradient is the unique gradient from CarmonChainProperties.
The support argument uses the 1/2 frontier: the source's 1/4 index in C.2
does not locate the nonzero noise coordinate for a smoothed selector.
-/

namespace HeavyTailedNoise.Fradin

open HeavyTailedNoise MeasureTheory
open scoped ENNReal
noncomputable section

/-- The actual vector whose single possible coordinate is randomized. -/
def maskedGradient {T : ℕ} (x : Point T) : Point T :=
  WithLp.toLp 2 (fun i => carmonChainGradient x i * mask i x)

theorem maskedGradient_apply {T : ℕ} (x : Point T) (i : Fin T) :
    maskedGradient x i = carmonChainGradient x i * mask i x := rfl

theorem maskedGradient_eq_zero_after_nonzero {T : ℕ} (x : Point T) (i j : Fin T)
    (hi : maskedGradient x i ≠ 0) (hij : i < j) : maskedGradient x j = 0 := by
  have hmask : mask i x ≠ 0 := (mul_ne_zero_iff.mp hi).2
  have htail : ∀ k : Fin T, i.val ≤ k.val → |x k| ≤ 1 / 2 := by
    intro k hk
    exact (suffix_small_of_mask_ne_zero i x hmask k hk).le
  have hgrad := carmonChainGradient_tail_eq_zero x htail j
    (show i.val + 1 ≤ j.val by exact hij)
  simp [hgrad, maskedGradient_apply]

theorem maskedGradient_at_most_one {T : ℕ} (x : Point T) (i j : Fin T)
    (hi : maskedGradient x i ≠ 0) (hj : maskedGradient x j ≠ 0) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (hj (maskedGradient_eq_zero_after_nonzero x i j hi hij))
  · exact hij
  · exact False.elim (hi (maskedGradient_eq_zero_after_nonzero x j i hj hij))

theorem abs_maskedGradient_apply_le_23 {T : ℕ} (x : Point T) (i : Fin T) :
    |maskedGradient x i| ≤ 23 := by
  rw [maskedGradient_apply, abs_mul, abs_of_nonneg (mask_nonneg i x)]
  exact (mul_le_mul_of_nonneg_right (abs_carmonChainGradient_apply_le_23 x i)
    (mask_nonneg i x)).trans (by nlinarith [mask_le_one i x])

theorem norm_maskedGradient_le_23 {T : ℕ} (x : Point T) :
    ‖maskedGradient x‖ ≤ 23 := by
  classical
  by_cases h : ∃ i, maskedGradient x i ≠ 0
  · obtain ⟨i, hi⟩ := h
    have heq : maskedGradient x = PiLp.single 2 i (maskedGradient x i) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp
      · have hj : maskedGradient x j = 0 := by
          by_contra hj
          exact hji (maskedGradient_at_most_one x j i hj hi)
        simp [PiLp.single_apply, hji, hj]
    rw [heq, PiLp.norm_single, Real.norm_eq_abs]
    exact abs_maskedGradient_apply_le_23 x i
  · have heq : maskedGradient x = 0 := by
      ext i
      exact not_ne_iff.mp (fun hi => h ⟨i, hi⟩)
    simp [heq]

theorem maskedGradient_single {T : ℕ} (hT : 0 < T) (x : Point T) :
    ∃ i : Fin T, maskedGradient x = PiLp.single 2 i (maskedGradient x i) := by
  classical
  by_cases h : ∃ i, maskedGradient x i ≠ 0
  · obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · have hj : maskedGradient x j = 0 := by
        by_contra hj
        exact hji (maskedGradient_at_most_one x j i hj hi)
      simp [PiLp.single_apply, hji, hj]
  · refine ⟨⟨0, hT⟩, ?_⟩
    have hz (i : Fin T) : maskedGradient x i = 0 :=
      not_ne_iff.mp (fun hi => h ⟨i, hi⟩)
    ext j
    simp [PiLp.single_apply, hz]

theorem maskedGradient_apply_sub_bound {T : ℕ} (x y : Point T) (i : Fin T) :
    |maskedGradient x i - maskedGradient y i| ≤ (5783 / 4 : ℝ) * ‖x - y‖ := by
  have hcoord : |carmonChainGradient x i - carmonChainGradient y i| ≤
      ‖carmonChainGradient x - carmonChainGradient y‖ := by
    simpa only [Real.norm_eq_abs, PiLp.sub_apply] using
      PiLp.norm_apply_le (carmonChainGradient x - carmonChainGradient y) i
  have hgrad := hcoord.trans (norm_carmonChainGradient_sub_le_152 x y)
  have heq : maskedGradient x i - maskedGradient y i =
      carmonChainGradient x i * (mask i x - mask i y) +
        (carmonChainGradient x i - carmonChainGradient y i) * mask i y := by
    simp only [maskedGradient_apply]
    ring
  rw [heq]
  calc
    _ ≤ |carmonChainGradient x i * (mask i x - mask i y)| +
        |(carmonChainGradient x i - carmonChainGradient y i) * mask i y| := abs_add_le _ _
    _ = |carmonChainGradient x i| * |mask i x - mask i y| +
        |carmonChainGradient x i - carmonChainGradient y i| * mask i y := by
      rw [abs_mul, abs_mul, abs_of_nonneg (mask_nonneg i y)]
    _ ≤ 23 * ((225 / 4 : ℝ) * ‖x - y‖) + (152 * ‖x - y‖) * 1 := by
      exact add_le_add
        (mul_le_mul (abs_carmonChainGradient_apply_le_23 x i) (mask_sub_bound i x y)
          (abs_nonneg _) (by norm_num))
        (mul_le_mul hgrad (mask_le_one i y) (mask_nonneg i y) (by positivity))
    _ = (5783 / 4 : ℝ) * ‖x - y‖ := by ring

theorem maskedGradient_sub_bound {T : ℕ} (hT : 0 < T) (x y : Point T) :
    ‖maskedGradient x - maskedGradient y‖ ≤ (5783 / 2 : ℝ) * ‖x - y‖ := by
  classical
  obtain ⟨i, hi⟩ := maskedGradient_single hT x
  obtain ⟨j, hj⟩ := maskedGradient_single hT y
  by_cases hij : i = j
  · subst j
    have heq : maskedGradient x - maskedGradient y =
        PiLp.single 2 i (maskedGradient x i - maskedGradient y i) := by
      conv_lhs => rw [hi, hj]
      rw [PiLp.single_sub]
    rw [heq, PiLp.norm_single, Real.norm_eq_abs]
    exact (maskedGradient_apply_sub_bound x y i).trans (by nlinarith [norm_nonneg (x-y)])
  · have hxi : maskedGradient x j = 0 := by rw [hi]; simp [PiLp.single_apply, Ne.symm hij]
    have hyj : maskedGradient y i = 0 := by rw [hj]; simp [PiLp.single_apply, hij]
    have heq : maskedGradient x - maskedGradient y =
        PiLp.single 2 i (maskedGradient x i - maskedGradient y i) +
          PiLp.single 2 j (maskedGradient x j - maskedGradient y j) := by
      conv_lhs => rw [hi, hj]
      rw [hyj, hxi, sub_zero, zero_sub, PiLp.single_neg]
      rfl
    rw [heq]
    exact (norm_add_le _ _).trans (by
      rw [PiLp.norm_single, PiLp.norm_single, Real.norm_eq_abs,
        Real.norm_eq_abs]
      linarith [maskedGradient_apply_sub_bound x y i, maskedGradient_apply_sub_bound x y j])

theorem continuous_maskedGradient {T : ℕ} : Continuous (maskedGradient (T := T)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin T => ℝ)).comp
  apply continuous_pi
  intro i
  exact (((PiLp.continuous_apply 2 (fun _ : Fin T => ℝ) i).comp
    (lipschitzWith_carmonChainGradient T).continuous).mul (continuous_mask i))

/-- This is a gradient estimator; no sample potential is imposed. -/
def bernoulliResponse {T : ℕ} (θ : unitInterval) (x : Point T) (ξ : Bool) : Point T :=
  carmonChainGradient x + noiseFactor θ ξ • maskedGradient x

theorem bernoulliResponse_apply {T : ℕ} (θ : unitInterval) (x : Point T) (ξ : Bool)
    (i : Fin T) : bernoulliResponse θ x ξ i =
      carmonChainGradient x i * (1 + mask i x * noiseFactor θ ξ) := by
  simp only [bernoulliResponse, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    maskedGradient_apply]
  ring

theorem integrable_bernoulliResponse {T : ℕ} (θ : unitInterval) (x : Point T) :
    Integrable (bernoulliResponse θ x) (bernoulliLaw θ) :=
  integrable_bernoulliLaw θ _

theorem integral_bernoulliResponse {T : ℕ} (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (x : Point T) : (∫ ξ, bernoulliResponse θ x ξ ∂bernoulliLaw θ) =
      carmonChainGradient x := by
  change (∫ ξ, carmonChainGradient x + noiseFactor θ ξ • maskedGradient x
    ∂bernoulliLaw θ) = carmonChainGradient x
  rw [integral_add (integrable_const _) (integrable_bernoulliLaw θ _),
    integral_const, integral_smul_const, integral_noiseFactor θ hθ, zero_smul, add_zero]
  simp

theorem measurable_bernoulliResponse {T : ℕ} (θ : unitInterval) :
    Measurable (fun z : Point T × Bool => bernoulliResponse θ z.1 z.2) := by
  apply Measurable.add
  · exact (lipschitzWith_carmonChainGradient T).continuous.measurable.comp measurable_fst
  · exact ((measurable_of_countable (noiseFactor θ)).comp measurable_snd).smul
      (continuous_maskedGradient.measurable.comp measurable_fst)

def bernoulliOracle (T : ℕ) (θ : unitInterval) : GradientOracle T Bool where
  law := bernoulliLaw θ
  law_probability := inferInstance
  response := bernoulliResponse θ
  measurable_response := measurable_bernoulliResponse θ

theorem bernoulliResponse_false_frontier_zero {T n : ℕ} (θ : unitInterval)
    (x : Point T) (hx : ∀ i : Fin T, n ≤ i.val → |x i| ≤ 1 / 4)
    (i : Fin T) (hi : n ≤ i.val) : bernoulliResponse θ x false i = 0 := by
  rw [bernoulliResponse_apply, mask_one_of_suffix_small i x
    (fun k hk => hx k (hi.trans hk))]
  simp [noiseFactor]

/-- Every seed can reveal at most the next coordinate of a robust zero-chain. -/
theorem bernoulliResponse_tail_zero {T n : ℕ} (θ : unitInterval)
    (x : Point T) (hx : ∀ i : Fin T, n ≤ i.val → |x i| ≤ 1 / 2)
    (i : Fin T) (hi : n + 1 ≤ i.val) (ξ : Bool) : bernoulliResponse θ x ξ i = 0 := by
  rw [bernoulliResponse_apply, carmonChainGradient_tail_eq_zero x hx i hi, zero_mul]

theorem bernoulliResponse_sub_gradient {T : ℕ} (θ : unitInterval) (x : Point T)
    (ξ : Bool) : bernoulliResponse θ x ξ - carmonChainGradient x =
      noiseFactor θ ξ • maskedGradient x := by
  simp [bernoulliResponse]

theorem integrable_centered_rpow {T : ℕ} (θ : unitInterval) (x : Point T) (p : ℝ) :
    Integrable (fun ξ => ‖bernoulliResponse θ x ξ - carmonChainGradient x‖ ^ p)
      (bernoulliLaw θ) := integrable_bernoulliLaw θ _

theorem integral_centered_rpow_le {T : ℕ} (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (x : Point T) {p : ℝ} (hp : 1 ≤ p) :
    (∫ ξ, ‖bernoulliResponse θ x ξ - carmonChainGradient x‖ ^ p ∂bernoulliLaw θ) ≤
      2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) := by
  have hfun : (fun ξ => ‖bernoulliResponse θ x ξ - carmonChainGradient x‖ ^ p) =
      (fun ξ => ‖maskedGradient x‖ ^ p * |noiseFactor θ ξ| ^ p) := by
    funext ξ
    rw [bernoulliResponse_sub_gradient, norm_smul, Real.norm_eq_abs,
      Real.mul_rpow (abs_nonneg _) (norm_nonneg _), mul_comm]
  rw [hfun, integral_const_mul]
  have hA : ‖maskedGradient x‖ ^ p ≤ (23 : ℝ) ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) (norm_maskedGradient_le_23 x) (by linarith)
  calc
    _ ≤ (23 : ℝ) ^ p * (2 * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) :=
      mul_le_mul hA (integral_abs_noiseFactor_rpow_le θ hθ hp)
        (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _))
        (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by ring

theorem centered_moment_le {T : ℕ} (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (x : Point T) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ξ, ENNReal.ofReal (‖bernoulliResponse θ x ξ - carmonChainGradient x‖ ^ p)
      ∂bernoulliLaw θ) ≤
      ENNReal.ofReal (2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_centered_rpow θ x p)
    (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) _))]
  exact ENNReal.ofReal_le_ofReal (integral_centered_rpow_le θ hθ x hp)

theorem bernoulliResponse_false_sub_bound {T : ℕ} (hT : 0 < T)
    (θ : unitInterval) (x y : Point T) :
    ‖bernoulliResponse θ x false - bernoulliResponse θ y false‖ ≤
      (6087 / 2 : ℝ) * ‖x - y‖ := by
  have heq : bernoulliResponse θ x false - bernoulliResponse θ y false =
      (carmonChainGradient x - carmonChainGradient y) -
        (maskedGradient x - maskedGradient y) := by
    simp only [bernoulliResponse, noiseFactor, Bool.false_eq_true, ↓reduceIte,
      zero_div, zero_sub, neg_smul, one_smul]
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by
    linarith [norm_carmonChainGradient_sub_le_152 x y, maskedGradient_sub_bound hT x y])

theorem bernoulliResponse_true_sub_bound {T : ℕ} (hT : 0 < T)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x y : Point T) :
    ‖bernoulliResponse θ x true - bernoulliResponse θ y true‖ ≤
      ((6087 / 2 : ℝ) / θ) * ‖x - y‖ := by
  have heq : bernoulliResponse θ x true - bernoulliResponse θ y true =
      (carmonChainGradient x - carmonChainGradient y) +
        noiseFactor θ true • (maskedGradient x - maskedGradient y) := by
    simp only [bernoulliResponse, smul_sub]
    abel
  have hnoise := noiseFactor_true_nonneg θ hθ
  have hnoisele : noiseFactor θ true ≤ 1 / (θ : ℝ) := by
    rw [noiseFactor_true_eq θ hθ]
    exact div_le_div_of_nonneg_right (by linarith [θ.property.1]) hθ.le
  have h152 : (152 : ℝ) ≤ 152 / (θ : ℝ) :=
    (le_div_iff₀ hθ).mpr (by nlinarith [θ.property.2])
  rw [heq]
  calc
    _ ≤ ‖carmonChainGradient x - carmonChainGradient y‖ +
        ‖noiseFactor θ true • (maskedGradient x - maskedGradient y)‖ := norm_add_le _ _
    _ = ‖carmonChainGradient x - carmonChainGradient y‖ +
        noiseFactor θ true * ‖maskedGradient x - maskedGradient y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnoise]
    _ ≤ 152 * ‖x - y‖ + (1 / (θ : ℝ)) * ((5783 / 2 : ℝ) * ‖x - y‖) :=
      add_le_add (norm_carmonChainGradient_sub_le_152 x y)
        (mul_le_mul hnoisele (maskedGradient_sub_bound hT x y) (norm_nonneg _)
          (by positivity))
    _ ≤ (152 / (θ : ℝ)) * ‖x - y‖ +
        (1 / (θ : ℝ)) * ((5783 / 2 : ℝ) * ‖x - y‖) := by
      exact add_le_add (mul_le_mul_of_nonneg_right h152 (norm_nonneg (x-y))) le_rfl
    _ = ((6087 / 2 : ℝ) / θ) * ‖x - y‖ := by ring

theorem integrable_increment_rpow {T : ℕ} (θ : unitInterval) (x y : Point T) (q : ℝ) :
    Integrable (fun ξ => ‖bernoulliResponse θ x ξ - bernoulliResponse θ y ξ‖ ^ q)
      (bernoulliLaw θ) := integrable_bernoulliLaw θ _

/-- Uniform conservative constant, including q=1. The atom calculation works for all q≥1. -/
theorem integral_increment_rpow_le {T : ℕ} (hT : 0 < T)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x y : Point T) {q : ℝ} (hq : 1 ≤ q) :
    (∫ ξ, ‖bernoulliResponse θ x ξ - bernoulliResponse θ y ξ‖ ^ q ∂bernoulliLaw θ) ≤
      (6087 : ℝ) ^ q / (θ : ℝ) ^ (q - 1) * ‖x - y‖ ^ q := by
  have hq0 : 0 ≤ q := by linarith
  have ht0 : 0 ≤ 1 - (θ : ℝ) := sub_nonneg.mpr θ.property.2
  have htpow : 0 < (θ : ℝ) ^ (q - 1) := Real.rpow_pos_of_pos hθ _
  have htpowle : (θ : ℝ) ^ (q - 1) ≤ 1 :=
    Real.rpow_le_one hθ.le θ.property.2 (by linarith)
  have htrue := Real.rpow_le_rpow (norm_nonneg _)
    (bernoulliResponse_true_sub_bound hT θ hθ x y) hq0
  have hfalse := Real.rpow_le_rpow (norm_nonneg _)
    (bernoulliResponse_false_sub_bound hT θ x y) hq0
  have hident : (θ : ℝ) * (((6087 / 2 : ℝ) / θ) * ‖x - y‖) ^ q =
      ((6087 / 2 : ℝ) * ‖x - y‖) ^ q / (θ : ℝ) ^ (q - 1) := by
    rw [div_mul_eq_mul_div, Real.div_rpow (by positivity) hθ.le,
      Real.rpow_sub hθ, Real.rpow_one]
    field_simp [ne_of_gt hθ, ne_of_gt (Real.rpow_pos_of_pos hθ q)]
  have hsecond : (1 - (θ : ℝ)) * ((6087 / 2 : ℝ) * ‖x - y‖) ^ q ≤
      ((6087 / 2 : ℝ) * ‖x - y‖) ^ q / (θ : ℝ) ^ (q - 1) := by
    apply (le_div_iff₀ htpow).mpr
    have hfac : (1 - (θ : ℝ)) * (θ : ℝ) ^ (q - 1) ≤ 1 := by
      exact (mul_le_mul (by linarith [θ.property.1] : 1 - (θ : ℝ) ≤ 1)
        htpowle (Real.rpow_nonneg hθ.le _) (by norm_num)).trans (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hfac
      (Real.rpow_nonneg (by positivity : 0 ≤ (6087 / 2 : ℝ) * ‖x-y‖) q)
    nlinarith
  have h2q : (2 : ℝ) ≤ (2 : ℝ) ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq
  have hconstant : 2 * (6087 / 2 : ℝ) ^ q ≤ (6087 : ℝ) ^ q := by
    calc
      _ ≤ (2 : ℝ) ^ q * (6087 / 2 : ℝ) ^ q :=
        mul_le_mul_of_nonneg_right h2q (Real.rpow_nonneg (by norm_num) _)
      _ = (6087 : ℝ) ^ q := by rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  rw [integral_bernoulliLaw]
  simp only [smul_eq_mul]
  calc
    _ ≤ (θ : ℝ) * (((6087 / 2 : ℝ) / θ) * ‖x-y‖) ^ q +
        (1 - (θ : ℝ)) * ((6087 / 2 : ℝ) * ‖x-y‖) ^ q :=
      add_le_add (mul_le_mul_of_nonneg_left htrue hθ.le)
        (mul_le_mul_of_nonneg_left hfalse ht0)
    _ ≤ 2 * (((6087 / 2 : ℝ) * ‖x-y‖) ^ q / (θ : ℝ) ^ (q - 1)) := by
      rw [hident]
      linarith
    _ = (2 * (6087 / 2 : ℝ) ^ q) / (θ : ℝ) ^ (q - 1) * ‖x-y‖ ^ q := by
      rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hconstant htpow.le)
      (Real.rpow_nonneg (norm_nonneg _) _)

theorem same_seed_increment_le {T : ℕ} (hT : 0 < T)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x y : Point T) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ ξ, ENNReal.ofReal (‖bernoulliResponse θ x ξ - bernoulliResponse θ y ξ‖ ^ q)
      ∂bernoulliLaw θ) ≤
      ENNReal.ofReal ((6087 : ℝ) ^ q / (θ : ℝ) ^ (q - 1) * ‖x - y‖ ^ q) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_increment_rpow θ x y q)
    (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) _))]
  exact ENNReal.ofReal_le_ofReal (integral_increment_rpow_le hT θ hθ x y hq)

end
end HeavyTailedNoise.Fradin
