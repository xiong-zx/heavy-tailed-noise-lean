import HeavyTailedNoise.Probability.HaarConditionalFrame
import HeavyTailedNoise.Lower.Gated.PrefixLocality
import HeavyTailedNoise.Lower.Gated.HardProjectionBounds

/-!
Fixed-prefix spherical cap bounds for the exact projected-Gaussian direction
kernel. Finite query unions require no mutual independence. Random query
families are treated only under an explicitly displayed reference product law.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology Classical

namespace HeavyTailedNoise

noncomputable section

def haarCapAngleSq : ℝ := 1 / (1 + 4 * (1000 + 1 / 16 + 1))

theorem haarCapAngleSq_eq : haarCapAngleSq = (4 / 16021 : ℝ) := by norm_num [haarCapAngleSq]

theorem haarCapAngleSq_pos : 0 < haarCapAngleSq := by norm_num [haarCapAngleSq]

theorem haarCapAngleSq_lt_one : haarCapAngleSq < 1 := by norm_num [haarCapAngleSq]

/-- The actual cap after a fixed prefix and a proposed next direction. -/
def fixedPrefixCap {d j : ℕ} (v : Fin j → Point d) (y : Point d) : Set (Point d) :=
  {u | (1 / 2 : ℝ) ≤ |inner ℝ y u| ∧
    ‖frameResidual v y - inner ℝ y u • u‖ ^ 2 ≤ 1000 + 1 / 16 + 1}

theorem measurableSet_fixedPrefixCap {d j : ℕ} (v : Fin j → Point d) (y : Point d) :
    MeasurableSet (fixedPrefixCap v y) := by
  have h1 : MeasurableSet {u : Point d | (1 / 2 : ℝ) ≤ |inner ℝ y u|} :=
    measurableSet_le measurable_const (by fun_prop)
  have h2 : MeasurableSet {u : Point d | ‖frameResidual v y - inner ℝ y u • u‖ ^ 2 ≤ 1000 + 1 / 16 + 1} :=
    measurableSet_le (by fun_prop) measurable_const
  exact h1.inter h2

theorem frameResidual_snoc {d j : ℕ} (v : Fin j → Point d) (u y : Point d) :
    frameResidual (Fin.snoc v u) y = frameResidual v y - inner ℝ y u • u := by
  unfold frameResidual
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [real_inner_comm y u]
  abel

theorem frameResidual_inner_complement {d j : ℕ} (v : Fin j → Point d) (y u : Point d)
    (hu : u ∈ (Submodule.span ℝ (Set.range v))ᗮ) :
    inner ℝ (frameResidual v y) u = inner ℝ y u := by
  have hzero (i : Fin j) : inner ℝ (v i) u = 0 :=
    ((Submodule.span ℝ (Set.range v)).mem_orthogonal u).mp hu (v i)
      (Submodule.subset_span (Set.mem_range_self i))
  unfold frameResidual
  rw [inner_sub_left, sum_inner]
  simp only [inner_smul_left, hzero, mul_zero, Finset.sum_const_zero, sub_zero]

theorem fixedPrefixCap_residual_norm_sq {d j : ℕ} (v : Fin j → Point d) (y u : Point d)
    (hu : u ∈ (Submodule.span ℝ (Set.range v))ᗮ) (hnorm : ‖u‖ = 1) :
    ‖frameResidual v y - inner ℝ y u • u‖ ^ 2 =
      ‖frameResidual v y‖ ^ 2 - (inner ℝ y u) ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, frameResidual_inner_complement v y u hu,
    norm_smul, Real.norm_eq_abs, hnorm]
  simp only [mul_one, sq_abs]
  ring

theorem fixedPrefixCap_angle_sq {d j : ℕ} (v : Fin j → Point d) (y u : Point d)
    (hu : u ∈ (Submodule.span ℝ (Set.range v))ᗮ) (hnorm : ‖u‖ = 1)
    (hcap : u ∈ fixedPrefixCap v y) :
    haarCapAngleSq * ‖frameResidual v y‖ ^ 2 ≤ (inner ℝ (frameResidual v y) u) ^ 2 := by
  obtain ⟨hhalf, hres⟩ := hcap
  have hsq : (1 / 4 : ℝ) ≤ (inner ℝ y u) ^ 2 := by
    have h := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_nonneg _)).mpr hhalf
    norm_num [sq_abs] at h
    exact h
  rw [fixedPrefixCap_residual_norm_sq v y u hu hnorm] at hres
  rw [frameResidual_inner_complement v y u hu, haarCapAngleSq_eq]
  nlinarith

theorem fixedPrefixCap_angle {d j : ℕ} (v : Fin j → Point d) (y u : Point d)
    (hu : u ∈ (Submodule.span ℝ (Set.range v))ᗮ) (hnorm : ‖u‖ = 1)
    (hcap : u ∈ fixedPrefixCap v y) :
    Real.sqrt haarCapAngleSq * ‖frameResidual v y‖ ≤ |inner ℝ (frameResidual v y) u| := by
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (abs_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt haarCapAngleSq_pos.le, sq_abs]
  exact fixedPrefixCap_angle_sq v y u hu hnorm hcap

theorem frameResidual_ne_zero_of_fixedPrefixCap {d j : ℕ} (v : Fin j → Point d) (y u : Point d)
    (hu : u ∈ (Submodule.span ℝ (Set.range v))ᗮ) (hcap : u ∈ fixedPrefixCap v y) :
    frameResidual v y ≠ 0 := by
  intro hz
  have hi := frameResidual_inner_complement v y u hu
  have hinner : inner ℝ y u = 0 := by simpa [hz] using hi.symm
  have hh := hcap.1
  norm_num [hinner] at hh

theorem complement_finrank_eq {d j : ℕ} (v : Fin j → Point d) (hv : Orthonormal ℝ v) :
    Module.finrank ℝ ((Submodule.span ℝ (Set.range v))ᗮ) = d - j := by
  let S := Submodule.span ℝ (Set.range v)
  have hS : Module.finrank ℝ S = j := by simpa [S] using finrank_span_eq_card hv.linearIndependent
  have hE : Module.finrank ℝ (Point d) = d := by simp [Point]
  have hsum := S.finrank_add_finrank_orthogonal
  rw [hS, hE] at hsum
  change Module.finrank ℝ Sᗮ = d - j
  omega

theorem stdNormal_hasSubgaussianMGF :
    HasSubgaussianMGF (fun x : ℝ => x) (1 : NNReal) (gaussianReal 0 1) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by rw [mgf_fun_id_gaussianReal]; simp

theorem stdNormal_abs_tail {ε : ℝ} (hε : 0 ≤ ε) :
    (gaussianReal 0 1).real {x : ℝ | ε ≤ |x|} ≤ 2 * Real.exp (-ε ^ 2 / 2) := by
  have hp := stdNormal_hasSubgaussianMGF.measure_ge_le hε
  have hn := stdNormal_hasSubgaussianMGF.neg.measure_ge_le hε
  have heq : {x : ℝ | ε ≤ |x|} = {x : ℝ | ε ≤ x} ∪ {x : ℝ | ε ≤ -x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    exact le_abs
  rw [heq]
  calc
    _ ≤ (gaussianReal 0 1).real {x : ℝ | ε ≤ x} + (gaussianReal 0 1).real {x : ℝ | ε ≤ -x} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / 2) + Real.exp (-ε ^ 2 / 2) := by
      simpa only [NNReal.coe_one, mul_one, Pi.neg_apply] using add_le_add hp hn
    _ = _ := by ring

theorem stdNormal_abs_tail_ennreal {ε : ℝ} (hε : 0 ≤ ε) :
    gaussianReal 0 1 {x : ℝ | ε ≤ |x|} ≤ ENNReal.ofReal (2 * Real.exp (-ε ^ 2 / 2)) := by
  calc
    _ = ENNReal.ofReal ((gaussianReal 0 1).real {x : ℝ | ε ≤ |x|}) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (stdNormal_abs_tail hε)

theorem integrable_stdNormal_exp_neg_sq {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun x : ℝ => Real.exp (-c * x ^ 2)) (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

/-- Exact Laplace transform of the square of a standard normal. -/
theorem stdNormal_exp_neg_sq_integral {c : ℝ} (hc : 0 ≤ c) :
    (∫ x : ℝ, Real.exp (-c * x ^ 2) ∂gaussianReal 0 1) = (Real.sqrt (1 + 2 * c))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hf : (fun x : ℝ => gaussianPDFReal 0 1 x • Real.exp (-c * x ^ 2)) =
      (fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 + c) * x ^ 2)) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul, mul_assoc]
    rw [← Real.exp_add]
    congr 2
    ring
  rw [hf, integral_const_mul, integral_gaussian]
  have hb : 0 < (1 / 2 : ℝ) + c := by linarith
  have hd : 0 < 1 + 2 * c := by linarith
  have hpi := Real.pi_pos
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi),
    Real.sq_sqrt (by positivity : 0 ≤ Real.pi / (1 / 2 + c)), inv_pow, Real.sq_sqrt hd.le]
  field_simp [hb.ne', hd.ne', hpi.ne']
  <;> ring

theorem exp_neg_mul_sum_sq_eq_prod (n : ℕ) (c : ℝ) (z : Fin n → ℝ) :
    Real.exp (-c * ∑ i, (z i) ^ 2) = ∏ i, Real.exp (-c * (z i) ^ 2) := by
  rw [Finset.mul_sum, Real.exp_sum]

theorem integrable_gaussian_exp_neg_sum_sq (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun z : Fin n → ℝ => Real.exp (-c * ∑ i, (z i) ^ 2))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  simp_rw [exp_neg_mul_sum_sq_eq_prod]
  exact Integrable.fintype_prod (fun _ => integrable_stdNormal_exp_neg_sq hc)

theorem gaussian_exp_neg_sum_sq_integral (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    (∫ z : Fin n → ℝ, Real.exp (-c * ∑ i, (z i) ^ 2)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) = (Real.sqrt (1 + 2 * c))⁻¹ ^ n := by
  simp_rw [exp_neg_mul_sum_sq_eq_prod]
  have h := integral_fin_nat_prod_eq_prod (μ := fun _ : Fin n => gaussianReal 0 1)
    (fun (_ : Fin n) (x : ℝ) => Real.exp (-c * x ^ 2))
  simpa only [stdNormal_exp_neg_sq_integral hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- An algebraic second-order logarithm bound suffices in the chosen large dimensions. -/
theorem log_one_sub_le_neg_sub_quarter {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    Real.log (1 - τ) ≤ -τ - τ ^ 2 / 4 := by
  let z := 1 - τ / 2 - τ ^ 2 / 8
  have ht2 : τ ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ hτ zero_le_one).mpr hτ1.le
    simpa using h
  have hz : 0 ≤ z := by dsimp [z]; nlinarith
  have hzsq : 1 - τ ≤ z ^ 2 := by
    dsimp [z]
    nlinarith [pow_nonneg hτ 3, pow_nonneg hτ 4]
  have hroot : Real.sqrt (1 - τ) ≤ z := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hz).mp
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - τ)]
    exact hzsq
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : 0 < 1 - τ))
  have hs := Real.log_sqrt (by linarith : 0 ≤ 1 - τ)
  dsimp [z] at hroot
  nlinarith

theorem sqrt_one_sub_pow_le_exp {n : ℕ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (hn : (4 : ℝ) ≤ n * τ) :
    (Real.sqrt (1 - τ)) ^ n ≤ Real.exp (-((n + 1 : ℕ) : ℝ) * τ / 2) := by
  have hp : 0 < 1 - τ := by linarith
  have hroot : 0 < Real.sqrt (1 - τ) := Real.sqrt_pos.mpr hp
  have hlog := log_one_sub_le_neg_sub_quarter hτ.le hτ1
  have hs := Real.log_sqrt hp.le
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hm := mul_le_mul_of_nonneg_left hlog hn0
  have hquad := mul_le_mul_of_nonneg_right hn hτ.le
  have he : (n : ℝ) * Real.log (Real.sqrt (1 - τ)) ≤ -((n + 1 : ℕ) : ℝ) * τ / 2 := by
    push_cast
    nlinarith
  calc
    _ = Real.exp ((n : ℝ) * Real.log (Real.sqrt (1 - τ))) := by
      rw [Real.exp_nat_mul, Real.exp_log hroot]
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem cap_large_dimension_condition {m : ℕ} (hm : 16022 ≤ m) :
    (4 : ℝ) ≤ (m - 1 : ℕ) * haarCapAngleSq := by
  rw [haarCapAngleSq_eq]
  have hn : (16021 : ℝ) ≤ (m - 1 : ℕ) := by exact_mod_cast (show 16021 ≤ m - 1 by omega)
  nlinarith

/-- Finite union accounting, with no independence assumption on the events. -/
theorem preselected_union_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n N : ℕ} (hn : n ≤ N + 2) (A : Fin n → Set Ω) {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ i, μ.real (A i) ≤ b) :
    μ.real (⋃ i, A i) ≤ (N + 2 : ℕ) * b := by
  calc
    _ ≤ ∑ i : Fin n, μ.real (A i) := measureReal_iUnion_fintype_le A
    _ ≤ ∑ _i : Fin n, b := Finset.sum_le_sum (fun i _ => hA i)
    _ = (n : ℝ) * b := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hb

/-- The reference product law is explicit; this does not assert independence
for the actual adaptive-query law. -/
theorem reference_product_bound_of_sections {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure α) (ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set (α × Ω)) (hA : MeasurableSet A) {b : ℝ} (hb : 0 ≤ b)
    (hsections : ∀ ω, μ.real ((fun u => (u, ω)) ⁻¹' A) ≤ b) :
    (μ.prod ν).real A ≤ b := by
  have hENN : (μ.prod ν) A ≤ ENNReal.ofReal b := by
    rw [Measure.prod_apply_symm hA]
    calc
      _ ≤ ∫⁻ _ω, ENNReal.ofReal b ∂ν := by
        apply lintegral_mono
        intro ω
        calc
          _ = ENNReal.ofReal (μ.real ((fun u => (u, ω)) ⁻¹' A)) :=
            (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (hsections ω)
      _ = _ := by simp
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hENN
  simpa only [measureReal_def, ENNReal.toReal_ofReal hb] using hreal


/-- Conditional normal tail integrated against the independent remaining Gaussian coordinates. -/
theorem gaussian_product_quadratic_cap_bound (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
      {p : ℝ × (Fin n → ℝ) | τ * (∑ i, (p.2 i) ^ 2) ≤ (1 - τ) * p.1 ^ 2} ≤
      ENNReal.ofReal (2 * (Real.sqrt (1 - τ)) ^ n) := by
  let ν := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let c := τ / (2 * (1 - τ))
  let A : Set (ℝ × (Fin n → ℝ)) :=
    {p | τ * (∑ i, (p.2 i) ^ 2) ≤ (1 - τ) * p.1 ^ 2}
  have hd : 0 < 1 - τ := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) (by fun_prop)
  have hsection (z : Fin n → ℝ) :
      gaussianReal 0 1 ((fun x => (x, z)) ⁻¹' A) ≤
        ENNReal.ofReal (2 * Real.exp (-c * ∑ i, (z i) ^ 2)) := by
    let S := ∑ i, (z i) ^ 2
    have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (z i))
    have hsqrt : 0 ≤ τ / (1 - τ) * S := mul_nonneg (div_nonneg hτ hd.le) hS
    have hsub : ((fun x => (x, z)) ⁻¹' A) ⊆
        {x : ℝ | Real.sqrt (τ / (1 - τ) * S) ≤ |x|} := by
      intro x hx
      have hh : τ * S ≤ (1 - τ) * x ^ 2 := hx
      have hsq : τ / (1 - τ) * S ≤ x ^ 2 := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hd).mpr
        nlinarith
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (abs_nonneg x)).mp
      rw [Real.sq_sqrt hsqrt, sq_abs]
      exact hsq
    have ht := stdNormal_abs_tail_ennreal (Real.sqrt_nonneg (τ / (1 - τ) * S))
    rw [Real.sq_sqrt hsqrt] at ht
    have hexp : -(τ / (1 - τ) * S) / 2 = -c * S := by
      dsimp [c]
      field_simp [hd.ne']
      <;> ring
    rw [hexp] at ht
    exact (measure_mono hsub).trans ht
  have hroot : (Real.sqrt (1 + 2 * c))⁻¹ = Real.sqrt (1 - τ) := by
    have ha : 0 < 1 + 2 * c := by positivity
    have heq : (1 + 2 * c) * (1 - τ) = 1 := by
      dsimp [c]
      field_simp [hd.ne']
      <;> ring
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [inv_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hd.le]
    have hh := congrArg (fun z : ℝ => (1 + 2 * c)⁻¹ * z) heq
    simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul, mul_one] using hh.symm
  have hInt :
      (∫⁻ z : Fin n → ℝ, ENNReal.ofReal (2 * Real.exp (-c * ∑ i, (z i) ^ 2)) ∂ν) =
        ENNReal.ofReal (2 * (Real.sqrt (1 - τ)) ^ n) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((integrable_gaussian_exp_neg_sum_sq n hc).const_mul 2)
      (Filter.Eventually.of_forall (fun z => by positivity)), integral_const_mul,
      gaussian_exp_neg_sum_sq_integral n hc, hroot]
  change ((gaussianReal 0 1).prod ν) A ≤ _
  rw [Measure.prod_apply_symm hA]
  exact (lintegral_mono hsection).trans_eq hInt

theorem gaussian_pi_quadratic_cap_bound (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
      {z : Fin (n + 1) → ℝ | τ * (∑ i : Fin n, (z i.succ) ^ 2) ≤ (1 - τ) * (z 0) ^ 2} ≤
      ENNReal.ofReal (2 * (Real.sqrt (1 - τ)) ^ n) := by
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let A : Set (ℝ × (Fin n → ℝ)) :=
    {p | τ * (∑ i, (p.2 i) ^ 2) ≤ (1 - τ) * p.1 ^ 2}
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) (by fun_prop)
  have hm : (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)).map E =
      (gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0).map_eq
  have hs : {z : Fin (n + 1) → ℝ | τ * (∑ i : Fin n, (z i.succ) ^ 2) ≤ (1 - τ) * (z 0) ^ 2} =
      E ⁻¹' A := by
    ext z
    simp [E, A, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.zero_succAbove, Fin.tail]
  rw [hs, ← Measure.map_apply E.measurable hA, hm]
  exact gaussian_product_quadratic_cap_bound n hτ hτ1

/-- The normalized first Gaussian coordinate has the elementary sphere-tail bound. -/
theorem gaussianDirection_first_coordinate_tail (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    (stdGaussian (Point (n + 1)))
      {z | Real.sqrt τ ≤ |(gaussianDirection z) 0|} ≤
      ENNReal.ofReal (2 * (Real.sqrt (1 - τ)) ^ n) := by
  have hset : MeasurableSet {z : Point (n + 1) | Real.sqrt τ ≤ |(gaussianDirection z) 0|} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [← map_pi_eq_stdGaussian (ι := Fin (n + 1)), Measure.map_apply (by fun_prop) hset]
  apply (measure_mono ?_).trans (gaussian_pi_quadratic_cap_bound n hτ.le hτ1)
  intro z hz
  let x : Point (n + 1) := WithLp.toLp 2 z
  have hx : x ≠ 0 := by
    intro hx0
    have h : Real.sqrt τ ≤ |(gaussianDirection x) 0| := hz
    simp [hx0, gaussianDirection] at h
    exact not_le_of_gt (Real.sqrt_pos.mpr hτ) h
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hangle : Real.sqrt τ * ‖x‖ ≤ |z 0| := by
    have h : Real.sqrt τ ≤ ‖x‖⁻¹ * |z 0| := by
      simpa [gaussianDirection, x, PiLp.smul_apply, abs_mul, abs_inv, abs_norm] using hz
    have hm := mul_le_mul_of_nonneg_right h hn.le
    simpa [mul_assoc, mul_left_comm, inv_mul_cancel₀ hn.ne'] using hm
  have hsq := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hn.le) (abs_nonneg (z 0))).mpr hangle
  rw [mul_pow, Real.sq_sqrt hτ.le, sq_abs, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at hsq
  change τ * (∑ i : Fin n, (z i.succ) ^ 2) ≤ (1 - τ) * (z 0) ^ 2
  change τ * ((z 0) ^ 2 + ∑ i : Fin n, (z i.succ) ^ 2) ≤ (z 0) ^ 2 at hsq
  nlinarith


theorem gaussianDirection_isometry {m : ℕ} (e : Point m ≃ₗᵢ[ℝ] Point m) (z : Point m) :
    gaussianDirection (e z) = e (gaussianDirection z) := by
  simp [gaussianDirection]

theorem gaussianDirection_law_isometry {m : ℕ} (e : Point m ≃ₗᵢ[ℝ] Point m) :
    ((stdGaussian (Point m)).map gaussianDirection).map e =
      (stdGaussian (Point m)).map gaussianDirection := by
  rw [Measure.map_map e.continuous.measurable (measurable_gaussianDirection m)]
  have hf : e ∘ gaussianDirection = gaussianDirection ∘ e :=
    funext fun z => (gaussianDirection_isometry e z).symm
  rw [hf, ← Measure.map_map (measurable_gaussianDirection m) e.continuous.measurable, stdGaussian_map e]

theorem gaussianDirection_unit_tail_succ (n : ℕ) (p : Point (n + 1)) (hp : ‖p‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    (stdGaussian (Point (n + 1))) {z | Real.sqrt τ ≤ |inner ℝ p (gaussianDirection z)|} ≤
      ENNReal.ofReal (2 * (Real.sqrt (1 - τ)) ^ n) := by
  let e₀ : Point (n + 1) := EuclideanSpace.single 0 1
  let L : Point (n + 1) ≃ₗᵢ[ℝ] Point (n + 1) := (ℝ ∙ (e₀ - p))ᗮ.reflection
  let μ := (stdGaussian (Point (n + 1))).map gaussianDirection
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  have hLp : L e₀ = p := Submodule.reflection_sub (he₀.trans hp.symm)
  have hA (w : Point (n + 1)) : MeasurableSet {u | Real.sqrt τ ≤ |inner ℝ w u|} :=
    measurableSet_le measurable_const (by fun_prop)
  have hpre : L ⁻¹' {u | Real.sqrt τ ≤ |inner ℝ p u|} =
      {u | Real.sqrt τ ≤ |inner ℝ e₀ u|} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hLp, L.inner_map_map]
  have hfirst : μ {u | Real.sqrt τ ≤ |inner ℝ e₀ u|} =
      (stdGaussian (Point (n + 1))) {z | Real.sqrt τ ≤ |(gaussianDirection z) 0|} := by
    rw [Measure.map_apply (measurable_gaussianDirection _) (hA e₀)]
    congr 1
    ext z
    simp [e₀, EuclideanSpace.inner_single_left]
  calc
    _ = μ {u | Real.sqrt τ ≤ |inner ℝ p u|} := by
      rw [Measure.map_apply (measurable_gaussianDirection _) (hA p)]
      rfl
    _ = (μ.map L) {u | Real.sqrt τ ≤ |inner ℝ p u|} := by
      rw [gaussianDirection_law_isometry L]
    _ = μ {u | Real.sqrt τ ≤ |inner ℝ e₀ u|} := by
      rw [Measure.map_apply L.continuous.measurable (hA p), hpre]
    _ = _ := hfirst
    _ ≤ _ := gaussianDirection_first_coordinate_tail n hτ hτ1

theorem gaussianDirection_vector_tail {m : ℕ} (hm : 0 < m) (p : Point m) (hp : p ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    (stdGaussian (Point m)) {z | Real.sqrt τ * ‖p‖ ≤ |inner ℝ p (gaussianDirection z)|} ≤
      ENNReal.ofReal (2 * (Real.sqrt (1 - τ)) ^ (m - 1)) := by
  rcases m with _ | n
  · omega
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  let e : Point (n + 1) := ‖p‖⁻¹ • p
  have he : ‖e‖ = 1 := norm_smul_inv_norm hp
  have hs : {z | Real.sqrt τ * ‖p‖ ≤ |inner ℝ p (gaussianDirection z)|} =
      {z | Real.sqrt τ ≤ |inner ℝ e (gaussianDirection z)|} := by
    ext z
    simp only [Set.mem_setOf_eq, e, real_inner_smul_left, abs_mul, abs_inv, abs_norm]
    rw [mul_comm (‖p‖⁻¹) (|inner ℝ p (gaussianDirection z)|), ← div_eq_mul_inv]
    exact (le_div_iff₀ hn).symm
  rw [hs]
  simpa using gaussianDirection_unit_tail_succ n e he hτ hτ1

/-- Coordinates for the exact fixed-prefix transition; no variable measurable basis is chosen. -/
theorem frameNextKernel_gaussian_coordinates {d j n : ℕ} (v : Fin j → Point d)
    (hv : Orthonormal ℝ v)
    (e : Point n ≃ₗᵢ[ℝ] (Submodule.span ℝ (Set.range v))ᗮ) :
    frameNextKernel d j v = (stdGaussian (Point n)).map
      (fun z => ((e (gaussianDirection z) : (Submodule.span ℝ (Set.range v))ᗮ) : Point d)) := by
  let W := (Submodule.span ℝ (Set.range v))ᗮ
  let D : W → Point d := fun w => ((‖w‖⁻¹ • w : W) : Point d)
  have hf : frameNextDirection v = D ∘ W.orthogonalProjectionOnto := by
    funext z
    unfold frameNextDirection gaussianDirection
    rw [frameResidual_eq_orthogonalProjection v hv z]
    rfl
  have hD : Measurable D := by dsimp [D]; fun_prop
  rw [frameNextKernel_apply, hf, ← Measure.map_map hD (by fun_prop),
    stdGaussian_orthogonalProjection_law d W, ← stdGaussian_map e,
    Measure.map_map hD e.continuous.measurable]
  congr 1
  funext z
  simp [D, gaussianDirection, Function.comp_def]
  rw [show ‖((e z : W) : Point d)‖ = ‖z‖ from e.norm_map z]

theorem complement_coordinates_inner {d j n : ℕ} (v : Fin j → Point d)
    (e : Point n ≃ₗᵢ[ℝ] (Submodule.span ℝ (Set.range v))ᗮ) (y : Point d) (z : Point n) :
    inner ℝ y ((e z : (Submodule.span ℝ (Set.range v))ᗮ) : Point d) =
      inner ℝ (e.symm (((Submodule.span ℝ (Set.range v))ᗮ).orthogonalProjectionOnto y)) z := by
  rw [← e.inner_map_map, e.apply_symm_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

theorem frameNextKernel_linear_tail {d j : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) (y : Point d) (hy : frameResidual v y ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    frameNextKernel d j v {u | Real.sqrt τ * ‖frameResidual v y‖ ≤ |inner ℝ y u|} ≤
      ENNReal.ofReal (2 * (Real.sqrt (1 - τ)) ^ (d - j - 1)) := by
  let W := (Submodule.span ℝ (Set.range v))ᗮ
  let n := Module.finrank ℝ W
  let e : Point n ≃ₗᵢ[ℝ] W := (stdOrthonormalBasis ℝ W).repr.symm
  let p := e.symm (W.orthogonalProjectionOnto y)
  have hn : n = d - j := complement_finrank_eq v hv
  have hnpos : 0 < n := by omega
  have hpNorm : ‖p‖ = ‖frameResidual v y‖ := by
    rw [frameResidual_eq_orthogonalProjection v hv y]
    exact e.symm.norm_map _
  have hp : p ≠ 0 := by
    intro hp0
    have hzero : ‖frameResidual v y‖ = 0 := by rw [← hpNorm, hp0, norm_zero]
    exact hy (norm_eq_zero.mp hzero)
  have hA : MeasurableSet {u : Point d | Real.sqrt τ * ‖frameResidual v y‖ ≤ |inner ℝ y u|} :=
    measurableSet_le measurable_const (by fun_prop)
  have hf : Measurable (fun z : Point n => ((e (gaussianDirection z) : W) : Point d)) := by
    unfold gaussianDirection
    fun_prop
  rw [frameNextKernel_gaussian_coordinates v hv e, Measure.map_apply hf hA]
  have hs : (fun z : Point n => ((e (gaussianDirection z) : W) : Point d)) ⁻¹'
      {u | Real.sqrt τ * ‖frameResidual v y‖ ≤ |inner ℝ y u|} =
      {z | Real.sqrt τ * ‖p‖ ≤ |inner ℝ p (gaussianDirection z)|} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hpNorm]
    have hi : inner ℝ y ((e (gaussianDirection z) : W) : Point d) = inner ℝ p (gaussianDirection z) :=
      complement_coordinates_inner v e y (gaussianDirection z)
    rw [hi]
  rw [hs]
  have h := gaussianDirection_vector_tail hnpos p hp hτ hτ1
  simpa only [hn] using h

theorem frameNextKernel_linear_tail_sharp {d j : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) (y : Point d) (hy : frameResidual v y ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (hm : (4 : ℝ) ≤ (d - j - 1 : ℕ) * τ) :
    frameNextKernel d j v {u | Real.sqrt τ * ‖frameResidual v y‖ ≤ |inner ℝ y u|} ≤
      ENNReal.ofReal (2 * Real.exp (-((d - j : ℕ) : ℝ) * τ / 2)) := by
  have h := sqrt_one_sub_pow_le_exp hτ hτ1 hm
  have hdim : (d - j - 1) + 1 = d - j := by omega
  rw [hdim] at h
  exact (frameNextKernel_linear_tail hj v hv y hy hτ hτ1).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h (by norm_num)))

theorem frameNextKernel_positive_linear_tail_zero {d j : ℕ} (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) (y : Point d) (hy : frameResidual v y = 0) {ε : ℝ} (hε : 0 < ε) :
    frameNextKernel d j v {u | ε ≤ |inner ℝ y u|} = 0 := by
  have hA : MeasurableSet {u : Point d | ε ≤ |inner ℝ y u|} := measurableSet_le measurable_const (by fun_prop)
  rw [frameNextKernel_apply, Measure.map_apply (measurable_frameNextDirection_fixed v) hA]
  have hs : frameNextDirection v ⁻¹' {u | ε ≤ |inner ℝ y u|} = ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hz
    have hi := frameResidual_inner_complement v y (frameNextDirection v z)
      (frameNextDirection_mem_complement v hv z)
    have hzero : inner ℝ y (frameNextDirection v z) = 0 := by simpa [hy] using hi.symm
    rw [hzero, abs_zero] at hz
    exact not_le_of_gt hε hz
  rw [hs, measure_empty]

/-- The frozen cap exponent is recovered for complement dimension at least 16022. -/
theorem frameNextKernel_fixed_cap_bound {d j : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) (hm : 16022 ≤ d - j) (y : Point d) :
    frameNextKernel d j v (fixedPrefixCap v y) ≤
      ENNReal.ofReal (2 * Real.exp (-((d - j : ℕ) : ℝ) * haarCapAngleSq / 2)) := by
  by_cases hy : frameResidual v y = 0
  · have hsub : fixedPrefixCap v y ⊆ {u : Point d | (1 / 2 : ℝ) ≤ |inner ℝ y u|} := fun _ hu => hu.1
    calc
      _ ≤ frameNextKernel d j v {u : Point d | (1 / 2 : ℝ) ≤ |inner ℝ y u|} := measure_mono hsub
      _ = 0 := frameNextKernel_positive_linear_tail_zero v hv y hy (by norm_num)
      _ ≤ _ := by positivity
  · have htail := frameNextKernel_linear_tail_sharp hj v hv y hy haarCapAngleSq_pos haarCapAngleSq_lt_one
      (cap_large_dimension_condition hm)
    have hA := measurableSet_fixedPrefixCap v y
    have hB : MeasurableSet {u : Point d | Real.sqrt haarCapAngleSq * ‖frameResidual v y‖ ≤ |inner ℝ y u|} :=
      measurableSet_le measurable_const (by fun_prop)
    rw [frameNextKernel_apply, Measure.map_apply (measurable_frameNextDirection_fixed v) hA]
    rw [frameNextKernel_apply, Measure.map_apply (measurable_frameNextDirection_fixed v) hB] at htail
    apply (measure_mono_ae ?_).trans htail
    filter_upwards [frameResidual_ne_zero_ae hj v hv] with z hz
    intro hcap
    have hcomp := frameNextDirection_mem_complement v hv z
    have hnorm := frameNextDirection_norm_one_of_ne_zero v z hz
    have hangle := fixedPrefixCap_angle v y (frameNextDirection v z) hcomp hnorm hcap
    rwa [frameResidual_inner_complement v y (frameNextDirection v z) hcomp] at hangle


theorem fixedPrefixCap_snoc_iff {d j : ℕ} (v : Fin j → Point d) (y u : Point d) :
    u ∈ fixedPrefixCap v y ↔
      (1 / 2 : ℝ) ≤ |inner ℝ y u| ∧ ‖frameResidual (Fin.snoc v u) y‖ ^ 2 ≤ 1000 + 1 / 16 + 1 := by
  rw [frameResidual_snoc]
  rfl

theorem frameNextKernel_fixed_cap_bound_real {d j : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) (hm : 16022 ≤ d - j) (y : Point d) :
    (frameNextKernel d j v).real (fixedPrefixCap v y) ≤
      2 * Real.exp (-((d - j : ℕ) : ℝ) * haarCapAngleSq / 2) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (frameNextKernel_fixed_cap_bound hj v hv hm y)
  have hb : 0 ≤ 2 * Real.exp (-((d - j : ℕ) : ℝ) * haarCapAngleSq / 2) := by positivity
  simpa only [measureReal_def, ENNReal.toReal_ofReal hb] using h

theorem fixedPrefixCap_preselected_union {d j n N : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) (hm : 16022 ≤ d - j) (y : Fin n → Point d) (hn : n ≤ N + 2) :
    (frameNextKernel d j v).real (⋃ i, fixedPrefixCap v (y i)) ≤
      2 * (N + 2 : ℕ) * Real.exp (-((d - j : ℕ) : ℝ) * haarCapAngleSq / 2) := by
  have h := preselected_union_bound (frameNextKernel d j v) hn (fun i => fixedPrefixCap v (y i))
    (by positivity) (fun i => frameNextKernel_fixed_cap_bound_real hj v hv hm (y i))
  nlinarith

/-- Random query lists appear only under this explicit reference product measure. -/
theorem fixedPrefixCap_reference_product_union {Ω : Type*} [MeasurableSpace Ω]
    {d j n N : ℕ} (hj : j < d) (v : Fin j → Point d) (hv : Orthonormal ℝ v)
    (hm : 16022 ≤ d - j) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (q : Ω → Fin n → Point d) (hq : Measurable q) (hn : n ≤ N + 2) :
    ((frameNextKernel d j v).prod ν).real
      {p : Point d × Ω | ∃ i, p.1 ∈ fixedPrefixCap v (q p.2 i)} ≤
      2 * (N + 2 : ℕ) * Real.exp (-((d - j : ℕ) : ℝ) * haarCapAngleSq / 2) := by
  have hA : MeasurableSet {p : Point d × Ω | ∃ i, p.1 ∈ fixedPrefixCap v (q p.2 i)} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    have hqi : Measurable (fun p : Point d × Ω => q p.2 i) :=
      ((measurable_pi_iff.mp hq) i).comp measurable_snd
    have h1 : MeasurableSet {p : Point d × Ω | (1 / 2 : ℝ) ≤ |inner ℝ (q p.2 i) p.1|} :=
      measurableSet_le measurable_const (by fun_prop)
    have h2 : MeasurableSet {p : Point d × Ω |
        ‖frameResidual v (q p.2 i) - inner ℝ (q p.2 i) p.1 • p.1‖ ^ 2 ≤ 1000 + 1 / 16 + 1} := by
      unfold frameResidual
      exact measurableSet_le (by fun_prop) measurable_const
    exact h1.inter h2
  apply reference_product_bound_of_sections (frameNextKernel d j v) ν _ hA (by positivity)
  intro ω
  simpa [Set.preimage_iUnion, Set.setOf_exists] using
    fixedPrefixCap_preselected_union hj v hv hm (q ω) hn

/-- The accident threshold bound under a fixed valid prefix. -/
theorem frameNextKernel_small_coordinate_bound {d j : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) {R : ℝ} (hR : 1 ≤ R)
    (hm : 4096 * R ^ 2 ≤ ((d - j - 1 : ℕ) : ℝ)) (y : Point d) (hy : ‖y‖ ≤ R) :
    frameNextKernel d j v {u | (1 / 32 : ℝ) ≤ |inner ℝ y u|} ≤
      ENNReal.ofReal (2 * Real.exp (-((d - j : ℕ) : ℝ) / (2048 * R ^ 2))) := by
  have hRpos : 0 < R := by linarith
  let τ := 1 / (1024 * R ^ 2)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ < 1 := by
    dsimp [τ]
    apply (div_lt_iff₀ (by positivity : 0 < 1024 * R ^ 2)).mpr
    nlinarith [sq_nonneg (R - 1)]
  have hn : (4 : ℝ) ≤ (d - j - 1 : ℕ) * τ := by
    dsimp [τ]
    rw [mul_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 1024 * R ^ 2)).mpr
    nlinarith
  have hproj : ‖frameResidual v y‖ ≤ R := by
    rw [frameResidual_eq_orthogonalProjection v hv y]
    exact (((Submodule.span ℝ (Set.range v))ᗮ).norm_orthogonalProjectionOnto_apply_le y).trans hy
  have hscale : Real.sqrt τ * R = (1 / 32 : ℝ) := by
    apply (sq_eq_sq₀ (by positivity) (by norm_num)).mp
    rw [mul_pow, Real.sq_sqrt hτ.le]
    dsimp [τ]
    field_simp [hRpos.ne']
    <;> norm_num
  by_cases hp : frameResidual v y = 0
  · rw [frameNextKernel_positive_linear_tail_zero v hv y hp (by norm_num)]
    positivity
  · have ht := frameNextKernel_linear_tail_sharp hj v hv y hp hτ hτ1 hn
    have hthresh : Real.sqrt τ * ‖frameResidual v y‖ ≤ (1 / 32 : ℝ) := by
      rw [← hscale]
      exact mul_le_mul_of_nonneg_left hproj (Real.sqrt_nonneg τ)
    have hsub : {u : Point d | (1 / 32 : ℝ) ≤ |inner ℝ y u|} ⊆
        {u | Real.sqrt τ * ‖frameResidual v y‖ ≤ |inner ℝ y u|} := fun u hu => hthresh.trans hu
    have hexp : -((d - j : ℕ) : ℝ) * τ / 2 = -((d - j : ℕ) : ℝ) / (2048 * R ^ 2) := by
      dsimp [τ]
      field_simp [hRpos.ne']
      <;> ring
    rw [hexp] at ht
    exact (measure_mono hsub).trans ht

theorem hardRadius_sq_exact (T : ℕ) : (hardRadius T) ^ 2 = 6250000 * (T : ℝ) := by
  unfold hardRadius
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ T)]
  norm_num

theorem hardRadius_accident_denominator (T : ℕ) :
    2048 * (hardRadius T) ^ 2 = 12800000000 * (T : ℝ) := by rw [hardRadius_sq_exact]; ring

theorem softProjection_preselected_small_coordinate_union {d j T n N : ℕ}
    (hj : j < d) (v : Fin j → Point d) (hv : Orthonormal ℝ v) (hT : 0 < T)
    (hm : 25600000000 * (T : ℝ) ≤ ((d - j - 1 : ℕ) : ℝ))
    (x : Fin n → Point d) (hn : n ≤ N + 2) :
    (frameNextKernel d j v).real (⋃ i,
      {u : Point d | (1 / 32 : ℝ) ≤ |inner ℝ (softProjection (hardRadius T) (x i)) u|}) ≤
      2 * (N + 2 : ℕ) * Real.exp (-((d - j : ℕ) : ℝ) / (12800000000 * (T : ℝ))) := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast Nat.succ_le_of_lt hT
  have hs : 1 ≤ Real.sqrt T := by
    have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ T)
    nlinarith [Real.sqrt_nonneg (T : ℝ)]
  have hR : 1 ≤ hardRadius T := by unfold hardRadius; nlinarith
  have hRpos : 0 < hardRadius T := by linarith
  have hdim : 4096 * (hardRadius T) ^ 2 ≤ ((d - j - 1 : ℕ) : ℝ) := by
    rw [hardRadius_sq_exact]
    nlinarith
  have hb (i : Fin n) : (frameNextKernel d j v).real
      {u : Point d | (1 / 32 : ℝ) ≤ |inner ℝ (softProjection (hardRadius T) (x i)) u|} ≤
      2 * Real.exp (-((d - j : ℕ) : ℝ) / (12800000000 * (T : ℝ))) := by
    have h := frameNextKernel_small_coordinate_bound hj v hv hR hdim
      (softProjection (hardRadius T) (x i)) (norm_softProjection_lt_radius hRpos (x i)).le
    rw [hardRadius_accident_denominator] at h
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    have hb0 : 0 ≤ 2 * Real.exp (-((d - j : ℕ) : ℝ) / (12800000000 * (T : ℝ))) := by positivity
    simpa only [measureReal_def, ENNReal.toReal_ofReal hb0] using hreal
  have h := preselected_union_bound (frameNextKernel d j v) hn
    (fun i => {u : Point d | (1 / 32 : ℝ) ≤ |inner ℝ (softProjection (hardRadius T) (x i)) u|})
    (by positivity) hb
  nlinarith

end

end HeavyTailedNoise
