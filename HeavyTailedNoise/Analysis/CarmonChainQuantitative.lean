import HeavyTailedNoise.Analysis.CarmonChainGap
import HeavyTailedNoise.Analysis.CarmonScalarSecondBound

/-!
The exact finite Carmon chain has Euclidean gradient norm at most `23 √T`
and Euclidean Hessian operator norm at most `152`. Quantitative statements
are on `Point d` with an orthonormal frame: the raw type `Fin T → ℝ` carries
its supremum norm and is not used as the quantitative domain.
-/

namespace HeavyTailedNoise

open scoped BigOperators

noncomputable section

def carmonChainLink (a b : ℝ) : ℝ :=
  carmonPsi (-a) * carmonPhi (-b) - carmonPsi a * carmonPhi b

theorem carmonChain_eq_sum_links {T : ℕ} (z : Fin T → ℝ) :
    carmonChain z = ∑ k, carmonChainLink (chainPredecessor z k) (z k) := by
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : k.val = 0
  · simp [carmonChainLink, chainPredecessor, h,
      carmonPsi_zero_of_le (by norm_num : (-1 : ℝ) ≤ 1 / 2)]
  · simp [carmonChainLink, h]

def chainLinkPrev (a b : ℝ) : ℝ :=
  -deriv carmonPsi (-a) * carmonPhi (-b) - deriv carmonPsi a * carmonPhi b

def chainLinkCurrent (a b : ℝ) : ℝ :=
  -carmonPsi (-a) * deriv carmonPhi (-b) - carmonPsi a * deriv carmonPhi b

def chainLinkPrevPrev (a b : ℝ) : ℝ :=
  deriv (deriv carmonPsi) (-a) * carmonPhi (-b) -
    deriv (deriv carmonPsi) a * carmonPhi b

def chainLinkPrevCurrent (a b : ℝ) : ℝ :=
  deriv carmonPsi (-a) * deriv carmonPhi (-b) - deriv carmonPsi a * deriv carmonPhi b

def chainLinkCurrentCurrent (a b : ℝ) : ℝ :=
  carmonPsi (-a) * deriv (deriv carmonPhi) (-b) -
    carmonPsi a * deriv (deriv carmonPhi) b

private theorem supported_products_abs_sum_le {f g : ℝ → ℝ} {A B : ℝ}
    (hf0 : ∀ t, t ≤ (1 / 2 : ℝ) → f t = 0)
    (hf : ∀ t, |f t| ≤ A) (hg : ∀ t, |g t| ≤ B) (hA : 0 ≤ A)
    (a b : ℝ) : |f (-a) * g (-b)| + |f a * g b| ≤ A * B := by
  by_cases ha : a ≤ (1 / 2 : ℝ)
  · rw [hf0 a ha, zero_mul, abs_zero, add_zero, abs_mul]
    exact mul_le_mul (hf _) (hg _) (abs_nonneg _) hA
  · have hn : -a ≤ (1 / 2 : ℝ) := by linarith
    rw [hf0 (-a) hn, zero_mul, abs_zero, zero_add, abs_mul]
    exact mul_le_mul (hf _) (hg _) (abs_nonneg _) hA

private theorem abs_carmonPsi_le_2719 (t : ℝ) : |carmonPsi t| ≤ (2719 / 1000 : ℝ) := by
  rw [abs_of_nonneg (carmonPsi_nonneg t)]
  exact (carmonPsi_lt_exp_one t).le.trans (Real.exp_one_lt_d9.le.trans (by norm_num))

private theorem abs_carmonPhi_le_414 (t : ℝ) : |carmonPhi t| ≤ (207 / 50 : ℝ) := by
  simpa only [abs_of_pos (carmonPhi_pos t)] using (carmonPhi_lt_414 t).le

private theorem abs_deriv_carmonPsi_le_446 (t : ℝ) : |deriv carmonPsi t| ≤ (223 / 50 : ℝ) := by
  simpa only [abs_of_nonneg (deriv_carmonPsi_nonneg t)] using (deriv_carmonPsi_lt_446 t).le

theorem abs_chainLinkPrev_le (a b : ℝ) : |chainLinkPrev a b| ≤ (46161 / 2500 : ℝ) := by
  have h := supported_products_abs_sum_le (fun _ ht => deriv_carmonPsi_zero_of_le ht)
    abs_deriv_carmonPsi_le_446 abs_carmonPhi_le_414 (by norm_num) a b
  have htri := norm_sub_le (-deriv carmonPsi (-a) * carmonPhi (-b))
    (deriv carmonPsi a * carmonPhi b)
  simp only [Real.norm_eq_abs, neg_mul, abs_neg] at htri
  simp only [chainLinkPrev, neg_mul]
  linarith

theorem abs_chainLinkCurrent_le (a b : ℝ) : |chainLinkCurrent a b| ≤ (89727 / 20000 : ℝ) := by
  have h := supported_products_abs_sum_le (fun _ ht => carmonPsi_zero_of_le ht)
    abs_carmonPsi_le_2719 abs_deriv_carmonPhi_le (by norm_num) a b
  have htri := norm_sub_le (-carmonPsi (-a) * deriv carmonPhi (-b))
    (carmonPsi a * deriv carmonPhi b)
  simp only [Real.norm_eq_abs, neg_mul, abs_neg] at htri
  simp only [chainLinkCurrent, neg_mul]
  linarith

theorem abs_chainLinkPrevPrev_le (a b : ℝ) : |chainLinkPrevPrev a b| ≤ (2691 / 20 : ℝ) := by
  have h := supported_products_abs_sum_le (fun _ ht => second_deriv_carmonPsi_zero_of_le ht)
    (fun t => (abs_second_deriv_carmonPsi_lt_32_5 t).le)
    abs_carmonPhi_le_414 (by norm_num) a b
  have htri := norm_sub_le (deriv (deriv carmonPsi) (-a) * carmonPhi (-b))
    (deriv (deriv carmonPsi) a * carmonPhi b)
  simp only [Real.norm_eq_abs] at htri
  unfold chainLinkPrevPrev
  linarith

theorem abs_chainLinkPrevCurrent_le (a b : ℝ) : |chainLinkPrevCurrent a b| ≤ (7359 / 1000 : ℝ) := by
  have h := supported_products_abs_sum_le (fun _ ht => deriv_carmonPsi_zero_of_le ht)
    abs_deriv_carmonPsi_le_446 abs_deriv_carmonPhi_le (by norm_num) a b
  have htri := norm_sub_le (deriv carmonPsi (-a) * deriv carmonPhi (-b))
    (deriv carmonPsi a * deriv carmonPhi b)
  simp only [Real.norm_eq_abs] at htri
  unfold chainLinkPrevCurrent
  linarith

theorem abs_chainLinkCurrentCurrent_le (a b : ℝ) :
    |chainLinkCurrentCurrent a b| ≤ (2719 / 1000 : ℝ) := by
  have h := supported_products_abs_sum_le (fun _ ht => carmonPsi_zero_of_le ht)
    abs_carmonPsi_le_2719 abs_second_deriv_carmonPhi_le_one (by norm_num) a b
  have htri := norm_sub_le (carmonPsi (-a) * deriv (deriv carmonPhi) (-b))
    (carmonPsi a * deriv (deriv carmonPhi) b)
  simp only [Real.norm_eq_abs] at htri
  unfold chainLinkCurrentCurrent
  linarith

/-- A finite orthogonal family of subunit vectors, including the zero
virtual predecessor, obeys the usual synthesis bound. -/
theorem orthogonal_subunit_sum_sq_le {d T : ℕ} {V : Fin T → Point d}
    (horth : Pairwise (fun i j => inner ℝ (V i) (V j) = 0))
    (hnorm : ∀ i, ‖V i‖ ≤ 1) (c : Fin T → ℝ) :
    ‖∑ i, c i • V i‖ ^ 2 ≤ ∑ i, (c i) ^ 2 := by
  have heq : ‖∑ i, c i • V i‖ ^ 2 = ∑ i, (c i) ^ 2 * ‖V i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    calc
      ∑ j, inner ℝ (c i • V i) (c j • V j) = inner ℝ (c i • V i) (c i • V i) := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          simp [real_inner_smul_left, real_inner_smul_right, horth hji.symm]
        · simp
      _ = (c i) ^ 2 * ‖V i‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [heq]
  apply Finset.sum_le_sum
  intro i hi
  have hn : ‖V i‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr (hnorm i)
  nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg (c i))]

theorem orthogonal_subunit_bessel {d T : ℕ} {V : Fin T → Point d}
    (horth : Pairwise (fun i j => inner ℝ (V i) (V j) = 0))
    (hnorm : ∀ i, ‖V i‖ ≤ 1) (x : Point d) :
    ∑ i, (inner ℝ (V i) x) ^ 2 ≤ ‖x‖ ^ 2 := by
  let w := ∑ i, (inner ℝ (V i) x) • V i
  have hnormw : ‖w‖ ^ 2 ≤ ∑ i, (inner ℝ (V i) x) ^ 2 :=
    orthogonal_subunit_sum_sq_le horth hnorm _
  have hin : inner ℝ w x = ∑ i, (inner ℝ (V i) x) ^ 2 := by
    simp [w, sum_inner, real_inner_smul_left, pow_two]
  have hn := sq_nonneg ‖x - w‖
  rw [norm_sub_sq_real, real_inner_comm w x, hin] at hn
  linarith

theorem orthogonal_subunit_sum_norm_le {d T : ℕ} {V : Fin T → Point d}
    (horth : Pairwise (fun i j => inner ℝ (V i) (V j) = 0))
    (hnorm : ∀ i, ‖V i‖ ≤ 1) (c : Fin T → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) :
    ‖∑ i, c i • V i‖ ≤ C * Real.sqrt T := by
  have hsum : (∑ i, (c i) ^ 2) ≤ C ^ 2 * T := by
    calc
      _ ≤ ∑ _i : Fin T, C ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hc i)
      _ = _ := by simp [mul_comm]
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ T)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
  rw [mul_pow, hs]
  exact (orthogonal_subunit_sum_sq_le horth hnorm c).trans hsum

theorem chainPredecessorVector_pairwise {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) :
    Pairwise (fun i j => inner ℝ (chainPredecessorVector U i) (chainPredecessorVector U j) = 0) := by
  intro i j hij
  by_cases hi : i.val = 0
  · simp [chainPredecessorVector, hi]
  by_cases hj : j.val = 0
  · simp [chainPredecessorVector, hj]
  simp only [chainPredecessorVector, dif_neg hi, dif_neg hj]
  apply hU.inner_eq_zero
  intro heq
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val heq
  simp only [Fin.val_mk] at hv
  omega

/-- A rectangular coefficient block between two orthogonal subunit families. -/
def orthogonalCoefficientBlock {d T : ℕ} (V W : Fin T → Point d) (c : Fin T → ℝ) :
    Point d →L[ℝ] Point d →L[ℝ] ℝ :=
  ∑ i, (c i • innerSL ℝ (V i)).smulRight (innerSL ℝ (W i))

theorem norm_orthogonalCoefficientBlock_le {d T : ℕ} {V W : Fin T → Point d}
    (hV : Pairwise (fun i j => inner ℝ (V i) (V j) = 0)) (hVn : ∀ i, ‖V i‖ ≤ 1)
    (hW : Pairwise (fun i j => inner ℝ (W i) (W j) = 0)) (hWn : ∀ i, ‖W i‖ ≤ 1)
    (c : Fin T → ℝ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) :
    ‖orthogonalCoefficientBlock V W c‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have heq : orthogonalCoefficientBlock V W c x =
      innerSL ℝ (∑ i, (c i * inner ℝ (V i) x) • W i) := by
    ext v
    simp [orthogonalCoefficientBlock, innerSL_apply_apply, sum_inner,
      real_inner_smul_left, smul_eq_mul]
  rw [heq, innerSL_apply_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  calc
    _ ≤ ∑ i, (c i * inner ℝ (V i) x) ^ 2 := orthogonal_subunit_sum_sq_le hW hWn _
    _ ≤ C ^ 2 * ∑ i, (inner ℝ (V i) x) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hci : (c i) ^ 2 ≤ C ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hc i)
      simpa only [mul_pow] using mul_le_mul_of_nonneg_right hci (sq_nonneg _)
    _ ≤ C ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (orthogonal_subunit_bessel hV hVn x) (sq_nonneg _)
    _ = (C * ‖x‖) ^ 2 := by ring


theorem hasFDerivAt_carmonChainLink_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {a' b' : E →L[ℝ] ℝ} {x : E}
    (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (fun y => carmonChainLink (a y) (b y))
      (chainLinkPrev (a x) (b x) • a' + chainLinkCurrent (a x) (b x) • b') x := by
  have hψa := (contDiff_carmonPsi_two.differentiable (by norm_num) (a x)).hasDerivAt.comp_hasFDerivAt x ha
  have hψn := (contDiff_carmonPsi_two.differentiable (by norm_num) (-a x)).hasDerivAt.comp_hasFDerivAt x ha.fun_neg
  have hφb := (differentiable_carmonPhi (b x)).hasDerivAt.comp_hasFDerivAt x hb
  have hφn := (differentiable_carmonPhi (-b x)).hasDerivAt.comp_hasFDerivAt x hb.fun_neg
  have h := (hψn.fun_mul hφn).fun_sub (hψa.fun_mul hφb)
  convert! h using 1 <;> ext v <;>
    simp only [carmonChainLink, chainLinkPrev, chainLinkCurrent,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, Function.comp_apply, Pi.neg_apply, smul_eq_mul] <;> ring

theorem hasFDerivAt_chainLinkPrev_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {a' b' : E →L[ℝ] ℝ} {x : E}
    (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (fun y => chainLinkPrev (a y) (b y))
      (chainLinkPrevPrev (a x) (b x) • a' + chainLinkPrevCurrent (a x) (b x) • b') x := by
  have hψa := (contDiff_carmonPsi_two.differentiable_deriv_two (a x)).hasDerivAt.comp_hasFDerivAt x ha
  have hψn := (contDiff_carmonPsi_two.differentiable_deriv_two (-a x)).hasDerivAt.comp_hasFDerivAt x ha.fun_neg
  have hφb := (differentiable_carmonPhi (b x)).hasDerivAt.comp_hasFDerivAt x hb
  have hφn := (differentiable_carmonPhi (-b x)).hasDerivAt.comp_hasFDerivAt x hb.fun_neg
  have h := (hψn.fun_neg.fun_mul hφn).fun_sub (hψa.fun_mul hφb)
  convert! h using 1 <;> ext v <;>
    simp only [chainLinkPrev, chainLinkPrevPrev, chainLinkPrevCurrent,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, Function.comp_apply, Pi.neg_apply, smul_eq_mul] <;> ring

theorem hasFDerivAt_chainLinkCurrent_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {a' b' : E →L[ℝ] ℝ} {x : E}
    (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (fun y => chainLinkCurrent (a y) (b y))
      (chainLinkPrevCurrent (a x) (b x) • a' + chainLinkCurrentCurrent (a x) (b x) • b') x := by
  have hψa := (contDiff_carmonPsi_two.differentiable (by norm_num) (a x)).hasDerivAt.comp_hasFDerivAt x ha
  have hψn := (contDiff_carmonPsi_two.differentiable (by norm_num) (-a x)).hasDerivAt.comp_hasFDerivAt x ha.fun_neg
  have hφb := (contDiff_carmonPhi_two.differentiable_deriv_two (b x)).hasDerivAt.comp_hasFDerivAt x hb
  have hφn := (contDiff_carmonPhi_two.differentiable_deriv_two (-b x)).hasDerivAt.comp_hasFDerivAt x hb.fun_neg
  have h := (hψn.fun_neg.fun_mul hφn).fun_sub (hψa.fun_mul hφb)
  convert! h using 1 <;> ext v <;>
    simp only [chainLinkCurrent, chainLinkPrevCurrent, chainLinkCurrentCurrent,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, Function.comp_apply, Pi.neg_apply, smul_eq_mul] <;> ring

/-- Exact derivative formula for the manuscript chain on the ambient space. -/
theorem hasFDerivAt_carmonChain_pullback {d T : ℕ} (U : Fin T → Point d) (y : Point d) :
    HasFDerivAt (fun x => carmonChain (frameCoordinates U x))
      (∑ k : Fin T, (chainLinkPrev (chainPredecessor (frameCoordinates U y) k) (frameCoordinates U y k) •
          innerSL ℝ (chainPredecessorVector U k) +
        chainLinkCurrent (chainPredecessor (frameCoordinates U y) k) (frameCoordinates U y k) •
          innerSL ℝ (U k))) y := by
  simp_rw [carmonChain_eq_sum_links]
  apply HasFDerivAt.fun_sum
  intro k hk
  exact hasFDerivAt_carmonChainLink_comp (hasFDerivAt_chainPredecessor_pullback U k y)
    (innerSL ℝ (U k)).hasFDerivAt

/-- The actual ambient Euclidean first-derivative norm, including `T = 0`. -/
theorem norm_fderiv_carmonChain_pullback_le_23_sqrt {d T : ℕ}
    {U : Fin T → Point d} (hU : Orthonormal ℝ U) (y : Point d) :
    ‖fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x)) y‖ ≤
      23 * Real.sqrt T := by
  let a : Fin T → ℝ := fun k => chainPredecessor (frameCoordinates U y) k
  let b : Fin T → ℝ := frameCoordinates U y
  have horth : Pairwise (fun i j => inner ℝ (U i) (U j) = 0) :=
    fun _ _ hij => hU.inner_eq_zero hij
  have hnorm : ∀ i, ‖U i‖ ≤ 1 := fun i => (hU.norm_eq_one i).le
  have hp := orthogonal_subunit_sum_norm_le (chainPredecessorVector_pairwise hU)
    (chainPredecessorVector_norm_le hU) (fun k => chainLinkPrev (a k) (b k))
    (by norm_num : (0 : ℝ) ≤ 46161 / 2500) (fun k => abs_chainLinkPrev_le (a k) (b k))
  have hc := orthogonal_subunit_sum_norm_le horth hnorm (fun k => chainLinkCurrent (a k) (b k))
    (by norm_num : (0 : ℝ) ≤ 89727 / 20000) (fun k => abs_chainLinkCurrent_le (a k) (b k))
  have heq : fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x)) y =
      innerSL ℝ ((∑ k, chainLinkPrev (a k) (b k) • chainPredecessorVector U k) +
        ∑ k, chainLinkCurrent (a k) (b k) • U k) := by
    rw [(hasFDerivAt_carmonChain_pullback U y).fderiv]
    ext v
    simp only [a, b, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, innerSL_apply_apply, inner_add_left, sum_inner,
      real_inner_smul_left, smul_eq_mul, Finset.sum_add_distrib]
  rw [heq, innerSL_apply_norm]
  calc
    _ ≤ ‖∑ k, chainLinkPrev (a k) (b k) • chainPredecessorVector U k‖ +
        ‖∑ k, chainLinkCurrent (a k) (b k) • U k‖ := norm_add_le _ _
    _ ≤ (46161 / 2500 : ℝ) * Real.sqrt T + (89727 / 20000 : ℝ) * Real.sqrt T := add_le_add hp hc
    _ ≤ 23 * Real.sqrt T := by nlinarith [Real.sqrt_nonneg (T : ℝ)]

def carmonChainSecondMap {d T : ℕ} (U : Fin T → Point d) (y : Point d) :
    Point d →L[ℝ] Point d →L[ℝ] ℝ :=
  let a := fun k => chainPredecessor (frameCoordinates U y) k
  let b := frameCoordinates U y
  ((orthogonalCoefficientBlock (chainPredecessorVector U) (chainPredecessorVector U)
      (fun k => chainLinkPrevPrev (a k) (b k)) +
    orthogonalCoefficientBlock U (chainPredecessorVector U)
      (fun k => chainLinkPrevCurrent (a k) (b k))) +
    orthogonalCoefficientBlock (chainPredecessorVector U) U
      (fun k => chainLinkPrevCurrent (a k) (b k))) +
    orthogonalCoefficientBlock U U (fun k => chainLinkCurrentCurrent (a k) (b k))

theorem hasFDerivAt_fderiv_carmonChain_pullback {d T : ℕ} (U : Fin T → Point d) (y : Point d) :
    HasFDerivAt (fderiv ℝ (fun x => carmonChain (frameCoordinates U x)))
      (carmonChainSecondMap U y) y := by
  have heq : fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x)) = (fun x =>
      ∑ k : Fin T, (chainLinkPrev (chainPredecessor (frameCoordinates U x) k) (frameCoordinates U x k) •
          innerSL ℝ (chainPredecessorVector U k) +
        chainLinkCurrent (chainPredecessor (frameCoordinates U x) k) (frameCoordinates U x k) •
          innerSL ℝ (U k))) := by
    funext x
    exact (hasFDerivAt_carmonChain_pullback U x).fderiv
  rw [heq]
  have hi (k : Fin T) :=
    ((hasFDerivAt_chainLinkPrev_comp (hasFDerivAt_chainPredecessor_pullback U k y)
      (innerSL ℝ (U k)).hasFDerivAt).smul_const (innerSL ℝ (chainPredecessorVector U k))).fun_add
    ((hasFDerivAt_chainLinkCurrent_comp (hasFDerivAt_chainPredecessor_pullback U k y)
      (innerSL ℝ (U k)).hasFDerivAt).smul_const (innerSL ℝ (U k)))
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ => hi k)
  apply h.congr_fderiv
  ext u v
  simp only [carmonChainSecondMap, orthogonalCoefficientBlock, frameCoordinates, innerSL_apply_apply,
    FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- The sparse four-block budget is `134.55 + 7.359 + 7.359 + 2.719 = 151.987`.
All norms are ambient Euclidean operator norms, independent of `d` and `T`. -/
theorem norm_second_fderiv_carmonChain_pullback_le_152 {d T : ℕ}
    {U : Fin T → Point d} (hU : Orthonormal ℝ U) (y : Point d) :
    ‖fderiv ℝ (fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x))) y‖ ≤ 152 := by
  let a : Fin T → ℝ := fun k => chainPredecessor (frameCoordinates U y) k
  let b : Fin T → ℝ := frameCoordinates U y
  have horth : Pairwise (fun i j => inner ℝ (U i) (U j) = 0) :=
    fun _ _ hij => hU.inner_eq_zero hij
  have hnorm : ∀ i, ‖U i‖ ≤ 1 := fun i => (hU.norm_eq_one i).le
  have hp := chainPredecessorVector_pairwise hU
  have hpn := chainPredecessorVector_norm_le hU
  have haa := norm_orthogonalCoefficientBlock_le hp hpn hp hpn
    (fun k => chainLinkPrevPrev (a k) (b k)) (by norm_num : (0 : ℝ) ≤ 2691 / 20)
    (fun k => abs_chainLinkPrevPrev_le (a k) (b k))
  have hab := norm_orthogonalCoefficientBlock_le horth hnorm hp hpn
    (fun k => chainLinkPrevCurrent (a k) (b k)) (by norm_num : (0 : ℝ) ≤ 7359 / 1000)
    (fun k => abs_chainLinkPrevCurrent_le (a k) (b k))
  have hba := norm_orthogonalCoefficientBlock_le hp hpn horth hnorm
    (fun k => chainLinkPrevCurrent (a k) (b k)) (by norm_num : (0 : ℝ) ≤ 7359 / 1000)
    (fun k => abs_chainLinkPrevCurrent_le (a k) (b k))
  have hbb := norm_orthogonalCoefficientBlock_le horth hnorm horth hnorm
    (fun k => chainLinkCurrentCurrent (a k) (b k)) (by norm_num : (0 : ℝ) ≤ 2719 / 1000)
    (fun k => abs_chainLinkCurrentCurrent_le (a k) (b k))
  rw [(hasFDerivAt_fderiv_carmonChain_pullback U y).fderiv]
  unfold carmonChainSecondMap
  dsimp only
  calc
    _ ≤ ((‖orthogonalCoefficientBlock (chainPredecessorVector U) (chainPredecessorVector U)
          (fun k => chainLinkPrevPrev (a k) (b k))‖ +
        ‖orthogonalCoefficientBlock U (chainPredecessorVector U)
          (fun k => chainLinkPrevCurrent (a k) (b k))‖) +
        ‖orthogonalCoefficientBlock (chainPredecessorVector U) U
          (fun k => chainLinkPrevCurrent (a k) (b k))‖) +
        ‖orthogonalCoefficientBlock U U (fun k => chainLinkCurrentCurrent (a k) (b k))‖ := by
      exact (ContinuousLinearMap.opNorm_add_le _ _).trans
        (add_le_add ((ContinuousLinearMap.opNorm_add_le _ _).trans
          (add_le_add (ContinuousLinearMap.opNorm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ ((2691 / 20 : ℝ) + 7359 / 1000 + 7359 / 1000) + 2719 / 1000 :=
      add_le_add (add_le_add (add_le_add haa hab) hba) hbb
    _ ≤ 152 := by norm_num

end

end HeavyTailedNoise
