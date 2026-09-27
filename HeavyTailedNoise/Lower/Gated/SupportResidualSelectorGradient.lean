import HeavyTailedNoise.Lower.Gated.SupportResidualQGradient

/-!
Exact scalar curvature, Glaeser, and finite-product estimates for the ambient
Euclidean derivative of the manuscript's suffix selector. No coordinate
sup-norm is substituted for the Euclidean norm.
-/

namespace HeavyTailedNoise

open Set Filter
open scoped BigOperators Topology

noncomputable section

/-- A second-order Taylor proof of the scalar Glaeser inequality. -/
theorem scalar_glaeser {f : ℝ → ℝ} {M : ℝ} (hf : ContDiff ℝ 2 f)
    (hf0 : ∀ t, 0 ≤ f t) (hM : 0 < M)
    (hf2 : ∀ t, |deriv (deriv f) t| ≤ M) (x : ℝ) :
    (deriv f x) ^ 2 ≤ 2 * M * f x := by
  by_cases hd : deriv f x = 0
  · rw [hd, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    have hx := hf0 x
    positivity
  let z : ℝ := x - deriv f x / M
  have hxz : x ≠ z := by
    intro h
    have hz : deriv f x / M = 0 := by dsimp [z] at h; linarith
    exact (div_ne_zero hd hM.ne') hz
  obtain ⟨c, hc, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hxz hf.contDiffOn
  have hwithin : derivWithin f (uIcc x z) x = deriv f x :=
    (hf.differentiable (by norm_num) x).derivWithin
      ((uniqueDiffOn_uIcc hxz) x left_mem_uIcc)
  have htaylor : taylorWithinEval f 1 (uIcc x z) x z = f x + (z - x) * deriv f x := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, taylorWithinEval_succ, taylor_within_zero_eval]
    norm_num [iteratedDerivWithin_one, hwithin, smul_eq_mul]
  have htwo : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have heq : f z - (f x + (z - x) * deriv f x) =
      deriv (deriv f) c * (z - x) ^ 2 / 2 := by
    simpa [htaylor, htwo, hwithin, Nat.factorial] using hrem
  have hb : deriv (deriv f) c ≤ M := (le_abs_self _).trans (hf2 c)
  have hbmul := mul_le_mul_of_nonneg_right hb (sq_nonneg (z - x))
  have hupper : f z ≤ f x + (z - x) * deriv f x + M * (z - x) ^ 2 / 2 := by
    linarith
  have hquad : 0 ≤ f x - (deriv f x) ^ 2 / (2 * M) := by
    calc
      0 ≤ f z := hf0 z
      _ ≤ f x + (z - x) * deriv f x + M * (z - x) ^ 2 / 2 := hupper
      _ = _ := by
        dsimp [z]
        field_simp [hM.ne']
        ring
  have hdiv : (deriv f x) ^ 2 / (2 * M) ≤ f x := by linarith
  have h := (div_le_iff₀ (by positivity : 0 < 2 * M)).mp hdiv
  nlinarith

/-- A rational curvature bound for the exact quintic. The polynomial identity
behind the estimate is `4/27-u(1-u)^2=(u-1/3)^2(4/3-u)`. -/
theorem abs_second_deriv_smoothstep_le (t : ℝ) :
    |deriv (deriv smoothstep) t| ≤ (231 / 40 : ℝ) := by
  rw [second_deriv_smoothstep_formula]
  split_ifs with h0 h1
  · norm_num
  · norm_num
  · have ht0 : 0 ≤ t := (lt_of_not_ge h0).le
    have ht1 : t ≤ 1 := (lt_of_not_ge h1).le
    have hu : (2 * t - 1) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
    have hcert := mul_nonneg (sq_nonneg ((2 * t - 1) ^ 2 - 1 / 3))
      (show 0 ≤ (4 / 3 : ℝ) - (2 * t - 1) ^ 2 by linarith)
    have hsq : (60 * t * (t - 1) * (2 * t - 1)) ^ 2 ≤ (100 / 3 : ℝ) := by
      nlinarith
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 231 / 40)).mp
    rw [sq_abs]
    nlinarith

lemma deriv_smoothstep_affine (c d x : ℝ) :
    deriv (fun t => smoothstep (c * t + d)) x = deriv smoothstep (c * x + d) * c := by
  have ha : HasDerivAt (fun t : ℝ => c * t + d) c x := by
    simpa using ((hasDerivAt_id x).const_mul c).add_const d
  exact (((differentiable_smoothstep _).hasDerivAt).comp x ha).deriv

lemma second_deriv_smoothstep_affine (c d x : ℝ) :
    deriv (deriv (fun t => smoothstep (c * t + d))) x =
      c ^ 2 * deriv (deriv smoothstep) (c * x + d) := by
  have heq : deriv (fun t => smoothstep (c * t + d)) =
      (fun t => deriv smoothstep (c * t + d) * c) := funext (deriv_smoothstep_affine c d)
  rw [heq]
  have ha : HasDerivAt (fun t : ℝ => c * t + d) c x := by
    simpa using ((hasDerivAt_id x).const_mul c).add_const d
  have h := (((differentiable_deriv_smoothstep _).hasDerivAt).comp x ha).mul_const c
  convert! h.deriv using 1 <;> ring

/-- Curvature bound for every positive-width absolute-value window, with the
zero neighborhood and both signs treated separately. -/
theorem abs_second_deriv_stepWindow_le {a w : ℝ} (ha : 0 < a) (hw : 0 < w) (z : ℝ) :
    |deriv (deriv (stepWindow a w)) z| ≤ (231 / 40 : ℝ) / w ^ 2 := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · have hlocal : stepWindow a w =ᶠ[𝓝 z]
        (fun t : ℝ => smoothstep ((-1 / w) * t + (-a / w))) := by
      filter_upwards [Iio_mem_nhds hz] with t ht
      change t < 0 at ht
      unfold stepWindow
      rw [abs_of_neg ht]
      congr 1
      ring
    rw [hlocal.deriv.deriv_eq, second_deriv_smoothstep_affine, abs_mul, abs_pow,
      abs_div, abs_neg, abs_one, abs_of_pos hw]
    calc
      _ ≤ (1 / w) ^ 2 * (231 / 40 : ℝ) :=
        mul_le_mul_of_nonneg_left (abs_second_deriv_smoothstep_le _) (sq_nonneg _)
      _ = _ := by ring
  · have hlocal := stepWindow_eventually_zero hw (show |(0 : ℝ)| < a by simpa using ha)
    have hzero : deriv (deriv (stepWindow a w)) 0 = 0 := by
      simpa using hlocal.deriv.deriv_eq
    rw [hzero, abs_zero]
    positivity
  · have hlocal : stepWindow a w =ᶠ[𝓝 z]
        (fun t : ℝ => smoothstep ((1 / w) * t + (-a / w))) := by
      filter_upwards [Ioi_mem_nhds hz] with t ht
      change 0 < t at ht
      unfold stepWindow
      rw [abs_of_pos ht]
      congr 1
      ring
    rw [hlocal.deriv.deriv_eq, second_deriv_smoothstep_affine, abs_mul, abs_pow,
      abs_div, abs_one, abs_of_pos hw]
    calc
      _ ≤ (1 / w) ^ 2 * (231 / 40 : ℝ) :=
        mul_le_mul_of_nonneg_left (abs_second_deriv_smoothstep_le _) (sq_nonneg _)
      _ = _ := by ring

theorem abs_second_deriv_carmonOmegaThree_le (z : ℝ) :
    |deriv (deriv carmonOmegaThree) z| ≤ (462 / 5 : ℝ) := by
  have h := abs_second_deriv_stepWindow_le (a := (1 / 4 : ℝ)) (w := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) z
  norm_num at h
  exact h

theorem carmonOmegaThree_glaeser (z : ℝ) :
    (deriv carmonOmegaThree z) ^ 2 ≤ (924 / 5 : ℝ) * carmonOmegaThree z := by
  have h := scalar_glaeser contDiff_carmonOmegaThree_two
    (fun t => (smoothstep_nonneg _ : 0 ≤ carmonOmegaThree t))
    (by norm_num : (0 : ℝ) < 462 / 5) abs_second_deriv_carmonOmegaThree_le z
  convert h using 1 <;> ring

/-- Frozen exponential-product calculation, stated for arbitrary finite scalar
data. Products with a removed index avoid division at selector endpoints. -/
theorem finite_selector_square_sum_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α δ : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hα : ∀ i ∈ s, 0 ≤ α i ∧ α i ≤ 1)
    (hδ : ∀ i ∈ s, (δ i) ^ 2 ≤ C * α i) :
    (∑ i ∈ s, ((∏ j ∈ s.erase i, (1 - α j)) * δ i) ^ 2) ≤ C := by
  let S : ℝ := ∑ i ∈ s, α i
  let P : ι → ℝ := fun i => ∏ j ∈ s.erase i, (1 - α j)
  have hP0 (i : ι) : 0 ≤ P i := by
    apply Finset.prod_nonneg
    intro j hj
    exact sub_nonneg.mpr (hα j (Finset.mem_of_mem_erase hj)).2
  have hP1 (i : ι) : P i ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro j hj
      exact sub_nonneg.mpr (hα j (Finset.mem_of_mem_erase hj)).2
    · intro j hj
      have h := (hα j (Finset.mem_of_mem_erase hj)).1
      linarith
  have hPexp (i : ι) (hi : i ∈ s) : P i ≤ Real.exp 1 * Real.exp (-S) := by
    calc
      P i ≤ ∏ j ∈ s.erase i, Real.exp (-α j) :=
        Finset.prod_le_prod₀ (fun j hj => sub_nonneg.mpr (hα j (Finset.mem_of_mem_erase hj)).2)
          (fun j _ => Real.one_sub_le_exp_neg (α j))
      _ = Real.exp (-(∑ j ∈ s.erase i, α j)) := by
        rw [← Real.exp_sum, Finset.sum_neg_distrib]
      _ ≤ Real.exp (1 - S) := by
        apply Real.exp_le_exp.mpr
        have hs := Finset.sum_erase_add s α hi
        have hi1 := (hα i hi).2
        dsimp [S]
        linarith
      _ = Real.exp 1 * Real.exp (-S) := by rw [sub_eq_add_neg, Real.exp_add]
  have hterm (i : ι) (hi : i ∈ s) : (P i * δ i) ^ 2 ≤
      C * α i * (Real.exp 1 * Real.exp (-S)) := by
    have hsq : (P i) ^ 2 ≤ P i := by nlinarith [hP0 i, hP1 i]
    calc
      _ = (δ i) ^ 2 * (P i) ^ 2 := by ring
      _ ≤ (C * α i) * P i :=
        mul_le_mul (hδ i hi) hsq (sq_nonneg _) (mul_nonneg hC (hα i hi).1)
      _ ≤ C * α i * (Real.exp 1 * Real.exp (-S)) :=
        mul_le_mul_of_nonneg_left (hPexp i hi) (mul_nonneg hC (hα i hi).1)
  calc
    _ ≤ ∑ i ∈ s, C * α i * (Real.exp 1 * Real.exp (-S)) :=
      Finset.sum_le_sum hterm
    _ = C * Real.exp 1 * (S * Real.exp (-S)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      dsimp [S]
      ring
    _ ≤ C * Real.exp 1 * Real.exp (-1) :=
      mul_le_mul_of_nonneg_left (Real.mul_exp_neg_le_exp_neg_one S)
        (mul_nonneg hC (Real.exp_pos 1).le)
    _ = C := by
      rw [Real.exp_neg]
      field_simp [(Real.exp_pos 1).ne']

/-- Exact ambient coefficient vector of a selected finite product. -/
def selectorProductGradient {d T : ℕ} (U : Fin T → Point d)
    (s : Finset (Fin T)) (y : Point d) : Point d :=
  ∑ i ∈ s,
    ((∏ j ∈ s.erase i, (1 - carmonOmegaThree (frameCoordinates U y j))) *
      (-deriv carmonOmegaThree (frameCoordinates U y i))) • U i

theorem hasFDerivAt_selectorProduct {d T : ℕ} (U : Fin T → Point d)
    (s : Finset (Fin T)) (y : Point d) :
    HasFDerivAt (fun x => ∏ i ∈ s, (1 - carmonOmegaThree (frameCoordinates U x i)))
      (innerSL ℝ (selectorProductGradient U s y)) y := by
  have hfac (i : Fin T) :
      HasFDerivAt (fun x => 1 - carmonOmegaThree (frameCoordinates U x i))
        (-(deriv carmonOmegaThree (frameCoordinates U y i) • innerSL ℝ (U i))) y :=
    ((((contDiff_carmonOmegaThree_two.differentiable (by norm_num)
      (frameCoordinates U y i)).hasDerivAt).comp_hasFDerivAt y
        (innerSL ℝ (U i)).hasFDerivAt).const_sub 1)
  have hp := HasFDerivAt.finsetProd (u := s) (fun i _ => hfac i)
  have hmap :
      (∑ i ∈ s, (∏ j ∈ s.erase i, (1 - carmonOmegaThree (frameCoordinates U y j))) •
        (-(deriv carmonOmegaThree (frameCoordinates U y i) • innerSL ℝ (U i)))) =
      innerSL ℝ (selectorProductGradient U s y) := by
    unfold selectorProductGradient
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      innerSL_apply_apply, real_inner_smul_left, smul_eq_mul]
    ring
  exact hp.congr_fderiv hmap

theorem selectorProductGradient_norm_sq {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (y : Point d) :
    ‖selectorProductGradient U s y‖ ^ 2 =
      ∑ i ∈ s, ((∏ j ∈ s.erase i, (1 - carmonOmegaThree (frameCoordinates U y j))) *
        (-deriv carmonOmegaThree (frameCoordinates U y i))) ^ 2 := by
  unfold selectorProductGradient
  rw [← real_inner_self_eq_norm_sq]
  simpa [pow_two] using hU.inner_sum
    (fun i => (∏ j ∈ s.erase i, (1 - carmonOmegaThree (frameCoordinates U y j))) *
      (-deriv carmonOmegaThree (frameCoordinates U y i)))
    (fun i => (∏ j ∈ s.erase i, (1 - carmonOmegaThree (frameCoordinates U y j))) *
      (-deriv carmonOmegaThree (frameCoordinates U y i))) s

/-- The ambient bound holds globally, including zero factors and empty suffixes. -/
theorem norm_fderiv_selectorProduct_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (y : Point d) :
    ‖fderiv ℝ (fun x => ∏ i ∈ s, (1 - carmonOmegaThree (frameCoordinates U x i))) y‖ ≤
      (68 / 5 : ℝ) := by
  rw [(hasFDerivAt_selectorProduct U s y).fderiv, innerSL_apply_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 68 / 5)).mp
  rw [selectorProductGradient_norm_sq hU]
  have hbound := finite_selector_square_sum_le s
    (fun i => carmonOmegaThree (frameCoordinates U y i))
    (fun i => -deriv carmonOmegaThree (frameCoordinates U y i))
    (C := (924 / 5 : ℝ)) (by norm_num)
    (fun i _ => ⟨smoothstep_nonneg _, smoothstep_le_one _⟩)
    (fun i _ => by simpa only [neg_sq] using carmonOmegaThree_glaeser (frameCoordinates U y i))
  exact hbound.trans (by norm_num)

theorem norm_fderiv_chainSelector_pullback_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    ‖fderiv ℝ (fun x => chainSelector carmonOmegaThree (frameCoordinates U x) k) y‖ ≤
      (68 / 5 : ℝ) :=
  norm_fderiv_selectorProduct_le hU (Finset.univ.filter (k < ·)) y

/-- The exact selector estimate removes its premise from the bound on Q. Only
the active residual-gradient estimate on the support of χ' remains. -/
theorem norm_gradient_gatedCorrection_le_100_of_residual_bounds
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (y : Point d)
    (hσ : ∀ k : Fin T,
      chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
        (frameCoordinates U y) k ≠ 0 →
      deriv carmonChi (gatedResidual U k y) ≠ 0 →
        ‖fderiv ℝ (gatedResidual U k) y‖ ≤ (3169 / 10 : ℝ)) :
    ‖gradient (gatedCorrection U) y‖ ≤ 100 := by
  apply norm_gradient_gatedCorrection_le_100_of_selector_residual_bounds hU y
  intro k hk
  exact ⟨norm_fderiv_chainSelector_pullback_le hU k y, hσ k hk⟩

end

end HeavyTailedNoise
