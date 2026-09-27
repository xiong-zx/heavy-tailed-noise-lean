import HeavyTailedNoise.Lower.Gated.HardObjectiveSmoothness
import HeavyTailedNoise.Lower.Gated.PrefixLocality
import HeavyTailedNoise.Analysis.CarmonChainStationarity

/-!
Actual stationarity barrier for the finite gated Haar construction. Queries
remain arbitrary points of the ambient Euclidean space. The near-region
condition is derived from a small gradient, never imposed on the algorithm.
-/

namespace HeavyTailedNoise

open scoped BigOperators Topology Classical

noncomputable section

theorem hardStationarity_radius_pos {T : ℕ} (hT : 0 < T) : 0 < hardRadius T := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  unfold hardRadius
  positivity

theorem fderiv_hardPotential {d T : ℕ} (hT : 0 < T) (U : Fin T → Point d) (x : Point d) :
    fderiv ℝ (hardPotential U) x =
      (fderiv ℝ (hardPreprojectionPotential U) (softProjection (hardRadius T) x)).comp
        (fderiv ℝ (softProjection (hardRadius T)) x) + (1 / 5 : ℝ) • innerSL ℝ x := by
  have hc := ((contDiff_hardPreprojectionPotential_two U).differentiable (by norm_num)
    (softProjection (hardRadius T) x)).hasFDerivAt.comp x
      ((contDiff_softProjection_two (hardStationarity_radius_pos hT)).differentiable (by norm_num) x).hasFDerivAt
  exact (hc.fun_add (hasFDerivAt_hardQuadratic x)).fderiv

theorem fderiv_softProjection_apply_in_image {d : ℕ} {R : ℝ} (hR : 0 < R) (x v : Point d) :
    fderiv ℝ (softProjection R) x v =
      softProjectionScale R x • v -
        (softProjectionScale R x / R ^ 2 * inner ℝ (softProjection R x) v) • softProjection R x := by
  rw [fderiv_softProjection_eq_rank hR]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    softProjectionRank, softProjectionRankBilinear_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  let a := softProjectionScale R x
  change a • v - (a ^ 3 / R ^ 2) • (inner ℝ x v • x) =
    a • v - (a / R ^ 2 * inner ℝ (a • x) v) • (a • x)
  rw [real_inner_smul_left, smul_smul, smul_smul]
  congr 2
  ring

def hardRadialCoefficient {d T : ℕ} (U : Fin T → Point d) (x : Point d) : ℝ :=
  let y := softProjection (hardRadius T) x
  softProjectionScale (hardRadius T) x / (hardRadius T) ^ 2 *
    fderiv ℝ (hardPreprojectionPotential U) y y

theorem fderiv_hardPotential_apply {d T : ℕ} (hT : 0 < T) (U : Fin T → Point d) (x v : Point d) :
    fderiv ℝ (hardPotential U) x v =
      softProjectionScale (hardRadius T) x *
        fderiv ℝ (hardPreprojectionPotential U) (softProjection (hardRadius T) x) v -
      hardRadialCoefficient U x * inner ℝ (softProjection (hardRadius T) x) v +
        (1 / 5 : ℝ) * inner ℝ x v := by
  rw [fderiv_hardPotential hT U x]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [fderiv_softProjection_apply_in_image (hardStationarity_radius_pos hT), map_sub, map_smul, map_smul]
  simp only [smul_eq_mul]
  unfold hardRadialCoefficient
  ring

theorem abs_hardRadialCoefficient_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d) : |hardRadialCoefficient U x| ≤ (1 / 20 : ℝ) := by
  let R := hardRadius T
  let y := softProjection R x
  let a := softProjectionScale R x
  let Γ := 23 * Real.sqrt T + 100
  have hR : 0 < R := hardStationarity_radius_pos hT
  have ha : 0 ≤ a := (softProjection_scale_pos_le_one hR x).1.le
  have ha1 : a ≤ 1 := (softProjection_scale_pos_le_one hR x).2
  have hΓ : 0 ≤ Γ := by dsimp [Γ]; positivity
  have hDF : |fderiv ℝ (hardPreprojectionPotential U) y y| ≤ Γ * R := by
    have h := (fderiv ℝ (hardPreprojectionPotential U) y).le_opNorm y
    have hb := mul_le_mul (norm_fderiv_hardPreprojectionPotential_le hU y)
      (norm_softProjection_lt_radius hR x).le (norm_nonneg y) hΓ
    have hfirst : |fderiv ℝ (hardPreprojectionPotential U) y y| ≤
        ‖fderiv ℝ (hardPreprojectionPotential U) y‖ * ‖y‖ := by
      simpa only [Real.norm_eq_abs] using h
    exact hfirst.trans hb
  change |a / R ^ 2 * fderiv ℝ (hardPreprojectionPotential U) y y| ≤ 1 / 20
  rw [abs_mul, abs_of_nonneg (div_nonneg ha (sq_nonneg R))]
  calc
    _ ≤ (a / R ^ 2) * (Γ * R) := mul_le_mul_of_nonneg_left hDF (by positivity)
    _ = a * (Γ / R) := by field_simp [hR.ne'] <;> ring
    _ ≤ 1 * (1 / 20 : ℝ) := mul_le_mul ha1 (hardPreprojection_gradient_over_radius_le hT)
      (div_nonneg hΓ hR.le) (by norm_num)
    _ = 1 / 20 := by ring


/-- Global far-query bound; no condition is placed on the algorithm's query. -/
theorem norm_gradient_hardPotential_lower_radial {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d) :
    (1 / 5 : ℝ) * ‖x‖ - (23 * Real.sqrt T + 100) ≤ ‖gradient (hardPotential U) x‖ := by
  let A := (fderiv ℝ (hardPreprojectionPotential U) (softProjection (hardRadius T) x)).comp
    (fderiv ℝ (softProjection (hardRadius T)) x)
  have hA : ‖A‖ ≤ 23 * Real.sqrt T + 100 := by
    calc
      _ ≤ ‖fderiv ℝ (hardPreprojectionPotential U) (softProjection (hardRadius T) x)‖ *
          ‖fderiv ℝ (softProjection (hardRadius T)) x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (23 * Real.sqrt T + 100) * 1 := mul_le_mul
        (norm_fderiv_hardPreprojectionPotential_le hU _)
        (norm_fderiv_softProjection_le_one (hardStationarity_radius_pos hT) x) (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have heq : (1 / 5 : ℝ) • innerSL ℝ x = fderiv ℝ (hardPotential U) x - A := by
    rw [fderiv_hardPotential hT U x]
    change (1 / 5 : ℝ) • innerSL ℝ x = A + (1 / 5 : ℝ) • innerSL ℝ x - A
    abel
  have hb : (1 / 5 : ℝ) * ‖x‖ ≤ ‖fderiv ℝ (hardPotential U) x‖ + ‖A‖ := by
    calc
      _ = ‖(1 / 5 : ℝ) • innerSL ℝ x‖ := by simp [norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
      _ = ‖fderiv ℝ (hardPotential U) x - A‖ := by rw [heq]
      _ ≤ _ := norm_sub_le _ _
  have hn : ‖gradient (hardPotential U) x‖ = ‖fderiv ℝ (hardPotential U) x‖ := by simp [gradient]
  rw [hn]
  linarith

theorem one_le_norm_gradient_hardPotential_of_far {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d)
    (hx : (1 + (23 * Real.sqrt T + 100)) / (1 / 5 : ℝ) ≤ ‖x‖) :
    1 ≤ ‖gradient (hardPotential U) x‖ := by
  have hm := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 5)).mp hx
  linarith [norm_gradient_hardPotential_lower_radial hU hT x]

/-- Small gradient forces the near region; this is a consequence, not a query restriction. -/
theorem softProjectionScale_gt_97_of_small_gradient {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d)
    (hg : ‖gradient (hardPotential U) x‖ < 1) :
    (97 / 100 : ℝ) < softProjectionScale (hardRadius T) x := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast Nat.succ_le_of_lt hT
  have hs : 1 ≤ Real.sqrt T := by
    have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ T)
    nlinarith [Real.sqrt_nonneg (T : ℝ)]
  have hr : ‖x‖ < 620 * Real.sqrt T := by
    nlinarith [norm_gradient_hardPotential_lower_radial hU hT x]
  have hR := hardStationarity_radius_pos hT
  have hratio : ‖x‖ / hardRadius T < (1 / 4 : ℝ) := by
    apply (div_lt_iff₀ hR).mpr
    unfold hardRadius
    nlinarith
  have hratio0 : 0 ≤ ‖x‖ / hardRadius T := div_nonneg (norm_nonneg _) hR.le
  have hsq : ‖x‖ ^ 2 / (hardRadius T) ^ 2 ≤ (1 / 16 : ℝ) := by
    have hh := (sq_le_sq₀ hratio0 (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hratio.le
    norm_num at hh
    simpa only [div_pow] using hh
  exact softProjection_scale_gt_97_of_scaled_norm_sq_le hR x hsq

/-- Transport a lower directional bound through the exact soft projection and regularizer. -/
theorem hardPotential_direction_lower {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x v : Point d) {s β : ℝ}
    (hs : 0 ≤ s) (hβ : 0 ≤ β)
    (hy : inner ℝ (softProjection (hardRadius T) x) v = s)
    (hf : -β * s ≤ fderiv ℝ (hardPreprojectionPotential U) (softProjection (hardRadius T) x) v) :
    (1 / 5 - β - 1 / 20) * s ≤ fderiv ℝ (hardPotential U) x v := by
  let a := softProjectionScale (hardRadius T) x
  have ha : 0 < a := (softProjection_scale_pos_le_one (hardStationarity_radius_pos hT) x).1
  have ha1 : a ≤ 1 := (softProjection_scale_pos_le_one (hardStationarity_radius_pos hT) x).2
  have hm : a * inner ℝ x v = s := by
    have hh : inner ℝ (softProjection (hardRadius T) x) v = a * inner ℝ x v := by
      change inner ℝ (a • x) v = a * inner ℝ x v
      exact real_inner_smul_left _ _ _
    exact hh.symm.trans hy
  have hx0 : 0 ≤ inner ℝ x v := by
    by_contra h
    have hn := mul_neg_of_pos_of_neg ha (lt_of_not_ge h)
    rw [hm] at hn
    exact not_lt_of_ge hs hn
  have hx : s ≤ inner ℝ x v := by
    have h := mul_le_mul_of_nonneg_right ha1 hx0
    simpa only [hm, one_mul] using h
  have hscaled : -β * s ≤ a * fderiv ℝ (hardPreprojectionPotential U) (softProjection (hardRadius T) x) v := by
    have h1 := mul_le_mul_of_nonneg_left hf ha.le
    have h2 := mul_le_mul_of_nonneg_right ha1 (mul_nonneg hβ hs)
    nlinarith
  have hc : hardRadialCoefficient U x ≤ (1 / 20 : ℝ) :=
    (le_abs_self _).trans (abs_hardRadialCoefficient_le hU hT x)
  have hrad : -(1 / 20 : ℝ) * s ≤ -hardRadialCoefficient U x * s := by
    nlinarith [mul_le_mul_of_nonneg_right hc hs]
  have hreg := mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 1 / 5)
  rw [fderiv_hardPotential_apply hT U x v, hy]
  change (1 / 5 - β - 1 / 20) * s ≤
    a * fderiv ℝ (hardPreprojectionPotential U) (softProjection (hardRadius T) x) v -
      hardRadialCoefficient U x * s + (1 / 5 : ℝ) * inner ℝ x v
  nlinarith

theorem deriv_smoothstep_nonneg (t : ℝ) : 0 ≤ deriv smoothstep t := by
  rw [deriv_smoothstep_formula]
  split_ifs <;> positivity

theorem deriv_carmonChi_nonpos (s : ℝ) : deriv carmonChi s ≤ 0 := by
  rw [deriv_carmonChi]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (deriv_smoothstep_nonneg _)) (by norm_num)

theorem carmonChi_one_of_le {s : ℝ} (hs : s ≤ 1 / 16) : carmonChi s = 1 := by
  unfold carmonChi
  rw [smoothstep_zero_of_nonpos (by linarith : (s - 1 / 16) / 1000 ≤ 0)]
  norm_num

theorem deriv_carmonChi_zero_of_le {s : ℝ} (hs : s ≤ 1 / 16) : deriv carmonChi s = 0 := by
  by_contra hn
  exact not_lt_of_ge hs (carmonChi_deriv_ne_zero_support hn).1

theorem abs_omegaSix_deriv_mul_coordinate_le (t : ℝ) : |deriv carmonOmegaSix t * t| ≤ (15 / 4 : ℝ) := by
  by_cases ht : |t| ≤ 1 / 8
  · have hd : |deriv carmonOmegaSix t| ≤ 30 := by
      have h := abs_deriv_stepWindow_le (a := (1 / 16 : ℝ)) (w := (1 / 16 : ℝ))
        (by norm_num) (by norm_num) t
      norm_num at h
      exact h
    rw [abs_mul]
    calc
      _ ≤ (30 : ℝ) * (1 / 8) := mul_le_mul hd ht (abs_nonneg _) (by norm_num)
      _ = 15 / 4 := by norm_num
  · norm_num [deriv_carmonOmegaSix_eq_zero_of_abs_ge (lt_of_not_ge ht).le]

theorem omegaThree_deriv_mul_one_sub_omegaSix (t : ℝ) :
    deriv carmonOmegaThree t * (1 - carmonOmegaSix t) = 0 := by
  by_cases ht : (1 / 8 : ℝ) ≤ |t|
  · simp [carmonOmegaSix_one ht]
  · have hω : carmonOmegaThree t = 0 := carmonOmegaThree_zero (by linarith [lt_of_not_ge ht])
    have hg := carmonOmegaThree_glaeser t
    rw [hω] at hg
    have hs : deriv carmonOmegaThree t * deriv carmonOmegaThree t = 0 := by nlinarith [sq_nonneg (deriv carmonOmegaThree t)]
    rcases mul_eq_zero.mp hs with hd | hd <;> simp [hd]

theorem actual_chainGateTerm_le_487 {T : ℕ} (z : Fin T → ℝ) (k : Fin T) :
    chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z k ≤ (487 / 100 : ℝ) := by
  have hnorm : ‖chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z k‖ ≤ (487 / 100 : ℝ) := by
    unfold chainGateTerm
    rw [norm_mul]
    calc
      _ ≤ (487 / 100 : ℝ) * 1 := mul_le_mul (norm_actual_chainCorrection_le z k)
        (norm_actual_chainSelector_le_one z k) (norm_nonneg _) (by norm_num)
      _ = _ := mul_one _
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)


/-- The manuscript's active residual direction `e^natural`. -/
def stationarityResidualDirection {d T : ℕ} (U : Fin T → Point d) (k : Fin T) (y : Point d) : Point d :=
  frameOrthogonalResidual U Finset.univ y +
    ∑ i ∈ Finset.univ.filter (k < ·),
      ((1 - carmonOmegaSix (frameCoordinates U y i)) * frameCoordinates U y i) • U i

theorem inner_self_full_frameResidual {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (y : Point d) :
    inner ℝ y (frameOrthogonalResidual U Finset.univ y) =
      ‖frameOrthogonalResidual U Finset.univ y‖ ^ 2 := by
  rw [frameOrthogonalResidual_norm_sq hU]
  unfold frameOrthogonalResidual
  rw [inner_sub_right, real_inner_self_eq_norm_sq, inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_smul_right, real_inner_comm (U i) y]
  simp [frameCoordinates, pow_two]

theorem frame_inner_stationarityResidualDirection_of_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) (i : Fin T) (hi : i ≤ k) :
    inner ℝ (U i) (stationarityResidualDirection U k y) = 0 := by
  have ho : inner ℝ (U i) (frameOrthogonalResidual U Finset.univ y) = 0 := by
    rw [real_inner_comm]
    exact full_frameResidual_orthogonal hU y i
  unfold stationarityResidualDirection
  rw [inner_add_right, ho, zero_add, inner_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i ≠ j := by
    intro heq
    subst j
    exact not_lt_of_ge hi (Finset.mem_filter.mp hj).2
  rw [inner_smul_right, hU.inner_eq_zero hij, mul_zero]

theorem frame_inner_stationarityResidualDirection_of_gt {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) (i : Fin T) (hi : k < i) :
    inner ℝ (U i) (stationarityResidualDirection U k y) =
      (1 - carmonOmegaSix (frameCoordinates U y i)) * frameCoordinates U y i := by
  have ho : inner ℝ (U i) (frameOrthogonalResidual U Finset.univ y) = 0 := by
    rw [real_inner_comm]
    exact full_frameResidual_orthogonal hU y i
  unfold stationarityResidualDirection
  rw [inner_add_right, ho, zero_add]
  exact hU.inner_right_sum _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

theorem predecessor_inner_stationarityResidualDirection_of_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) (i : Fin T) (hi : i ≤ k) :
    inner ℝ (chainPredecessorVector U i) (stationarityResidualDirection U k y) = 0 := by
  by_cases hi0 : i.val = 0
  · simp [chainPredecessorVector, hi0]
  · simp only [chainPredecessorVector, dif_neg hi0]
    apply frame_inner_stationarityResidualDirection_of_le hU k y
    change i.val - 1 ≤ k.val
    change i.val ≤ k.val at hi
    omega

theorem fullResidual_inner_stationarityResidualDirection {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    inner ℝ (frameOrthogonalResidual U Finset.univ y) (stationarityResidualDirection U k y) =
      ‖frameOrthogonalResidual U Finset.univ y‖ ^ 2 := by
  unfold stationarityResidualDirection
  rw [inner_add_right, real_inner_self_eq_norm_sq, inner_sum]
  simp only [inner_smul_right, full_frameResidual_orthogonal hU, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem inner_stationarityResidualDirection_eq_sigma {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    inner ℝ y (stationarityResidualDirection U k y) = gatedResidual U k y := by
  unfold stationarityResidualDirection
  rw [inner_add_right, inner_self_full_frameResidual hU, inner_sum, gatedResidual_eq_energy hU]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_smul_right, real_inner_comm (U i) y]
  simp only [frameCoordinates]
  ring

theorem norm_stationarityResidualDirection_sq_le_sigma {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    ‖stationarityResidualDirection U k y‖ ^ 2 ≤ gatedResidual U k y := by
  let c : Fin T → ℝ := fun i => (1 - carmonOmegaSix (frameCoordinates U y i)) * frameCoordinates U y i
  have hn : ‖∑ i ∈ Finset.univ.filter (k < ·), c i • U i‖ ^ 2 =
      ∑ i ∈ Finset.univ.filter (k < ·), (c i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa [pow_two] using hU.inner_sum c c (Finset.univ.filter (k < ·))
  have ho : inner ℝ (frameOrthogonalResidual U Finset.univ y)
      (∑ i ∈ Finset.univ.filter (k < ·), c i • U i) = 0 := by
    rw [inner_sum]
    simp only [inner_smul_right, full_frameResidual_orthogonal hU, mul_zero, Finset.sum_const_zero]
  calc
    _ = ‖frameOrthogonalResidual U Finset.univ y‖ ^ 2 +
        ∑ i ∈ Finset.univ.filter (k < ·), (c i) ^ 2 := by
      unfold stationarityResidualDirection
      change ‖frameOrthogonalResidual U Finset.univ y + ∑ i ∈ Finset.univ.filter (k < ·), c i • U i‖ ^ 2 = _
      rw [norm_add_sq_real, ho, hn]
      ring
    _ ≤ ‖frameOrthogonalResidual U Finset.univ y‖ ^ 2 +
        ∑ i ∈ Finset.univ.filter (k < ·),
          (1 - carmonOmegaSix (frameCoordinates U y i)) * (frameCoordinates U y i) ^ 2 := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i hi
      have h0 : 0 ≤ 1 - carmonOmegaSix (frameCoordinates U y i) := sub_nonneg.mpr (carmonOmegaSix_le_one _)
      have h1 : 1 - carmonOmegaSix (frameCoordinates U y i) ≤ 1 := by linarith [carmonOmegaSix_nonneg (frameCoordinates U y i)]
      have hsq : (1 - carmonOmegaSix (frameCoordinates U y i)) ^ 2 ≤
          1 - carmonOmegaSix (frameCoordinates U y i) := by nlinarith
      simpa only [c, mul_pow] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (frameCoordinates U y i))
    _ = gatedResidual U k y := (gatedResidual_eq_energy hU k y).symm

theorem fderiv_gatedResidual_on_stationarityDirection {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    fderiv ℝ (gatedResidual U k) y (stationarityResidualDirection U k y) =
      2 * ‖frameOrthogonalResidual U Finset.univ y‖ ^ 2 +
      ∑ i ∈ Finset.univ.filter (k < ·), residualCoordinateGradient (frameCoordinates U y i) *
        ((1 - carmonOmegaSix (frameCoordinates U y i)) * frameCoordinates U y i) := by
  rw [(hasFDerivAt_gatedResidual hU k y).fderiv, innerSL_apply_apply]
  unfold residualGradientVector
  rw [inner_add_left, real_inner_smul_left, fullResidual_inner_stationarityResidualDirection hU, sum_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_smul_left, frame_inner_stationarityResidualDirection_of_gt hU k y i (Finset.mem_filter.mp hi).2]

theorem residualCoordinateGradient_direction_lower (t : ℝ) :
    -(15 / 4 : ℝ) * (1 - carmonOmegaSix t) * t ^ 2 ≤
      residualCoordinateGradient t * ((1 - carmonOmegaSix t) * t) := by
  have hw : 0 ≤ 1 - carmonOmegaSix t := sub_nonneg.mpr (carmonOmegaSix_le_one t)
  have hd : deriv carmonOmegaSix t * t ≤ (15 / 4 : ℝ) :=
    (le_abs_self _).trans (abs_omegaSix_deriv_mul_coordinate_le t)
  have hm := mul_le_mul_of_nonneg_right hd (mul_nonneg hw (sq_nonneg t))
  have hs := mul_nonneg (sq_nonneg (1 - carmonOmegaSix t)) (sq_nonneg t)
  unfold residualCoordinateGradient
  nlinarith

theorem fderiv_gatedResidual_on_stationarityDirection_lower {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    -(15 / 4 : ℝ) * gatedResidual U k y ≤
      fderiv ℝ (gatedResidual U k) y (stationarityResidualDirection U k y) := by
  rw [fderiv_gatedResidual_on_stationarityDirection hU, gatedResidual_eq_energy hU]
  calc
    _ = -(15 / 4 : ℝ) * ‖frameOrthogonalResidual U Finset.univ y‖ ^ 2 +
        ∑ i ∈ Finset.univ.filter (k < ·), -(15 / 4 : ℝ) *
          (1 - carmonOmegaSix (frameCoordinates U y i)) * (frameCoordinates U y i) ^ 2 := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := add_le_add (by nlinarith [sq_nonneg ‖frameOrthogonalResidual U Finset.univ y‖])
      (Finset.sum_le_sum (fun i _ => residualCoordinateGradient_direction_lower (frameCoordinates U y i)))


theorem chainLinkPrev_zero_of_predecessor_small {a b : ℝ} (ha : |a| ≤ (1 / 2 : ℝ)) :
    chainLinkPrev a b = 0 := by
  obtain ⟨hl, hu⟩ := abs_le.mp ha
  simp [chainLinkPrev, deriv_carmonPsi_zero_of_le hu,
    deriv_carmonPsi_zero_of_le (by linarith : -a ≤ (1 / 2 : ℝ))]

theorem chainLinkCurrent_zero_of_predecessor_small {a b : ℝ} (ha : |a| ≤ (1 / 2 : ℝ)) :
    chainLinkCurrent a b = 0 := by
  obtain ⟨hl, hu⟩ := abs_le.mp ha
  simp [chainLinkCurrent, carmonPsi_zero_of_le hu,
    carmonPsi_zero_of_le (by linarith : -a ≤ (1 / 2 : ℝ))]

theorem chainPredecessor_small_after_active {T : ℕ} {z : Fin T → ℝ} {k i : Fin T}
    (hactive : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z k ≠ 0)
    (hki : k < i) : |chainPredecessor z i| ≤ (1 / 2 : ℝ) := by
  obtain ⟨_, hk, hlater⟩ := chainGateTerm_support (fun _ ht => carmonPsi_zero_of_le ht)
    (fun _ ht => carmonOmega_one ht) (fun _ ht => carmonOmegaThree_one ht) hactive
  have hi0 : i.val ≠ 0 := by omega
  let p : Fin T := ⟨i.val - 1, by omega⟩
  have hkp : k ≤ p := by change k.val ≤ i.val - 1; change k.val < i.val at hki; omega
  have hp : |z p| < (1 / 2 : ℝ) := by
    rcases lt_or_eq_of_le hkp with hlt | heq
    · exact hlater p hlt
    · simpa only [← heq] using hk
  simpa [chainPredecessor, hi0, p] using hp.le

theorem fderiv_carmonChain_on_active_direction_eq_zero {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d)
    (hactive : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0) :
    fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x)) y
      (stationarityResidualDirection U k y) = 0 := by
  rw [(hasFDerivAt_carmonChain_pullback U y).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hik : i ≤ k
  · rw [predecessor_inner_stationarityResidualDirection_of_le hU k y i hik,
      frame_inner_stationarityResidualDirection_of_le hU k y i hik]
    ring
  · have hp := chainPredecessor_small_after_active hactive (lt_of_not_ge hik)
    rw [chainLinkPrev_zero_of_predecessor_small hp, chainLinkCurrent_zero_of_predecessor_small hp]
    ring

theorem fderiv_chainCorrection_on_stationarityDirection_eq_zero {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    fderiv ℝ (fun x : Point d => chainCorrection carmonPsi carmonPhi carmonOmega 1
      (frameCoordinates U x) k) y (stationarityResidualDirection U k y) = 0 := by
  have hd := hasFDerivAt_frontierCorrection_comp (hasFDerivAt_chainPredecessor_pullback U k y)
    (innerSL ℝ (U k)).hasFDerivAt
  rw [show fderiv ℝ (fun x : Point d => chainCorrection carmonPsi carmonPhi carmonOmega 1
    (frameCoordinates U x) k) y = _ from hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [predecessor_inner_stationarityResidualDirection_of_le hU k y k le_rfl,
    frame_inner_stationarityResidualDirection_of_le hU k y k le_rfl]
  ring

theorem fderiv_chainSelector_on_stationarityDirection_eq_zero {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    fderiv ℝ (fun x : Point d => chainSelector carmonOmegaThree (frameCoordinates U x) k) y
      (stationarityResidualDirection U k y) = 0 := by
  rw [show fderiv ℝ (fun x : Point d => chainSelector carmonOmegaThree (frameCoordinates U x) k) y =
      innerSL ℝ (selectorProductGradient U (Finset.univ.filter (k < ·)) y) from
    (hasFDerivAt_selectorProduct U (Finset.univ.filter (k < ·)) y).fderiv]
  rw [innerSL_apply_apply]
  unfold selectorProductGradient
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro i hi
  rw [real_inner_smul_left,
    frame_inner_stationarityResidualDirection_of_gt hU k y i (Finset.mem_filter.mp hi).2]
  let P := ∏ j ∈ (Finset.univ.filter (k < ·)).erase i, (1 - carmonOmegaThree (frameCoordinates U y j))
  change (P * (-deriv carmonOmegaThree (frameCoordinates U y i))) *
    ((1 - carmonOmegaSix (frameCoordinates U y i)) * frameCoordinates U y i) = 0
  calc
    _ = -P * (deriv carmonOmegaThree (frameCoordinates U y i) *
        (1 - carmonOmegaSix (frameCoordinates U y i))) * frameCoordinates U y i := by ring
    _ = 0 := by rw [omegaThree_deriv_mul_one_sub_omegaSix]; ring

theorem fderiv_chainGateTerm_on_stationarityDirection_eq_zero {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    fderiv ℝ (fun x : Point d => chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U x) k) y (stationarityResidualDirection U k y) = 0 := by
  have hq : ContDiff ℝ 2 (fun x : Point d => chainCorrection carmonPsi carmonPhi carmonOmega 1
      (frameCoordinates U x) k) :=
    (contDiff_chainCorrection 1 k contDiff_carmonPsi_two contDiff_carmonPhi_two contDiff_carmonOmega_two).comp
      (contDiff_frameCoordinates_two U)
  have hp : ContDiff ℝ 2 (fun x : Point d => chainSelector carmonOmegaThree (frameCoordinates U x) k) :=
    (contDiff_chainSelector k contDiff_carmonOmegaThree_two).comp (contDiff_frameCoordinates_two U)
  unfold chainGateTerm
  rw [fderiv_fun_mul (hq.differentiable (by norm_num) y) (hp.differentiable (by norm_num) y)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_chainCorrection_on_stationarityDirection_eq_zero hU k y,
    fderiv_chainSelector_on_stationarityDirection_eq_zero hU k y]
  ring

theorem fderiv_gateFactor_actual {d T : ℕ} (U : Fin T → Point d) (k : Fin T) (y : Point d) :
    fderiv ℝ (fun x : Point d => 1 - carmonChi (gatedResidual U k x)) y =
      -(deriv carmonChi (gatedResidual U k y) • fderiv ℝ (gatedResidual U k) y) := by
  exact (((contDiff_carmonChi_two.differentiable (by norm_num) (gatedResidual U k y)).hasDerivAt.comp_hasFDerivAt y
    ((contDiff_gatedResidual_two U k).differentiable (by norm_num) y).hasFDerivAt).const_sub 1).fderiv

theorem fderiv_gatedCorrectionTerm_on_stationarityDirection {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    fderiv ℝ (gatedCorrectionTerm U k) y (stationarityResidualDirection U k y) =
      -deriv carmonChi (gatedResidual U k y) *
        chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 (frameCoordinates U y) k *
        fderiv ℝ (gatedResidual U k) y (stationarityResidualDirection U k y) := by
  have ha : ContDiff ℝ 2 (fun x : Point d => 1 - carmonChi (gatedResidual U k x)) :=
    contDiff_const.sub (contDiff_carmonChi_two.comp (contDiff_gatedResidual_two U k))
  have hs : ContDiff ℝ 2 (fun x : Point d => chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U x) k) := (contDiff_actual_chainGateTerm_two k).comp (contDiff_frameCoordinates_two U)
  unfold gatedCorrectionTerm
  rw [fderiv_fun_mul (ha.differentiable (by norm_num) y) (hs.differentiable (by norm_num) y),
    fderiv_gateFactor_actual]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
  rw [fderiv_chainGateTerm_on_stationarityDirection_eq_zero hU k y]
  ring

theorem fderiv_gatedCorrectionTerm_zero_of_residual_le {d T : ℕ}
    (U : Fin T → Point d) (k : Fin T) (y : Point d) (hσ : gatedResidual U k y ≤ (1 / 16 : ℝ)) :
    fderiv ℝ (gatedCorrectionTerm U k) y = 0 := by
  have ha : ContDiff ℝ 2 (fun x : Point d => 1 - carmonChi (gatedResidual U k x)) :=
    contDiff_const.sub (contDiff_carmonChi_two.comp (contDiff_gatedResidual_two U k))
  have hs : ContDiff ℝ 2 (fun x : Point d => chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U x) k) := (contDiff_actual_chainGateTerm_two k).comp (contDiff_frameCoordinates_two U)
  unfold gatedCorrectionTerm
  rw [fderiv_fun_mul (ha.differentiable (by norm_num) y) (hs.differentiable (by norm_num) y),
    fderiv_gateFactor_actual, carmonChi_one_of_le hσ, deriv_carmonChi_zero_of_le hσ]
  simp

theorem fderiv_hardPreprojection_on_active_direction {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d)
    (hactive : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0) :
    fderiv ℝ (hardPreprojectionPotential U) y (stationarityResidualDirection U k y) =
      -deriv carmonChi (gatedResidual U k y) *
        chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 (frameCoordinates U y) k *
        fderiv ℝ (gatedResidual U k) y (stationarityResidualDirection U k y) := by
  rw [fderiv_hardPreprojectionPotential, ContinuousLinearMap.add_apply,
    fderiv_carmonChain_on_active_direction_eq_zero hU k y hactive,
    fderiv_gatedCorrection_eq_active U y hactive, zero_add]
  exact fderiv_gatedCorrectionTerm_on_stationarityDirection hU k y

theorem fderiv_hardPreprojection_on_active_direction_lower {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d)
    (hactive : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0) :
    -(7 / 200 : ℝ) * gatedResidual U k y ≤
      fderiv ℝ (hardPreprojectionPotential U) y (stationarityResidualDirection U k y) := by
  let σ := gatedResidual U k y
  let S := chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 (frameCoordinates U y) k
  let α := -deriv carmonChi σ * S
  have hσ : 0 ≤ σ := gatedResidual_nonneg hU k y
  have hS : 0 ≤ S := actual_chainGateTerm_nonneg _ _
  have hSupper : S ≤ (487 / 100 : ℝ) := actual_chainGateTerm_le_487 _ _
  have hχ : 0 ≤ -deriv carmonChi σ := neg_nonneg.mpr (deriv_carmonChi_nonpos σ)
  have hχupper : -deriv carmonChi σ ≤ (15 / 8 : ℝ) / 1000 :=
    (neg_le_abs _).trans (abs_deriv_carmonChi_le σ)
  have hα : 0 ≤ α := mul_nonneg hχ hS
  have hαupper : α ≤ ((15 / 8 : ℝ) / 1000) * (487 / 100) :=
    mul_le_mul hχupper hSupper hS (by norm_num)
  have hD := fderiv_gatedResidual_on_stationarityDirection_lower hU k y
  have h1 := mul_le_mul_of_nonneg_left hD hα
  have h2 := mul_le_mul_of_nonneg_right hαupper (mul_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 4) hσ)
  rw [fderiv_hardPreprojection_on_active_direction hU k y hactive]
  change -(7 / 200 : ℝ) * σ ≤ α * fderiv ℝ (gatedResidual U k) y (stationarityResidualDirection U k y)
  change α * (-(15 / 4 : ℝ) * σ) ≤ α * fderiv ℝ (gatedResidual U k) y (stationarityResidualDirection U k y) at h1
  nlinarith


theorem norm_functional_ge_one_fortieth_of_direction {d : ℕ} (L : Point d →L[ℝ] ℝ)
    (v : Point d) (s : ℝ) (hs : (1 / 16 : ℝ) ≤ s) (hv : ‖v‖ ^ 2 ≤ s)
    (hdir : (1 / 10 : ℝ) * s ≤ L v) : (1 / 40 : ℝ) ≤ ‖L‖ := by
  have hspos : 0 < s := by linarith
  have hL0 := L.opNorm_nonneg
  have hupper : L v ≤ ‖L‖ * ‖v‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using L.le_opNorm v)
  have hprod := hdir.trans hupper
  by_contra hnot
  have hg : ‖L‖ < (1 / 40 : ℝ) := lt_of_not_ge hnot
  have hsq : ((1 / 10 : ℝ) * s) ^ 2 ≤ (‖L‖ * ‖v‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg hL0 (norm_nonneg v))).mpr hprod
  have hLsq : ‖L‖ ^ 2 < (1 / 40 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hL0 (by norm_num : (0 : ℝ) ≤ 1 / 40)).mpr hg
  have h1 := mul_le_mul_of_nonneg_left hv (sq_nonneg ‖L‖)
  have h2 := mul_lt_mul_of_pos_right hLsq hspos
  have h3 := mul_le_mul_of_nonneg_right hs hspos.le
  simp only [mul_pow] at hsq
  nlinarith

/-- The active residual-gate case excludes stationarity at every query location. -/
theorem norm_gradient_hardPotential_ge_one_fortieth_of_active_high_residual
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (hT : 0 < T)
    (x : Point d) (k : Fin T)
    (hactive : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U (softProjection (hardRadius T) x)) k ≠ 0)
    (hσ : (1 / 16 : ℝ) ≤ gatedResidual U k (softProjection (hardRadius T) x)) :
    (1 / 40 : ℝ) ≤ ‖gradient (hardPotential U) x‖ := by
  let y := softProjection (hardRadius T) x
  let e := stationarityResidualDirection U k y
  let σ := gatedResidual U k y
  have hσ0 : 0 ≤ σ := gatedResidual_nonneg hU k y
  have hf := fderiv_hardPreprojection_on_active_direction_lower hU k y hactive
  have hd := hardPotential_direction_lower hU hT x e hσ0
    (by norm_num : (0 : ℝ) ≤ 7 / 200)
    (inner_stationarityResidualDirection_eq_sigma hU k y) hf
  have hd' : (1 / 10 : ℝ) * σ ≤ fderiv ℝ (hardPotential U) x e := by
    norm_num at hd
    nlinarith
  have hb := norm_functional_ge_one_fortieth_of_direction (fderiv ℝ (hardPotential U) x) e σ hσ
    (norm_stationarityResidualDirection_sq_le_sigma hU k y) hd'
  simpa [gradient] using hb

/-- Any small-gradient point has exactly zero correction derivative. -/
theorem fderiv_gatedCorrection_zero_at_small_gradient {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d)
    (hg : ‖gradient (hardPotential U) x‖ < (1 / 40 : ℝ)) :
    fderiv ℝ (gatedCorrection U) (softProjection (hardRadius T) x) = 0 := by
  let y := softProjection (hardRadius T) x
  by_cases hex : ∃ k : Fin T, chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0
  · obtain ⟨k, hk⟩ := hex
    have hlow : gatedResidual U k y < (1 / 16 : ℝ) := by
      by_contra h
      exact not_lt_of_ge (norm_gradient_hardPotential_ge_one_fortieth_of_active_high_residual hU hT x k hk
        (le_of_not_gt h)) hg
    rw [fderiv_gatedCorrection_eq_active U y hk]
    exact fderiv_gatedCorrectionTerm_zero_of_residual_le U k y hlow.le
  · apply fderiv_gatedCorrection_eq_zero_of_all_inactive
    intro k
    by_contra hk
    exact hex ⟨k, hk⟩

theorem fderiv_hardPotential_frontier_lt_neg_seven_tenths {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d) (k : Fin T)
    (hcurrent : |frameCoordinates U (softProjection (hardRadius T) x) k| < 1)
    (hforce : fderiv ℝ (hardPreprojectionPotential U) (softProjection (hardRadius T) x) (U k) < -1)
    (ha97 : (97 / 100 : ℝ) < softProjectionScale (hardRadius T) x) :
    fderiv ℝ (hardPotential U) x (U k) < -(7 / 10 : ℝ) := by
  let a := softProjectionScale (hardRadius T) x
  let z := frameCoordinates U (softProjection (hardRadius T) x) k
  let t := inner ℝ x (U k)
  let b := hardRadialCoefficient U x
  have ha : 0 < a := (softProjection_scale_pos_le_one (hardStationarity_radius_pos hT) x).1
  have hz : z = a * t := by
    change inner ℝ (U k) (a • x) = a * inner ℝ x (U k)
    rw [real_inner_smul_right, real_inner_comm]
  have hzt : z < 1 := (le_abs_self z).trans_lt hcurrent
  have hreg : (1 / 5 : ℝ) * t < (21 / 100 : ℝ) := by
    by_cases ht : t ≤ 0
    · nlinarith
    · have htpos : 0 < t := lt_of_not_ge ht
      have hm := mul_lt_mul_of_pos_right ha97 htpos
      change (97 / 100 : ℝ) * t < a * t at hm
      rw [← hz] at hm
      nlinarith
  have hrad : -b * z ≤ (1 / 20 : ℝ) := by
    have hab : |b * z| ≤ (1 / 20 : ℝ) := by
      rw [abs_mul]
      calc
        _ ≤ (1 / 20 : ℝ) * 1 := mul_le_mul (abs_hardRadialCoefficient_le hU hT x)
          hcurrent.le (abs_nonneg z) (by norm_num)
        _ = _ := mul_one _
    nlinarith [neg_le_abs (b * z)]
  have hf := mul_lt_mul_of_pos_left hforce ha
  have hy : inner ℝ (softProjection (hardRadius T) x) (U k) = z := by
    rw [real_inner_comm]
    rfl
  rw [fderiv_hardPotential_apply hT U x (U k), hy]
  change a * fderiv ℝ (hardPreprojectionPotential U) (softProjection (hardRadius T) x) (U k) -
    b * z + (1 / 5 : ℝ) * t < -(7 / 10 : ℝ)
  nlinarith

theorem fderiv_carmonChain_on_fullResidual_eq_zero {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (y : Point d) :
    fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x)) y
      (frameOrthogonalResidual U Finset.univ y) = 0 := by
  have hc (i : Fin T) : inner ℝ (U i) (frameOrthogonalResidual U Finset.univ y) = 0 := by
    rw [real_inner_comm]
    exact full_frameResidual_orthogonal hU y i
  have hp (i : Fin T) : inner ℝ (chainPredecessorVector U i) (frameOrthogonalResidual U Finset.univ y) = 0 := by
    by_cases hi : i.val = 0
    · simp [chainPredecessorVector, hi]
    · simp only [chainPredecessorVector, dif_neg hi]
      exact hc _
  rw [(hasFDerivAt_carmonChain_pullback U y).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, hp, hc,
    mul_zero, add_zero, Finset.sum_const_zero]

theorem fullResidual_norm_lt_one_sixth_of_small_gradient {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d)
    (hg : ‖gradient (hardPotential U) x‖ < (1 / 40 : ℝ))
    (hQ : fderiv ℝ (gatedCorrection U) (softProjection (hardRadius T) x) = 0) :
    ‖frameOrthogonalResidual U Finset.univ (softProjection (hardRadius T) x)‖ < (1 / 6 : ℝ) := by
  let y := softProjection (hardRadius T) x
  let r := frameOrthogonalResidual U Finset.univ y
  have hp : fderiv ℝ (hardPreprojectionPotential U) y r = 0 := by
    rw [fderiv_hardPreprojectionPotential, ContinuousLinearMap.add_apply, hQ,
      ContinuousLinearMap.zero_apply, add_zero]
    exact fderiv_carmonChain_on_fullResidual_eq_zero hU y
  have hd := hardPotential_direction_lower hU hT x r (sq_nonneg ‖r‖)
    (by norm_num : (0 : ℝ) ≤ 0) (inner_self_full_frameResidual hU y) (by rw [hp]; norm_num)
  have hn : ‖fderiv ℝ (hardPotential U) x‖ < (1 / 40 : ℝ) := by simpa [gradient] using hg
  have hupper : fderiv ℝ (hardPotential U) x r ≤ ‖fderiv ℝ (hardPotential U) x‖ * ‖r‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (fderiv ℝ (hardPotential U) x).le_opNorm r)
  by_contra hnot
  have hr : (1 / 6 : ℝ) ≤ ‖r‖ := le_of_not_gt hnot
  have hrpos : 0 < ‖r‖ := by linarith
  have hstrict := mul_lt_mul_of_pos_right hn hrpos
  have hsq := mul_le_mul_of_nonneg_right hr (norm_nonneg r)
  norm_num at hd
  nlinarith

/-- The exact global stationarity decoding statement of the frozen construction. -/
theorem hardPotential_stationarity_decoding {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d)
    (hg : ‖gradient (hardPotential U) x‖ < (1 / 40 : ℝ)) :
    (∀ i : Fin T, 1 ≤ |frameCoordinates U (softProjection (hardRadius T) x) i|) ∧
      ‖frameOrthogonalResidual U Finset.univ (softProjection (hardRadius T) x)‖ < (1 / 6 : ℝ) := by
  let y := softProjection (hardRadius T) x
  have hQ := fderiv_gatedCorrection_zero_at_small_gradient hU hT x hg
  have hp : fderiv ℝ (hardPreprojectionPotential U) y =
      fderiv ℝ (fun z : Point d => carmonChain (frameCoordinates U z)) y := by
    rw [fderiv_hardPreprojectionPotential, hQ, add_zero]
  constructor
  · by_contra hnot
    have hex : ∃ i : Fin T, |frameCoordinates U y i| < 1 := by simpa only [not_forall, not_le] using hnot
    obtain ⟨k, hcurrent, hprev⟩ := exists_carmon_frontier_of_small_coordinate (frameCoordinates U y) hex
    have hforce : fderiv ℝ (hardPreprojectionPotential U) y (U k) < -1 := by
      rw [hp]
      exact fderiv_carmonChain_frontier_lt_neg_one hU y k hprev hcurrent
    have ha97 := softProjectionScale_gt_97_of_small_gradient hU hT x (hg.trans (by norm_num))
    have hd := fderiv_hardPotential_frontier_lt_neg_seven_tenths hU hT x k hcurrent hforce ha97
    have hb : |fderiv ℝ (hardPotential U) x (U k)| ≤ ‖fderiv ℝ (hardPotential U) x‖ := by
      simpa only [Real.norm_eq_abs, hU.norm_eq_one k, mul_one] using
        (fderiv ℝ (hardPotential U) x).le_opNorm (U k)
    have hn : ‖fderiv ℝ (hardPotential U) x‖ < (1 / 40 : ℝ) := by simpa [gradient] using hg
    nlinarith [neg_le_abs (fderiv ℝ (hardPotential U) x (U k))]
  · exact fullResidual_norm_lt_one_sixth_of_small_gradient hU hT x hg hQ

/-- Small-gradient outputs lie in the final cap used in the stage-counting argument. -/
theorem mem_final_prefixCapSet_of_small_gradient {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (j : Fin T) (hj : j.val + 1 = T) (x : Point d)
    (hg : ‖gradient (hardPotential U) x‖ < (1 / 40 : ℝ)) :
    softProjection (hardRadius T) x ∈ prefixCapSet U j := by
  obtain ⟨hc, hr⟩ := hardPotential_stationarity_decoding hU hT x hg
  have hfilter : Finset.univ.filter (· ≤ j) = (Finset.univ : Finset (Fin T)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have hi := i.isLt
    change i.val ≤ j.val
    omega
  change (1 / 2 : ℝ) ≤ |frameCoordinates U (softProjection (hardRadius T) x) j| ∧ _
  constructor
  · linarith [hc j]
  · rw [hfilter]
    have hs := (sq_le_sq₀ (norm_nonneg (frameOrthogonalResidual U Finset.univ (softProjection (hardRadius T) x)))
      (by norm_num : (0 : ℝ) ≤ 1 / 6)).mpr hr.le
    nlinarith

end

end HeavyTailedNoise
