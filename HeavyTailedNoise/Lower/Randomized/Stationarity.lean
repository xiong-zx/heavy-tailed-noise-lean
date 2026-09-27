import HeavyTailedNoise.Lower.Randomized.Projection
import HeavyTailedNoise.Lower.Gated.HardStationarity

/-! Deterministic gap and all-point barrier for the actual Bernoulli/Carmon lift. -/

namespace HeavyTailedNoise.RandomizedLift

open scoped BigOperators
noncomputable section

@[simp] theorem coordinates_zero {d T : ℕ} (U : Fin T → Point d) (R : ℝ) :
    coordinates U R 0 = 0 := by
  ext i
  simp [coordinates, softProjection_zero, frameCoordinates]

theorem potential_gap_le_12T {d T : ℕ} (U : Fin T → Point d) (R : ℝ)
    {η : ℝ} (hη : 0 ≤ η) (x : Point d) :
    potential U R η 0 - potential U R η x ≤ 12 * T := by
  have hc := carmonChainValue_gap_le_12T (coordinates U R x)
  have hr : 0 ≤ (η / 2) * ‖x‖ ^ 2 := by positivity
  simpa only [potential, coordinates_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero] using (show carmonChainValue 0 -
      (carmonChainValue (coordinates U R x) + (η/2) * ‖x‖ ^ 2) ≤ 12 * T by linarith)

/-- The actual formula packaged in the existing shared Objective model. -/
def objective {d T : ℕ} (hd : 0 < d) (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) (η : ℝ) (hη : 0 ≤ η) : Objective d (12 * T) where
  dimension_pos := hd
  value := potential U R η
  grad := populationGradient U R η
  hasGradientAt := hasGradientAt_potential U hR η
  continuous_grad := continuous_populationGradient U hR η
  gap := potential_gap_le_12T U R hη

theorem fderiv_potential {d T : ℕ} (U : Fin T → Point d) {R : ℝ}
    (hR : 0 < R) (η : ℝ) (x : Point d) :
    fderiv ℝ (potential U R η) x =
      (fderiv ℝ (fun y : Point d => carmonChain (frameCoordinates U y)) (softProjection R x)).comp
        (fderiv ℝ (softProjection R) x) + η • innerSL ℝ x := by
  have hP : Differentiable ℝ (fun y : Point d => carmonChain (frameCoordinates U y)) :=
    ((contDiff_carmonChain_two T).comp (contDiff_frameCoordinates_two U)).differentiable (by norm_num)
  have hc := (hP (softProjection R x)).hasFDerivAt.comp x
    ((((contDiff_softProjection_two hR).differentiable (by norm_num)) x).hasFDerivAt)
  have hq : HasFDerivAt (fun y : Point d => (η/2)*‖y‖^2) (η • innerSL ℝ x) x := by
    have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (η/2)
    apply h.congr_fderiv
    ext v
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  exact (hc.add hq).fderiv

def radialCoefficient {d T : ℕ} (U : Fin T → Point d) (R : ℝ) (x : Point d) : ℝ :=
  softProjectionScale R x / R ^ 2 *
    fderiv ℝ (fun y : Point d => carmonChain (frameCoordinates U y)) (softProjection R x) (softProjection R x)

theorem fderiv_potential_apply {d T : ℕ} (U : Fin T → Point d) {R : ℝ}
    (hR : 0 < R) (η : ℝ) (x v : Point d) :
    fderiv ℝ (potential U R η) x v =
      softProjectionScale R x *
        fderiv ℝ (fun y : Point d => carmonChain (frameCoordinates U y)) (softProjection R x) v -
      radialCoefficient U R x * inner ℝ (softProjection R x) v + η * inner ℝ x v := by
  rw [fderiv_potential U hR η x]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [fderiv_softProjection_apply_in_image hR, map_sub, map_smul, map_smul]
  simp only [smul_eq_mul]
  unfold radialCoefficient
  ring

theorem abs_radialCoefficient_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (x : Point d) :
    |radialCoefficient U R x| ≤ (23 * Real.sqrt T) / R := by
  let a := softProjectionScale R x
  let y := softProjection R x
  have ha : 0 ≤ a := (softProjection_scale_pos_le_one hR x).1.le
  have ha1 : a ≤ 1 := (softProjection_scale_pos_le_one hR x).2
  have hDF : |fderiv ℝ (fun y : Point d => carmonChain (frameCoordinates U y)) y y| ≤
      (23 * Real.sqrt T) * R := by
    have hn := (fderiv ℝ (fun y : Point d => carmonChain (frameCoordinates U y)) y).le_opNorm y
    exact (show |fderiv ℝ (fun y : Point d => carmonChain (frameCoordinates U y)) y y| ≤
      ‖fderiv ℝ (fun y : Point d => carmonChain (frameCoordinates U y)) y‖ * ‖y‖ by simpa using hn).trans
      (mul_le_mul (norm_fderiv_carmonChain_pullback_le_23_sqrt hU y)
        (norm_softProjection_lt_radius hR x).le (norm_nonneg y) (by positivity))
  change |a / R ^ 2 * fderiv ℝ (fun y : Point d => carmonChain (frameCoordinates U y)) y y| ≤ _
  rw [abs_mul, abs_of_nonneg (div_nonneg ha (sq_nonneg R))]
  calc
    _ ≤ (a / R^2) * ((23 * Real.sqrt T) * R) := mul_le_mul_of_nonneg_left hDF (by positivity)
    _ = a * ((23 * Real.sqrt T) / R) := by field_simp [hR.ne'] <;> ring
    _ ≤ 1 * ((23 * Real.sqrt T) / R) := mul_le_mul_of_nonneg_right ha1 (by positivity)
    _ = _ := one_mul _

theorem populationGradient_radial_lower {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) {η : ℝ} (hη : 0 ≤ η) (x : Point d) :
    η * ‖x‖ - 23 * Real.sqrt T ≤ ‖populationGradient U R η x‖ := by
  have hb := (norm_transport_apply_le hU hR x (carmonChainGradient (coordinates U R x))).trans
    (norm_carmonChainGradient_le_23_sqrt _)
  have heq : η • x = populationGradient U R η x -
      transport U R x (carmonChainGradient (coordinates U R x)) := by simp [populationGradient]
  have hn := norm_sub_le (populationGradient U R η x)
    (transport U R x (carmonChainGradient (coordinates U R x)))
  rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hn
  linarith

theorem scale_gt_97_of_small_populationGradient {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d)
    (hg : ‖populationGradient U (liftRadius T) (1/5) x‖ < (1/2 : ℝ)) :
    (97/100 : ℝ) < softProjectionScale (liftRadius T) x := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast Nat.succ_le_of_lt hT
  have hs : 1 ≤ Real.sqrt T := by
    have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ T)
    nlinarith [Real.sqrt_nonneg (T : ℝ)]
  have hn := populationGradient_radial_lower hU (liftRadius_pos hT) (by norm_num : (0 : ℝ) ≤ 1/5) x
  have hx : ‖x‖ < 118 * Real.sqrt T := by nlinarith
  have hsq : ‖x‖ ^ 2 ≤ (118 * Real.sqrt T) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg x) (by positivity)).mpr hx.le
  have hscaled : ‖x‖ ^ 2 / (liftRadius T)^2 ≤ (1/16 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos (liftRadius_pos hT))).mpr
    unfold liftRadius
    nlinarith [sq_nonneg (Real.sqrt (T : ℝ))]
  exact softProjection_scale_gt_97_of_scaled_norm_sq_le (liftRadius_pos hT) x hscaled

theorem lift_radialCoefficient_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d) :
    |radialCoefficient U (liftRadius T) x| ≤ (1/20 : ℝ) := by
  have hR := liftRadius_pos hT
  exact (abs_radialCoefficient_le hU hR x).trans (by
    apply (div_le_iff₀ hR).mpr
    unfold liftRadius
    nlinarith [Real.sqrt_nonneg (T : ℝ)])

/-- Every missing chain coordinate excludes small stationarity at every ambient point. -/
theorem lift_stationarity_barrier {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hT : 0 < T) (x : Point d)
    (hmissing : ∃ i : Fin T, |coordinates U (liftRadius T) x i| < 1) :
    (1/2 : ℝ) ≤ ‖populationGradient U (liftRadius T) (1/5) x‖ := by
  by_contra hnot
  have hg : ‖populationGradient U (liftRadius T) (1/5) x‖ < (1/2 : ℝ) := lt_of_not_ge hnot
  let R := liftRadius T
  let a := softProjectionScale R x
  let y := softProjection R x
  obtain ⟨k, hcurrent, hprev⟩ := exists_carmon_frontier_of_small_coordinate (frameCoordinates U y) hmissing
  have hforce := fderiv_carmonChain_frontier_lt_neg_one hU y k hprev hcurrent
  have ha97 := scale_gt_97_of_small_populationGradient hU hT x hg
  have ha : 0 < a := (softProjection_scale_pos_le_one (liftRadius_pos hT) x).1
  let z := frameCoordinates U y k
  let t := inner ℝ x (U k)
  have hz : z = a * t := by
    change inner ℝ (U k) (a • x) = a * inner ℝ x (U k)
    rw [real_inner_smul_right, real_inner_comm]
  have hzt : z < 1 := (le_abs_self z).trans_lt hcurrent
  have hreg : (1/5 : ℝ) * t < (21/100 : ℝ) := by
    by_cases ht : t ≤ 0
    · nlinarith
    · have htpos : 0 < t := lt_of_not_ge ht
      have hm := mul_lt_mul_of_pos_right ha97 htpos
      change (97/100 : ℝ) * t < a * t at hm
      rw [← hz] at hm
      nlinarith
  have hrad : -radialCoefficient U R x * z ≤ (1/20 : ℝ) := by
    have hab : |radialCoefficient U R x * z| ≤ (1/20 : ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul (lift_radialCoefficient_le hU hT x) hcurrent.le
        (abs_nonneg z) (by norm_num)).trans (by norm_num)
    nlinarith [neg_le_abs (radialCoefficient U R x * z)]
  have hf := mul_lt_mul_of_pos_left hforce ha
  have hy : inner ℝ y (U k) = z := by rw [real_inner_comm]; rfl
  have hdir : fderiv ℝ (potential U R (1/5)) x (U k) < -(7/10 : ℝ) := by
    rw [fderiv_potential_apply U (liftRadius_pos hT) (1/5) x (U k), hy]
    change a * fderiv ℝ (fun y : Point d => carmonChain (frameCoordinates U y)) y (U k) -
      radialCoefficient U R x * z + (1/5 : ℝ) * t < -(7/10 : ℝ)
    nlinarith
  have hb : |fderiv ℝ (potential U R (1/5)) x (U k)| ≤ ‖populationGradient U R (1/5) x‖ := by
    have hn := (fderiv ℝ (potential U R (1/5)) x).le_opNorm (U k)
    have heq : ‖fderiv ℝ (potential U R (1/5)) x‖ = ‖populationGradient U R (1/5) x‖ := by
      dsimp [R]
      rw [populationGradient_eq_gradient U (liftRadius_pos hT) (1/5)]
      simp [gradient]
    simpa only [Real.norm_eq_abs, hU.norm_eq_one k, mul_one, heq] using hn
  nlinarith [neg_le_abs (fderiv ℝ (potential U R (1/5)) x (U k))]

end
end HeavyTailedNoise.RandomizedLift
