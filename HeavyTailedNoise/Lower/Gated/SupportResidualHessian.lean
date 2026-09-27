import HeavyTailedNoise.Lower.Gated.SupportResidualGradientFinal
import HeavyTailedNoise.Analysis.CarmonScalarSecondBound
import HeavyTailedNoise.Analysis.SecondDerivative

/-!
Second-order accounting for the actual ambient Euclidean correction Q.
The exact corrected six-term budget is
1638083391684817 / 400000000000 = 4095.2084792120425 < 4100.
It uses |χ''| ≤ 5.775 / 10^6 and does not round intermediate contributions down.
-/

namespace HeavyTailedNoise

open scoped BigOperators Topology

noncomputable section

theorem second_deriv_carmonChi (s : ℝ) :
    deriv (deriv carmonChi) s = -((1 / 1000 : ℝ) ^ 2 *
      deriv (deriv smoothstep) ((1 / 1000) * s + (-(1 / 16000)))) := by
  have heq : carmonChi = (fun t : ℝ => 1 - smoothstep ((1 / 1000) * t + (-(1 / 16000)))) := by
    funext t
    unfold carmonChi
    congr 2
    ring
  rw [heq, deriv_const_sub', deriv.fun_neg, second_deriv_smoothstep_affine]

theorem abs_second_deriv_carmonChi_le (s : ℝ) :
    |deriv (deriv carmonChi) s| ≤ (231 / 40 : ℝ) / 1000 ^ 2 := by
  rw [second_deriv_carmonChi, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg (1 / 1000 : ℝ))]
  calc
    _ ≤ (1 / 1000 : ℝ) ^ 2 * (231 / 40) :=
      mul_le_mul_of_nonneg_left (abs_second_deriv_smoothstep_le _) (sq_nonneg _)
    _ = _ := by ring

theorem carmonChi_second_deriv_ne_zero_upper {s : ℝ}
    (hs : deriv (deriv carmonChi) s ≠ 0) : s < 1000 + 1 / 16 := by
  by_contra h
  have hu : (1 : ℝ) ≤ (1 / 1000) * s + (-(1 / 16000)) := by linarith
  have hu0 : ¬(1 / 1000 : ℝ) * s + (-(1 / 16000)) ≤ 0 := by linarith
  apply hs
  rw [second_deriv_carmonChi, second_deriv_smoothstep_formula, if_neg hu0, if_pos hu]
  norm_num

theorem norm_fderiv_gatedResidual_le_of_le_upper
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d)
    (hσ : gatedResidual U k y ≤ 1000 + 1 / 16) :
    ‖fderiv ℝ (gatedResidual U k) y‖ ≤ (3169 / 10 : ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3169 / 10)).mp
  calc
    _ ≤ (502 / 5 : ℝ) * gatedResidual U k y := norm_fderiv_gatedResidual_sq_le hU k y
    _ ≤ (502 / 5 : ℝ) * (1000 + 1 / 16) := mul_le_mul_of_nonneg_left hσ (by norm_num)
    _ ≤ _ := by norm_num

theorem norm_second_fderiv_gateFactor_le
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d)
    (hσσ : ‖fderiv ℝ (fderiv ℝ (gatedResidual U k)) y‖ ≤ 41) :
    ‖fderiv ℝ (fderiv ℝ (fun x => 1 - carmonChi (gatedResidual U k x))) y‖ ≤
      ((15 / 8 : ℝ) / 1000) * 41 + ((231 / 40 : ℝ) / 1000 ^ 2) * (3169 / 10) ^ 2 := by
  rw [norm_second_fderiv_const_sub]
  have ht1 : |deriv carmonChi (gatedResidual U k y)| *
      ‖fderiv ℝ (fderiv ℝ (gatedResidual U k)) y‖ ≤ ((15 / 8 : ℝ) / 1000) * 41 := by
    gcongr
    exact abs_deriv_carmonChi_le _
  have ht2 : |deriv (deriv carmonChi) (gatedResidual U k y)| *
      ‖fderiv ℝ (gatedResidual U k) y‖ ^ 2 ≤
        ((231 / 40 : ℝ) / 1000 ^ 2) * (3169 / 10) ^ 2 := by
    by_cases hzero : deriv (deriv carmonChi) (gatedResidual U k y) = 0
    · norm_num [hzero]
    · have hg := norm_fderiv_gatedResidual_le_of_le_upper hU k y
        (carmonChi_second_deriv_ne_zero_upper hzero).le
      gcongr
      exact abs_second_deriv_carmonChi_le _
  exact (norm_second_fderiv_scalar_comp_le contDiff_carmonChi_two
    (contDiff_gatedResidual_two U k) y).trans (add_le_add ht1 ht2)

theorem second_fderiv_gatedCorrection_eq_sum {d T : ℕ} (U : Fin T → Point d) (y : Point d) :
    fderiv ℝ (fderiv ℝ (gatedCorrection U)) y =
      ∑ k : Fin T, fderiv ℝ (fderiv ℝ (gatedCorrectionTerm U k)) y := by
  have heq : fderiv ℝ (gatedCorrection U) =
      (fun x => ∑ k : Fin T, fderiv ℝ (gatedCorrectionTerm U k) x) :=
    funext (fderiv_gatedCorrection_eq_sum U)
  rw [heq]
  exact fderiv_fun_sum fun k _ =>
    ((contDiff_gatedCorrectionTerm_two U k).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) y

theorem second_fderiv_gatedCorrection_eq_active {d T : ℕ} (U : Fin T → Point d) (y : Point d)
    {k : Fin T}
    (hk : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0) :
    fderiv ℝ (fderiv ℝ (gatedCorrection U)) y =
      fderiv ℝ (fderiv ℝ (gatedCorrectionTerm U k)) y := by
  rw [second_fderiv_gatedCorrection_eq_sum]
  apply Finset.sum_eq_single k
  · intro j hj hjk
    apply (gatedCorrectionTerm_zeroTwoJet_of_inactive (U := U) (k := j) (y := y) ?_).second.fderiv
    by_contra hact
    exact hjk (actual_chainGateTerm_unique_active hact hk)
  · simp

/-- Exact corrected arithmetic for the frozen component Hessian estimates. -/
theorem residual_hessian_budget :
    (487 / 100 : ℝ) * (((231 / 40) / 1000 ^ 2) * (3169 / 10) ^ 2 + ((15 / 8) / 1000) * 41) +
      2 * (((15 / 8) / 1000) * (3169 / 10)) * (30 + (487 / 100) * (68 / 5)) +
      264 + 2 * 30 * (68 / 5) + (487 / 100) * 595 ≤ 4100 := by norm_num

theorem norm_second_gatedCorrectionTerm_le_4100_of_component_bounds
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d)
    (hk : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0)
    (hqH : ‖fderiv ℝ (fderiv ℝ (fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
      (frameCoordinates U x) k)) y‖ ≤ 264)
    (hpH : ‖fderiv ℝ (fderiv ℝ (fun x => chainSelector carmonOmegaThree
      (frameCoordinates U x) k)) y‖ ≤ 595)
    (hσH : ‖fderiv ℝ (fderiv ℝ (gatedResidual U k)) y‖ ≤ 41) :
    ‖fderiv ℝ (fderiv ℝ (gatedCorrectionTerm U k)) y‖ ≤ 4100 := by
  let a : Point d → ℝ := fun x => 1 - carmonChi (gatedResidual U k x)
  let q : Point d → ℝ := fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
    (frameCoordinates U x) k
  let p : Point d → ℝ := fun x => chainSelector carmonOmegaThree (frameCoordinates U x) k
  have ha : ContDiff ℝ 2 a :=
    contDiff_const.sub (contDiff_carmonChi_two.comp (contDiff_gatedResidual_two U k))
  have hq : ContDiff ℝ 2 q := (contDiff_chainCorrection 1 k contDiff_carmonPsi_two
    contDiff_carmonPhi_two contDiff_carmonOmega_two).comp (contDiff_frameCoordinates_two U)
  have hp : ContDiff ℝ 2 p := (contDiff_chainSelector k contDiff_carmonOmegaThree_two).comp
    (contDiff_frameCoordinates_two U)
  have hav : ‖a y‖ ≤ 1 := norm_gateFactor_le_one U k y
  have hqv : ‖q y‖ ≤ (487 / 100 : ℝ) := norm_actual_chainCorrection_le _ _
  have hpv : ‖p y‖ ≤ 1 := norm_actual_chainSelector_le_one _ _
  have hdq : ‖fderiv ℝ q y‖ ≤ 30 := (norm_fderiv_chainCorrection_pullback_lt_30 hU k y hk).le
  have hdp : ‖fderiv ℝ p y‖ ≤ (68 / 5 : ℝ) := norm_fderiv_chainSelector_pullback_le hU k y
  have hda : ‖fderiv ℝ a y‖ ≤ ((15 / 8 : ℝ) / 1000) * (3169 / 10) :=
    norm_fderiv_gateFactor_le U k y (fun hχ =>
      norm_fderiv_gatedResidual_le_on_chi_deriv_support hU k y hχ)
  have haH : ‖fderiv ℝ (fderiv ℝ a) y‖ ≤
      ((15 / 8 : ℝ) / 1000) * 41 + ((231 / 40 : ℝ) / 1000 ^ 2) * (3169 / 10) ^ 2 :=
    norm_second_fderiv_gateFactor_le hU k y hσH
  have hqpv : ‖q y * p y‖ ≤ (487 / 100 : ℝ) := by
    rw [norm_mul]
    calc
      _ ≤ (487 / 100 : ℝ) * 1 := by gcongr
      _ = _ := by ring
  have hdqp : ‖fderiv ℝ (fun x => q x * p x) y‖ ≤ (487 / 100 : ℝ) * (68 / 5) + 30 := by
    calc
      _ ≤ ‖q y‖ * ‖fderiv ℝ p y‖ + ‖p y‖ * ‖fderiv ℝ q y‖ :=
        gate_norm_fderiv_mul_le (hq.differentiable (by norm_num) y) (hp.differentiable (by norm_num) y)
      _ ≤ (487 / 100 : ℝ) * (68 / 5) + 1 * 30 := by gcongr
      _ = _ := by ring
  have hqpH : ‖fderiv ℝ (fderiv ℝ (fun x => q x * p x)) y‖ ≤
      (487 / 100 : ℝ) * 595 + 264 + 2 * 30 * (68 / 5) := by
    calc
      _ ≤ ‖q y‖ * ‖fderiv ℝ (fderiv ℝ p) y‖ + ‖p y‖ * ‖fderiv ℝ (fderiv ℝ q) y‖ +
          2 * ‖fderiv ℝ q y‖ * ‖fderiv ℝ p y‖ := norm_second_fderiv_mul_le hq hp y
      _ ≤ (487 / 100 : ℝ) * 595 + 1 * 264 + 2 * 30 * (68 / 5) := by gcongr
      _ = _ := by ring
  have heq : gatedCorrectionTerm U k = (fun x => a x * (q x * p x)) := rfl
  rw [heq]
  calc
    _ ≤ ‖a y‖ * ‖fderiv ℝ (fderiv ℝ (fun x => q x * p x)) y‖ +
        ‖q y * p y‖ * ‖fderiv ℝ (fderiv ℝ a) y‖ +
        2 * ‖fderiv ℝ a y‖ * ‖fderiv ℝ (fun x => q x * p x) y‖ :=
      norm_second_fderiv_mul_le ha (hq.mul hp) y
    _ ≤ 1 * ((487 / 100 : ℝ) * 595 + 264 + 2 * 30 * (68 / 5)) +
        (487 / 100) * (((15 / 8) / 1000) * 41 + ((231 / 40) / 1000 ^ 2) * (3169 / 10) ^ 2) +
        2 * (((15 / 8) / 1000) * (3169 / 10)) * ((487 / 100) * (68 / 5) + 30) := by gcongr
    _ ≤ 4100 := by norm_num

theorem norm_second_gatedCorrection_le_4100_of_component_bounds
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (y : Point d)
    (hH : ∀ k : Fin T, chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0 →
      ‖fderiv ℝ (fderiv ℝ (fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
        (frameCoordinates U x) k)) y‖ ≤ 264 ∧
      ‖fderiv ℝ (fderiv ℝ (fun x => chainSelector carmonOmegaThree
        (frameCoordinates U x) k)) y‖ ≤ 595 ∧
      ‖fderiv ℝ (fderiv ℝ (gatedResidual U k)) y‖ ≤ 41) :
    ‖fderiv ℝ (fderiv ℝ (gatedCorrection U)) y‖ ≤ 4100 := by
  by_cases ha : ∃ k : Fin T, chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0
  · obtain ⟨k, hk⟩ := ha
    rw [second_fderiv_gatedCorrection_eq_active U y hk]
    obtain ⟨hqH, hpH, hσH⟩ := hH k hk
    exact norm_second_gatedCorrectionTerm_le_4100_of_component_bounds hU k y hk hqH hpH hσH
  · have hzero : ∀ k : Fin T, chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
        (frameCoordinates U y) k = 0 := by simpa using ha
    rw [second_fderiv_gatedCorrection_eq_sum]
    have heq : (∑ k : Fin T, fderiv ℝ (fderiv ℝ (gatedCorrectionTerm U k)) y) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact (gatedCorrectionTerm_zeroTwoJet_of_inactive (hzero k)).second.fderiv
    rw [heq, ContinuousLinearMap.opNorm_zero]
    norm_num

theorem abs_second_deriv_carmonOmega_le (t : ℝ) :
    |deriv (deriv carmonOmega) t| ≤ (411 / 10 : ℝ) := by
  have h := abs_second_deriv_stepWindow_le (a := (1 / 8 : ℝ)) (w := (3 / 8 : ℝ))
    (by norm_num) (by norm_num) t
  norm_num at h
  exact h.trans (by norm_num)

def frontierPrevPrevCoefficient (a b : ℝ) : ℝ :=
  (deriv (deriv carmonPsi) a * (carmonPhi b - carmonPhi 0 + 1) +
    deriv (deriv carmonPsi) (-a) * (carmonPhi 0 - carmonPhi (-b) + 1)) * (1 - carmonOmega b)

def frontierPrevCurrentCoefficient (a b : ℝ) : ℝ :=
  (deriv carmonPsi a * deriv carmonPhi b - deriv carmonPsi (-a) * deriv carmonPhi (-b)) *
      (1 - carmonOmega b) -
    (deriv carmonPsi a * (carmonPhi b - carmonPhi 0 + 1) -
      deriv carmonPsi (-a) * (carmonPhi 0 - carmonPhi (-b) + 1)) * deriv carmonOmega b

def frontierCurrentCurrentCoefficient (a b : ℝ) : ℝ :=
  (carmonPsi a * deriv (deriv carmonPhi) b - carmonPsi (-a) * deriv (deriv carmonPhi) (-b)) *
      (1 - carmonOmega b) -
    2 * (carmonPsi a * deriv carmonPhi b + carmonPsi (-a) * deriv carmonPhi (-b)) * deriv carmonOmega b -
    (carmonPsi a * (carmonPhi b - carmonPhi 0 + 1) +
      carmonPsi (-a) * (carmonPhi 0 - carmonPhi (-b) + 1)) * deriv (deriv carmonOmega) b

theorem abs_frontierPrevPrevCoefficient_le {a b : ℝ}
    (ha : (1 / 2 : ℝ) < |a|) (hb : |b| < 1 / 2) :
    |frontierPrevPrevCoefficient a b| ≤ (583 / 10 : ℝ) := by
  obtain ⟨hA, hB⟩ := correction_bracket_abs_bounds hb
  have hc := abs_one_sub_carmonOmega_le b
  have hψ (t : ℝ) : |deriv (deriv carmonPsi) t| ≤ (65 / 2 : ℝ) :=
    (abs_second_deriv_carmonPsi_lt_32_5 t).le
  rcases lt_abs.mp ha with ha | ha
  · have hz : deriv (deriv carmonPsi) (-a) = 0 := second_deriv_carmonPsi_zero_of_le (by linarith)
    simp only [frontierPrevPrevCoefficient, hz, zero_mul, add_zero, abs_mul]
    calc
      _ ≤ (65 / 2 : ℝ) * (224 / 125) * 1 := by gcongr; exact hψ a
      _ ≤ 583 / 10 := by norm_num
  · have hz : deriv (deriv carmonPsi) a = 0 := second_deriv_carmonPsi_zero_of_le (by linarith)
    simp only [frontierPrevPrevCoefficient, hz, zero_mul, zero_add, abs_mul]
    calc
      _ ≤ (65 / 2 : ℝ) * (224 / 125) * 1 := by gcongr; exact hψ (-a)
      _ ≤ 583 / 10 := by norm_num

private theorem mixed_coefficient_numeric_bound {c A d v w : ℝ}
    (hc : |c| ≤ (223 / 50 : ℝ)) (hA : |A| ≤ (224 / 125 : ℝ))
    (hd : |d| ≤ (33 / 20 : ℝ)) (hv : |v| ≤ 1) (hw : |w| ≤ 5) :
    |c * d * v - c * A * w| ≤ (237 / 5 : ℝ) := by
  calc
    _ ≤ |c * d * v| + |c * A * w| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (c * d * v) (c * A * w)
    _ = |c| * |d| * |v| + |c| * |A| * |w| := by simp only [abs_mul]
    _ ≤ (223 / 50 : ℝ) * (33 / 20) * 1 + (223 / 50) * (224 / 125) * 5 := by gcongr
    _ ≤ 237 / 5 := by norm_num

theorem abs_frontierPrevCurrentCoefficient_le {a b : ℝ}
    (ha : (1 / 2 : ℝ) < |a|) (hb : |b| < 1 / 2) :
    |frontierPrevCurrentCoefficient a b| ≤ (237 / 5 : ℝ) := by
  obtain ⟨hA, hB⟩ := correction_bracket_abs_bounds hb
  have hc := abs_one_sub_carmonOmega_le b
  have hψ (t : ℝ) : |deriv carmonPsi t| ≤ (223 / 50 : ℝ) := by
    rw [abs_of_nonneg (deriv_carmonPsi_nonneg t)]
    exact (deriv_carmonPsi_lt_446 t).le
  rcases lt_abs.mp ha with ha | ha
  · have hz : deriv carmonPsi (-a) = 0 := deriv_carmonPsi_zero_of_le (by linarith)
    simp only [frontierPrevCurrentCoefficient, hz, zero_mul, sub_zero]
    exact mixed_coefficient_numeric_bound (hψ a) hA (abs_deriv_carmonPhi_le b) hc
      (abs_deriv_carmonOmega_le b)
  · have hz : deriv carmonPsi a = 0 := deriv_carmonPsi_zero_of_le (by linarith)
    have heq : frontierPrevCurrentCoefficient a b =
        -(deriv carmonPsi (-a) * deriv carmonPhi (-b) * (1 - carmonOmega b) -
          deriv carmonPsi (-a) * (carmonPhi 0 - carmonPhi (-b) + 1) * deriv carmonOmega b) := by
      unfold frontierPrevCurrentCoefficient
      rw [hz]
      ring
    rw [heq, abs_neg]
    exact mixed_coefficient_numeric_bound (hψ (-a)) hB (abs_deriv_carmonPhi_le (-b)) hc
      (abs_deriv_carmonOmega_le b)

private theorem current_second_coefficient_numeric_bound {c A d₁ d₂ v w₁ w₂ : ℝ}
    (hc : |c| ≤ Real.exp 1) (hA : |A| ≤ (224 / 125 : ℝ))
    (hd₁ : |d₁| ≤ (33 / 20 : ℝ)) (hd₂ : |d₂| ≤ 1) (hv : |v| ≤ 1)
    (hw₁ : |w₁| ≤ 5) (hw₂ : |w₂| ≤ (411 / 10 : ℝ)) :
    |c * d₂ * v - 2 * c * d₁ * w₁ - c * A * w₂| ≤ 248 := by
  calc
    _ ≤ |c * d₂ * v - 2 * c * d₁ * w₁| + |c * A * w₂| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (c * d₂ * v - 2 * c * d₁ * w₁) (c * A * w₂)
    _ ≤ (|c * d₂ * v| + |2 * c * d₁ * w₁|) + |c * A * w₂| := by
      apply add_le_add _ le_rfl
      simpa only [Real.norm_eq_abs] using norm_sub_le (c * d₂ * v) (2 * c * d₁ * w₁)
    _ = |c| * |d₂| * |v| + 2 * |c| * |d₁| * |w₁| + |c| * |A| * |w₂| := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ Real.exp 1 * 1 * 1 + 2 * Real.exp 1 * (33 / 20) * 5 +
        Real.exp 1 * (224 / 125) * (411 / 10) := by gcongr
    _ ≤ (2.7182818286 : ℝ) * 1 * 1 + 2 * (2.7182818286 : ℝ) * (33 / 20) * 5 +
        (2.7182818286 : ℝ) * (224 / 125) * (411 / 10) := by gcongr <;> exact Real.exp_one_lt_d9.le
    _ ≤ 248 := by norm_num

theorem abs_frontierCurrentCurrentCoefficient_le {a b : ℝ}
    (ha : (1 / 2 : ℝ) < |a|) (hb : |b| < 1 / 2) :
    |frontierCurrentCurrentCoefficient a b| ≤ 248 := by
  obtain ⟨hA, hB⟩ := correction_bracket_abs_bounds hb
  have hc := abs_one_sub_carmonOmega_le b
  have hψ (t : ℝ) : |carmonPsi t| ≤ Real.exp 1 := by
    rw [abs_of_nonneg (carmonPsi_nonneg t)]
    exact carmonPsi_le_exp_one t
  rcases lt_abs.mp ha with ha | ha
  · have hz : carmonPsi (-a) = 0 := carmonPsi_zero_of_le (by linarith)
    have heq : frontierCurrentCurrentCoefficient a b =
        carmonPsi a * deriv (deriv carmonPhi) b * (1 - carmonOmega b) -
          2 * carmonPsi a * deriv carmonPhi b * deriv carmonOmega b -
          carmonPsi a * (carmonPhi b - carmonPhi 0 + 1) * deriv (deriv carmonOmega) b := by
      unfold frontierCurrentCurrentCoefficient
      rw [hz]
      ring
    rw [heq]
    exact current_second_coefficient_numeric_bound (hψ a) hA (abs_deriv_carmonPhi_le b)
      (abs_second_deriv_carmonPhi_le_one b) hc (abs_deriv_carmonOmega_le b)
      (abs_second_deriv_carmonOmega_le b)
  · have hz : carmonPsi a = 0 := carmonPsi_zero_of_le (by linarith)
    have heq : frontierCurrentCurrentCoefficient a b =
        carmonPsi (-a) * (-deriv (deriv carmonPhi) (-b)) * (1 - carmonOmega b) -
          2 * carmonPsi (-a) * deriv carmonPhi (-b) * deriv carmonOmega b -
          carmonPsi (-a) * (carmonPhi 0 - carmonPhi (-b) + 1) * deriv (deriv carmonOmega) b := by
      unfold frontierCurrentCurrentCoefficient
      rw [hz]
      ring
    rw [heq]
    exact current_second_coefficient_numeric_bound (hψ (-a)) hB (abs_deriv_carmonPhi_le (-b))
      (by simpa only [abs_neg] using abs_second_deriv_carmonPhi_le_one (-b)) hc
      (abs_deriv_carmonOmega_le b) (abs_second_deriv_carmonOmega_le b)

theorem hasFDerivAt_frontierPrevCoefficient_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {a' b' : E →L[ℝ] ℝ} {x : E}
    (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (fun y => frontierPrevCoefficient (a y) (b y))
      (frontierPrevPrevCoefficient (a x) (b x) • a' +
        frontierPrevCurrentCoefficient (a x) (b x) • b') x := by
  have hψa := (contDiff_carmonPsi_two.differentiable_deriv_two (a x)).hasDerivAt.comp_hasFDerivAt x ha
  have hψn := (contDiff_carmonPsi_two.differentiable_deriv_two (-a x)).hasDerivAt.comp_hasFDerivAt x ha.fun_neg
  have hφb := (differentiable_carmonPhi (b x)).hasDerivAt.comp_hasFDerivAt x hb
  have hφn := (differentiable_carmonPhi (-b x)).hasDerivAt.comp_hasFDerivAt x hb.fun_neg
  have hω := (contDiff_carmonOmega_two.differentiable (by norm_num) (b x)).hasDerivAt.comp_hasFDerivAt x hb
  have h := ((hψa.fun_mul ((hφb.sub_const (carmonPhi 0)).add_const 1)).fun_sub
    (hψn.fun_mul ((hφn.const_sub (carmonPhi 0)).add_const 1))).fun_mul (hω.const_sub 1)
  convert! h using 1 <;> ext v <;>
    simp only [frontierPrevCoefficient, frontierPrevPrevCoefficient, frontierPrevCurrentCoefficient,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, Function.comp_apply, Pi.neg_apply, smul_eq_mul] <;> ring

theorem hasFDerivAt_frontierCurrentCoefficient_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℝ} {a' b' : E →L[ℝ] ℝ} {x : E}
    (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (fun y => frontierCurrentCoefficient (a y) (b y))
      (frontierPrevCurrentCoefficient (a x) (b x) • a' +
        frontierCurrentCurrentCoefficient (a x) (b x) • b') x := by
  have hψa := (contDiff_carmonPsi_two.differentiable (by norm_num) (a x)).hasDerivAt.comp_hasFDerivAt x ha
  have hψn := (contDiff_carmonPsi_two.differentiable (by norm_num) (-a x)).hasDerivAt.comp_hasFDerivAt x ha.fun_neg
  have hφb := (differentiable_carmonPhi (b x)).hasDerivAt.comp_hasFDerivAt x hb
  have hφn := (differentiable_carmonPhi (-b x)).hasDerivAt.comp_hasFDerivAt x hb.fun_neg
  have hdφb := (contDiff_carmonPhi_two.differentiable_deriv_two (b x)).hasDerivAt.comp_hasFDerivAt x hb
  have hdφn := (contDiff_carmonPhi_two.differentiable_deriv_two (-b x)).hasDerivAt.comp_hasFDerivAt x hb.fun_neg
  have hω := (contDiff_carmonOmega_two.differentiable (by norm_num) (b x)).hasDerivAt.comp_hasFDerivAt x hb
  have hdω := (contDiff_carmonOmega_two.differentiable_deriv_two (b x)).hasDerivAt.comp_hasFDerivAt x hb
  have hfirst := ((hψa.fun_mul hdφb).fun_add (hψn.fun_mul hdφn)).fun_mul (hω.const_sub 1)
  have hsecond := ((hψa.fun_mul ((hφb.sub_const (carmonPhi 0)).add_const 1)).fun_add
    (hψn.fun_mul ((hφn.const_sub (carmonPhi 0)).add_const 1))).fun_mul hdω
  have h := hfirst.fun_sub hsecond
  convert! h using 1 <;> ext v <;>
    simp only [frontierCurrentCoefficient, frontierPrevCurrentCoefficient, frontierCurrentCurrentCoefficient,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, Function.comp_apply, Pi.neg_apply, smul_eq_mul] <;> ring

def frontierSecondMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a' b' : E →L[ℝ] ℝ) (a b : ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (frontierPrevPrevCoefficient a b • a' + frontierPrevCurrentCoefficient a b • b').smulRight a' +
  (frontierPrevCurrentCoefficient a b • a' + frontierCurrentCurrentCoefficient a b • b').smulRight b'

theorem hasFDerivAt_fderiv_chainCorrection_pullback {d T : ℕ}
    (U : Fin T → Point d) (k : Fin T) (y : Point d) :
    HasFDerivAt (fderiv ℝ (fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
      (frameCoordinates U x) k))
      (frontierSecondMap (innerSL ℝ (chainPredecessorVector U k)) (innerSL ℝ (U k))
        (chainPredecessor (frameCoordinates U y) k) (frameCoordinates U y k)) y := by
  have heq : fderiv ℝ (fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
      (frameCoordinates U x) k) = (fun x =>
      frontierPrevCoefficient (chainPredecessor (frameCoordinates U x) k) (frameCoordinates U x k) •
          innerSL ℝ (chainPredecessorVector U k) +
      frontierCurrentCoefficient (chainPredecessor (frameCoordinates U x) k) (frameCoordinates U x k) •
          innerSL ℝ (U k)) := by
    funext x
    exact (hasFDerivAt_frontierCorrection_comp (hasFDerivAt_chainPredecessor_pullback U k x)
      (innerSL ℝ (U k)).hasFDerivAt).fderiv
  rw [heq]
  exact ((hasFDerivAt_frontierPrevCoefficient_comp (hasFDerivAt_chainPredecessor_pullback U k y)
    (innerSL ℝ (U k)).hasFDerivAt).smul_const (innerSL ℝ (chainPredecessorVector U k))).fun_add
    ((hasFDerivAt_frontierCurrentCoefficient_comp (hasFDerivAt_chainPredecessor_pullback U k y)
      (innerSL ℝ (U k)).hasFDerivAt).smul_const (innerSL ℝ (U k)))

theorem chainPredecessorVector_bessel_pair {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (x : Point d) :
    (inner ℝ (chainPredecessorVector U k) x) ^ 2 + (inner ℝ (U k) x) ^ 2 ≤ ‖x‖ ^ 2 := by
  by_cases hk : k.val = 0
  · have h := hU.sum_inner_products_le (s := {k}) x
    simpa [chainPredecessorVector, hk, Real.norm_eq_abs, sq_abs] using h
  · let j : Fin T := ⟨k.val - 1, by omega⟩
    have hjk : j ≠ k := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [j] at hv
      omega
    have hpred : chainPredecessorVector U k = U j := by simp [chainPredecessorVector, hk, j]
    rw [hpred]
    have h := hU.sum_inner_products_le (s := {j, k}) x
    simpa [hjk, Real.norm_eq_abs, sq_abs] using h

theorem norm_orthogonal_pair_sq_le {d : ℕ} {u v : Point d} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (huv : inner ℝ u v = 0) (a b : ℝ) : ‖a • u + b • v‖ ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have hau : ‖a • u‖ ≤ |a| := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_left hu (abs_nonneg a)
  have hbv : ‖b • v‖ ≤ |b| := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_left hv (abs_nonneg b)
  have hasq := (sq_le_sq₀ (norm_nonneg (a • u)) (abs_nonneg a)).mpr hau
  have hbsq := (sq_le_sq₀ (norm_nonneg (b • v)) (abs_nonneg b)).mpr hbv
  rw [sq_abs] at hasq hbsq
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, huv]
  nlinarith

theorem symmetric_pair_matrix_sq_bound (A B C r s : ℝ) :
    (A * r + B * s) ^ 2 + (B * r + C * s) ^ 2 ≤
      (A ^ 2 + 2 * B ^ 2 + C ^ 2) * (r ^ 2 + s ^ 2) := by
  nlinarith [sq_nonneg (B * r - A * s), sq_nonneg (C * r - B * s)]

theorem norm_frontierSecondMap_le_264 {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) {a b : ℝ}
    (ha : (1 / 2 : ℝ) < |a|) (hb : |b| < 1 / 2) :
    ‖frontierSecondMap (innerSL ℝ (chainPredecessorVector U k)) (innerSL ℝ (U k)) a b‖ ≤ 264 := by
  let A := frontierPrevPrevCoefficient a b
  let B := frontierPrevCurrentCoefficient a b
  let C := frontierCurrentCurrentCoefficient a b
  have hA : |A| ≤ (583 / 10 : ℝ) := abs_frontierPrevPrevCoefficient_le ha hb
  have hB : |B| ≤ (237 / 5 : ℝ) := abs_frontierPrevCurrentCoefficient_le ha hb
  have hC : |C| ≤ 248 := abs_frontierCurrentCurrentCoefficient_le ha hb
  have hF : A ^ 2 + 2 * B ^ 2 + C ^ 2 ≤ (264 : ℝ) ^ 2 := by
    have hAsq := (sq_le_sq₀ (abs_nonneg A) (by norm_num : (0 : ℝ) ≤ 583 / 10)).mpr hA
    have hBsq := (sq_le_sq₀ (abs_nonneg B) (by norm_num : (0 : ℝ) ≤ 237 / 5)).mpr hB
    have hCsq := (sq_le_sq₀ (abs_nonneg C) (by norm_num : (0 : ℝ) ≤ 248)).mpr hC
    rw [sq_abs] at hAsq hBsq hCsq
    nlinarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  let r := inner ℝ (chainPredecessorVector U k) x
  let s := inner ℝ (U k) x
  have hpoint : frontierSecondMap (innerSL ℝ (chainPredecessorVector U k)) (innerSL ℝ (U k)) a b x =
      innerSL ℝ ((A * r + B * s) • chainPredecessorVector U k + (B * r + C * s) • U k) := by
    ext v
    simp only [frontierSecondMap, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_add_left, real_inner_smul_left,
      smul_eq_mul]
    rfl
  rw [hpoint, innerSL_apply_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (264 : ℝ) * ‖x‖)).mp
  calc
    _ ≤ (A * r + B * s) ^ 2 + (B * r + C * s) ^ 2 :=
      norm_orthogonal_pair_sq_le (chainPredecessorVector_norm_le hU k) (hU.norm_eq_one k).le
        (chainPredecessorVector_orthogonal hU k) _ _
    _ ≤ (A ^ 2 + 2 * B ^ 2 + C ^ 2) * (r ^ 2 + s ^ 2) := symmetric_pair_matrix_sq_bound A B C r s
    _ ≤ (264 : ℝ) ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul hF (chainPredecessorVector_bessel_pair hU k x) (by positivity) (by norm_num)
    _ = ((264 : ℝ) * ‖x‖) ^ 2 := by ring

theorem norm_second_fderiv_chainCorrection_pullback_le_264
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d)
    (hk : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0) :
    ‖fderiv ℝ (fderiv ℝ (fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
      (frameCoordinates U x) k)) y‖ ≤ 264 := by
  rw [(hasFDerivAt_fderiv_chainCorrection_pullback U k y).fderiv]
  obtain ⟨ha, hb, _⟩ := chainGateTerm_support (fun _ ht => carmonPsi_zero_of_le ht)
    (fun _ ht => carmonOmega_one ht) (fun _ ht => carmonOmegaThree_one ht) hk
  exact norm_frontierSecondMap_le_264 hU k ha hb

theorem abs_coordinate_mul_deriv_carmonOmegaSix_le (t : ℝ) :
    |t * deriv carmonOmegaSix t| ≤ (15 / 4 : ℝ) := by
  by_cases ht : |t| ≤ 1 / 8
  · have hd := abs_deriv_stepWindow_le (a := (1 / 16 : ℝ)) (w := (1 / 16 : ℝ))
      (by norm_num) (by norm_num) t
    norm_num at hd
    have hd6 : |deriv carmonOmegaSix t| ≤ 30 := hd
    rw [abs_mul]
    calc
      _ ≤ (1 / 8 : ℝ) * 30 := by gcongr
      _ = _ := by norm_num
  · norm_num [deriv_carmonOmegaSix_eq_zero_of_abs_ge (lt_of_not_ge ht).le]

theorem abs_coordinate_sq_mul_second_deriv_carmonOmegaSix_le (t : ℝ) :
    |t ^ 2 * deriv (deriv carmonOmegaSix) t| ≤ (231 / 10 : ℝ) := by
  by_cases ht : |t| ≤ 1 / 8
  · have hd := abs_second_deriv_carmonOmegaSix_le t
    rw [abs_mul, abs_pow]
    calc
      _ ≤ (1 / 8 : ℝ) ^ 2 * (7392 / 5) := by gcongr
      _ = _ := by norm_num
  · have hopen : IsOpen {u : ℝ | (1 / 8 : ℝ) < |u|} :=
      isOpen_lt continuous_const continuous_abs
    have hlocal : carmonOmegaSix =ᶠ[𝓝 t] (fun _ : ℝ => 1) := by
      filter_upwards [hopen.mem_nhds (lt_of_not_ge ht)] with u hu
      exact carmonOmegaSix_one hu.le
    have hz : deriv (deriv carmonOmegaSix) t = 0 := by simpa using hlocal.deriv.deriv_eq
    norm_num [hz]

theorem hasDerivAt_residualCoordinateGradient (t : ℝ) :
    HasDerivAt residualCoordinateGradient
      (2 * (1 - carmonOmegaSix t) - 4 * t * deriv carmonOmegaSix t -
        t ^ 2 * deriv (deriv carmonOmegaSix) t) t := by
  have hω := (contDiff_carmonOmegaSix_two.differentiable (by norm_num) t).hasDerivAt
  have hdω := (contDiff_carmonOmegaSix_two.differentiable_deriv_two t).hasDerivAt
  have h := (((hω.const_sub 1).mul (hasDerivAt_id t)).const_mul 2).sub
    (hdω.mul ((hasDerivAt_id t).pow 2))
  convert! h using 1
  · funext u
    simp only [residualCoordinateGradient, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · norm_num [Pi.pow_apply, id_eq] <;> ring

theorem abs_deriv_residualCoordinateGradient_le (t : ℝ) :
    |deriv residualCoordinateGradient t| ≤ (401 / 10 : ℝ) := by
  rw [(hasDerivAt_residualCoordinateGradient t).deriv]
  have hx := abs_le.mp (abs_coordinate_mul_deriv_carmonOmegaSix_le t)
  have hxx := abs_le.mp (abs_coordinate_sq_mul_second_deriv_carmonOmegaSix_le t)
  have h0 := carmonOmegaSix_nonneg t
  have h1 := carmonOmegaSix_le_one t
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The real-linear view of Mathlib's sesquilinear inner-product map. -/
def realInnerLinearMap (d : ℕ) : Point d →L[ℝ] Point d →L[ℝ] ℝ where
  toFun := fun x => innerSL ℝ x
  map_add' := by
    intro x y
    ext v
    simp only [innerSL_apply_apply, inner_add_left, ContinuousLinearMap.add_apply]
  map_smul' := by
    intro a x
    ext v
    simp only [innerSL_apply_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply,
      RingHom.id_apply, smul_eq_mul]
  cont := (innerSL ℝ (E := Point d)).continuous

@[simp] theorem realInnerLinearMap_apply (d : ℕ) (x : Point d) :
    realInnerLinearMap d x = innerSL ℝ x := rfl

/-- Curried bilinear map for a scalar multiple of the full frame-complement
projection plus a diagonal block in selected frame coordinates. -/
def frameBlockSecondMap {d T : ℕ} (U : Fin T → Point d) (s : Finset (Fin T))
    (a : ℝ) (c : Fin T → ℝ) : Point d →L[ℝ] Point d →L[ℝ] ℝ :=
  a • realInnerLinearMap d -
    (∑ i : Fin T, (a • innerSL ℝ (U i)).smulRight (innerSL ℝ (U i))) +
    ∑ i ∈ s, (c i • innerSL ℝ (U i)).smulRight (innerSL ℝ (U i))

theorem frameBlockSecondMap_apply {d T : ℕ} (U : Fin T → Point d) (s : Finset (Fin T))
    (a : ℝ) (c : Fin T → ℝ) (x : Point d) :
    frameBlockSecondMap U s a c x = innerSL ℝ
      (a • frameOrthogonalResidual U Finset.univ x +
        ∑ i ∈ s, (c i * frameCoordinates U x i) • U i) := by
  ext v
  simp only [frameBlockSecondMap, frameOrthogonalResidual, frameCoordinates,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, FunLike.coe_sum, Finset.sum_apply,
    realInnerLinearMap_apply, innerSL_apply_apply, inner_add_left, real_inner_smul_left, inner_sub_left, sum_inner,
    smul_eq_mul, mul_sub, Finset.mul_sum, mul_assoc]

theorem norm_frameBlockSecondMap_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (a : ℝ) (c : Fin T → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (ha : |a| ≤ M) (hc : ∀ i ∈ s, |c i| ≤ M) :
    ‖frameBlockSecondMap U s a c‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  rw [frameBlockSecondMap_apply, innerSL_apply_norm]
  have hnorm : ‖∑ i ∈ s, (c i * frameCoordinates U x i) • U i‖ ^ 2 =
      ∑ i ∈ s, (c i * frameCoordinates U x i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa [pow_two] using hU.inner_sum (fun i => c i * frameCoordinates U x i)
      (fun i => c i * frameCoordinates U x i) s
  have horth : inner ℝ (a • frameOrthogonalResidual U Finset.univ x)
      (∑ i ∈ s, (c i * frameCoordinates U x i) • U i) = 0 := by
    rw [real_inner_smul_left, inner_sum]
    simp only [inner_smul_right, full_frameResidual_orthogonal hU, mul_zero, Finset.sum_const_zero]
  have hAsq : a ^ 2 ≤ M ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg a) hM).mpr ha
    simpa only [sq_abs] using h
  have hsum : (∑ i ∈ s, (c i * frameCoordinates U x i) ^ 2) ≤
      M ^ 2 * ∑ i ∈ s, (frameCoordinates U x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hci : (c i) ^ 2 ≤ M ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (c i)) hM).mpr (hc i hi)
      simpa only [sq_abs] using h
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right hci (sq_nonneg (frameCoordinates U x i))
  have hsubset : (∑ i ∈ s, (frameCoordinates U x i) ^ 2) ≤
      ∑ i : Fin T, (frameCoordinates U x i) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => sq_nonneg _)
  have henergy : ‖frameOrthogonalResidual U Finset.univ x‖ ^ 2 +
      (∑ i ∈ s, (frameCoordinates U x i) ^ 2) ≤ ‖x‖ ^ 2 := by
    rw [frameOrthogonalResidual_norm_sq hU]
    linarith
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg x))).mp
  rw [norm_add_sq_real, horth, hnorm, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  calc
    _ ≤ M ^ 2 * ‖frameOrthogonalResidual U Finset.univ x‖ ^ 2 +
        M ^ 2 * ∑ i ∈ s, (frameCoordinates U x i) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hAsq (sq_nonneg ‖frameOrthogonalResidual U Finset.univ x‖)
      linarith
    _ = M ^ 2 * (‖frameOrthogonalResidual U Finset.univ x‖ ^ 2 +
        ∑ i ∈ s, (frameCoordinates U x i) ^ 2) := by ring
    _ ≤ M ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left henergy (sq_nonneg M)
    _ = (M * ‖x‖) ^ 2 := by ring

theorem hasFDerivAt_fderiv_gatedResidual {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    HasFDerivAt (fderiv ℝ (gatedResidual U k))
      (frameBlockSecondMap U (Finset.univ.filter (k < ·)) 2
        (fun i => deriv residualCoordinateGradient (frameCoordinates U y i))) y := by
  have heq : fderiv ℝ (gatedResidual U k) = (fun x =>
      (2 : ℝ) • innerSL ℝ x -
      (∑ i : Fin T, (2 * frameCoordinates U x i) • innerSL ℝ (U i)) +
      ∑ i ∈ Finset.univ.filter (k < ·),
        residualCoordinateGradient (frameCoordinates U x i) • innerSL ℝ (U i)) := by
    funext x
    rw [(hasFDerivAt_gatedResidual hU k x).fderiv]
    ext v
    simp only [residualGradientVector, frameOrthogonalResidual, frameCoordinates,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      FunLike.coe_sum, Finset.sum_apply, innerSL_apply_apply, inner_add_left, real_inner_smul_left,
      inner_sub_left, sum_inner, smul_eq_mul, mul_sub, Finset.mul_sum, mul_assoc]
  rw [heq]
  have hI : HasFDerivAt (fun x : Point d => innerSL ℝ x) (realInnerLinearMap d) y :=
    (realInnerLinearMap d).hasFDerivAt
  have hp (i : Fin T) : HasFDerivAt
      (fun x => (2 * frameCoordinates U x i) • innerSL ℝ (U i))
      (((2 : ℝ) • innerSL ℝ (U i)).smulRight (innerSL ℝ (U i))) y := by
    have h := ((innerSL ℝ (U i)).hasFDerivAt (x := y)).const_smul (2 : ℝ)
    convert! h.smul_const (innerSL ℝ (U i)) using 1 <;> ext v w <;>
      simp only [frameCoordinates, Pi.smul_apply, innerSL_apply_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring
  have ht (i : Fin T) : HasFDerivAt
      (fun x => residualCoordinateGradient (frameCoordinates U x i) • innerSL ℝ (U i))
      ((deriv residualCoordinateGradient (frameCoordinates U y i) • innerSL ℝ (U i)).smulRight
        (innerSL ℝ (U i))) y :=
    (((hasDerivAt_residualCoordinateGradient (frameCoordinates U y i)).differentiableAt.hasDerivAt).comp_hasFDerivAt
      y (innerSL ℝ (U i)).hasFDerivAt).smul_const (innerSL ℝ (U i))
  have h := ((hI.const_smul (2 : ℝ)).fun_sub (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hp i))).fun_add
    (HasFDerivAt.fun_sum (u := Finset.univ.filter (k < ·)) (fun i _ => ht i))
  convert! h using 1 <;> simp only [frameBlockSecondMap, Pi.smul_apply]

theorem norm_second_fderiv_gatedResidual_le_41 {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    ‖fderiv ℝ (fderiv ℝ (gatedResidual U k)) y‖ ≤ 41 := by
  rw [(hasFDerivAt_fderiv_gatedResidual hU k y).fderiv]
  apply norm_frameBlockSecondMap_le hU _ _ _ (by norm_num) (by norm_num)
  intro i hi
  exact (abs_deriv_residualCoordinateGradient_le (frameCoordinates U y i)).trans (by norm_num)

theorem hasFDerivAt_fderiv_finsetProd
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι]
    (s : Finset ι) (f : ι → E → ℝ) (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : E) :
    HasFDerivAt (fderiv ℝ (fun y => ∏ i ∈ s, f i y))
      (s.sum (fun i : ι => (∏ j ∈ s.erase i, f j x) • fderiv ℝ (fderiv ℝ (f i)) x +
        (∑ j ∈ s.erase i, (∏ l ∈ (s.erase i).erase j, f l x) • fderiv ℝ (f j) x).smulRight
          (fderiv ℝ (f i) x))) x := by
  have heq : fderiv ℝ (fun y => ∏ i ∈ s, f i y) =
      (fun y => ∑ i ∈ s, (∏ j ∈ s.erase i, f j y) • fderiv ℝ (f i) y) := by
    funext y
    exact fderiv_finsetProd (fun i hi => (hf i hi).differentiable (by norm_num) y)
  rw [heq]
  apply HasFDerivAt.fun_sum
  intro i hi
  have hp := HasFDerivAt.finsetProd (u := s.erase i) (fun j hj =>
    ((hf j (Finset.mem_of_mem_erase hj)).differentiable (by norm_num) x).hasFDerivAt)
  have hfi := (((hf i hi).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  exact hp.fun_smul hfi

theorem fderiv_selectorFactor {d T : ℕ} (U : Fin T → Point d) (i : Fin T) (y : Point d) :
    fderiv ℝ (fun x => 1 - carmonOmegaThree (frameCoordinates U x i)) y =
      -(deriv carmonOmegaThree (frameCoordinates U y i) • innerSL ℝ (U i)) := by
  exact ((((contDiff_carmonOmegaThree_two.differentiable (by norm_num)
    (frameCoordinates U y i)).hasDerivAt).comp_hasFDerivAt y
      (innerSL ℝ (U i)).hasFDerivAt).const_sub 1).fderiv

theorem hasFDerivAt_fderiv_selectorFactor {d T : ℕ}
    (U : Fin T → Point d) (i : Fin T) (y : Point d) :
    HasFDerivAt (fderiv ℝ (fun x => 1 - carmonOmegaThree (frameCoordinates U x i)))
      ((-deriv (deriv carmonOmegaThree) (frameCoordinates U y i) • innerSL ℝ (U i)).smulRight
        (innerSL ℝ (U i))) y := by
  have heq : fderiv ℝ (fun x => 1 - carmonOmegaThree (frameCoordinates U x i)) =
      (fun x => -(deriv carmonOmegaThree (frameCoordinates U x i) • innerSL ℝ (U i))) :=
    funext (fderiv_selectorFactor U i)
  rw [heq]
  have h := ((contDiff_carmonOmegaThree_two.differentiable_deriv_two
    (frameCoordinates U y i)).hasDerivAt.comp_hasFDerivAt y (innerSL ℝ (U i)).hasFDerivAt).smul_const
      (innerSL ℝ (U i))
  convert! h.fun_neg using 1 <;> ext u v <;>
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul] <;> ring

theorem second_fderiv_selectorFactor {d T : ℕ}
    (U : Fin T → Point d) (i : Fin T) (y : Point d) :
    fderiv ℝ (fderiv ℝ (fun x => 1 - carmonOmegaThree (frameCoordinates U x i))) y =
      (-deriv (deriv carmonOmegaThree) (frameCoordinates U y i) • innerSL ℝ (U i)).smulRight
        (innerSL ℝ (U i)) := (hasFDerivAt_fderiv_selectorFactor U i y).fderiv

def selectorDiagonalSecondMap {d T : ℕ} (U : Fin T → Point d) (s : Finset (Fin T))
    (y : Point d) : Point d →L[ℝ] Point d →L[ℝ] ℝ :=
  frameBlockSecondMap U s 0 (fun i =>
    (∏ j ∈ s.erase i, (1 - carmonOmegaThree (frameCoordinates U y j))) *
      (-deriv (deriv carmonOmegaThree) (frameCoordinates U y i)))

def selectorOffSecondMap {d T : ℕ} (U : Fin T → Point d) (s : Finset (Fin T))
    (y : Point d) : Point d →L[ℝ] Point d →L[ℝ] ℝ :=
  ∑ i ∈ s,
    (∑ j ∈ s.erase i,
      (∏ l ∈ (s.erase i).erase j, (1 - carmonOmegaThree (frameCoordinates U y l))) •
        (-(deriv carmonOmegaThree (frameCoordinates U y j) • innerSL ℝ (U j)))).smulRight
      (-(deriv carmonOmegaThree (frameCoordinates U y i) • innerSL ℝ (U i)))

theorem hasFDerivAt_fderiv_selectorProduct {d T : ℕ} (U : Fin T → Point d)
    (s : Finset (Fin T)) (y : Point d) :
    HasFDerivAt (fderiv ℝ (fun x => ∏ i ∈ s, (1 - carmonOmegaThree (frameCoordinates U x i))))
      (selectorDiagonalSecondMap U s y + selectorOffSecondMap U s y) y := by
  have hf (i : Fin T) : ContDiff ℝ 2 (fun x => 1 - carmonOmegaThree (frameCoordinates U x i)) :=
    contDiff_const.sub (contDiff_carmonOmegaThree_two.comp
      ((contDiff_pi.mp (contDiff_frameCoordinates_two U)) i))
  have h := hasFDerivAt_fderiv_finsetProd s
    (fun i x => 1 - carmonOmegaThree (frameCoordinates U x i)) (fun i _ => hf i) y
  apply h.congr_fderiv
  simp only [second_fderiv_selectorFactor, fderiv_selectorFactor]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · unfold selectorDiagonalSecondMap frameBlockSecondMap
    ext u v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.zero_apply, FunLike.coe_sum, Finset.sum_apply, smul_eq_mul,
      zero_mul, mul_zero, Finset.sum_const_zero, sub_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · rfl

theorem selector_scalar_product_bounds {T : ℕ} (z : Fin T → ℝ) (s : Finset (Fin T)) :
    0 ≤ (∏ i ∈ s, (1 - carmonOmegaThree (z i))) ∧
      (∏ i ∈ s, (1 - carmonOmegaThree (z i))) ≤ 1 := by
  have h0 (i : Fin T) : 0 ≤ 1 - carmonOmegaThree (z i) := sub_nonneg.mpr (smoothstep_le_one _)
  have h1 (i : Fin T) : 1 - carmonOmegaThree (z i) ≤ 1 := by
    have h : 0 ≤ carmonOmegaThree (z i) := smoothstep_nonneg _
    linarith
  exact ⟨Finset.prod_nonneg (fun i _ => h0 i), Finset.prod_le_one₀ (fun i _ => h0 i) (fun i _ => h1 i)⟩

theorem norm_selectorDiagonalSecondMap_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (y : Point d) :
    ‖selectorDiagonalSecondMap U s y‖ ≤ (462 / 5 : ℝ) := by
  apply norm_frameBlockSecondMap_le hU _ _ _ (by norm_num) (by norm_num)
  intro i hi
  obtain ⟨hp0, hp1⟩ := selector_scalar_product_bounds (frameCoordinates U y) (s.erase i)
  rw [abs_mul, abs_neg, abs_of_nonneg hp0]
  calc
    _ ≤ 1 * (462 / 5 : ℝ) := by gcongr; exact abs_second_deriv_carmonOmegaThree_le _
    _ = _ := by ring

theorem double_erased_product_le_exp {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α : ι → ℝ) (hα : ∀ i ∈ s, 0 ≤ α i ∧ α i ≤ 1)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s.erase i) :
    (∏ l ∈ (s.erase i).erase j, (1 - α l)) ≤
      (Real.exp 1) ^ 2 * Real.exp (-(∑ l ∈ s, α l)) := by
  calc
    _ ≤ ∏ l ∈ (s.erase i).erase j, Real.exp (-α l) :=
      Finset.prod_le_prod₀
        (fun l hl => sub_nonneg.mpr (hα l (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))).2)
        (fun l _ => Real.one_sub_le_exp_neg (α l))
    _ = Real.exp (-(∑ l ∈ (s.erase i).erase j, α l)) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]
    _ ≤ Real.exp (2 - ∑ l ∈ s, α l) := by
      apply Real.exp_le_exp.mpr
      have hs := Finset.sum_erase_add s α hi
      have hsj := Finset.sum_erase_add (s.erase i) α hj
      have hi1 := (hα i hi).2
      have hj1 := (hα j (Finset.mem_of_mem_erase hj)).2
      linarith
    _ = (Real.exp 1) ^ 2 * Real.exp (-(∑ l ∈ s, α l)) := by
      rw [show (2 : ℝ) - ∑ l ∈ s, α l = (1 + 1) + (-(∑ l ∈ s, α l)) by ring,
        Real.exp_add, Real.exp_add]
      ring

theorem weighted_frame_coordinate_sum_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (c : Fin T → ℝ) (x : Point d) :
    (∑ i ∈ s, |c i| * |frameCoordinates U x i|) ≤
      Real.sqrt (∑ i ∈ s, (c i) ^ 2) * ‖x‖ := by
  have h0 : 0 ≤ ∑ i ∈ s, (c i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB : (∑ i ∈ s, (frameCoordinates U x i) ^ 2) ≤ ‖x‖ ^ 2 := by
    simpa [frameCoordinates, Real.norm_eq_abs, sq_abs] using hU.sum_inner_products_le (s := s) x
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  calc
    _ ≤ (∑ i ∈ s, (c i) ^ 2) * ∑ i ∈ s, (frameCoordinates U x i) ^ 2 := by
      simpa only [sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq s (fun i => |c i|)
        (fun i => |frameCoordinates U x i|)
    _ ≤ (∑ i ∈ s, (c i) ^ 2) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left hB h0
    _ = (Real.sqrt (∑ i ∈ s, (c i) ^ 2) * ‖x‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt h0]

theorem selectorOffSecondMap_apply {d T : ℕ} (U : Fin T → Point d)
    (s : Finset (Fin T)) (y x v : Point d) :
    selectorOffSecondMap U s y x v =
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        (∏ l ∈ (s.erase i).erase j, (1 - carmonOmegaThree (frameCoordinates U y l))) *
          (deriv carmonOmegaThree (frameCoordinates U y j) * frameCoordinates U x j) *
          (deriv carmonOmegaThree (frameCoordinates U y i) * frameCoordinates U v i) := by
  simp only [selectorOffSecondMap, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, innerSL_apply_apply, frameCoordinates, smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem norm_selectorOffSecondMap_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (y : Point d) :
    ‖selectorOffSecondMap U s y‖ ≤ (924 / 5 : ℝ) * Real.exp 1 := by
  let α : Fin T → ℝ := fun i => carmonOmegaThree (frameCoordinates U y i)
  let δ : Fin T → ℝ := fun i => deriv carmonOmegaThree (frameCoordinates U y i)
  let S : ℝ := ∑ i ∈ s, α i
  let D : ℝ := ∑ i ∈ s, (δ i) ^ 2
  let E : ℝ := (Real.exp 1) ^ 2 * Real.exp (-S)
  let P : Fin T → Fin T → ℝ := fun i j => ∏ l ∈ (s.erase i).erase j, (1 - α l)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hP0 (i j : Fin T) : 0 ≤ P i j :=
    (selector_scalar_product_bounds (frameCoordinates U y) ((s.erase i).erase j)).1
  have hP (i : Fin T) (hi : i ∈ s) (j : Fin T) (hj : j ∈ s.erase i) : P i j ≤ E :=
    double_erased_product_le_exp s α (fun l _ => ⟨smoothstep_nonneg _, smoothstep_le_one _⟩) hi hj
  have hpoint (x v : Point d) : |selectorOffSecondMap U s y x v| ≤ E * D * ‖x‖ * ‖v‖ := by
    have hentry (i : Fin T) (hi : i ∈ s) (j : Fin T) (hj : j ∈ s.erase i) :
        |P i j * (δ j * frameCoordinates U x j) * (δ i * frameCoordinates U v i)| ≤
          E * (|δ i| * |frameCoordinates U v i|) * (|δ j| * |frameCoordinates U x j|) := by
      simp only [abs_mul]
      rw [abs_of_nonneg (hP0 i j)]
      calc
        _ = P i j * (|δ i| * |frameCoordinates U v i|) * (|δ j| * |frameCoordinates U x j|) := by ring
        _ ≤ _ := by gcongr; exact hP i hi j hj
    have hraw : |selectorOffSecondMap U s y x v| ≤
        ∑ i ∈ s, ∑ j ∈ s.erase i,
          E * (|δ i| * |frameCoordinates U v i|) * (|δ j| * |frameCoordinates U x j|) := by
      rw [selectorOffSecondMap_apply]
      change |∑ i ∈ s, ∑ j ∈ s.erase i,
        P i j * (δ j * frameCoordinates U x j) * (δ i * frameCoordinates U v i)| ≤ _
      calc
        _ ≤ ∑ i ∈ s, |∑ j ∈ s.erase i,
            P i j * (δ j * frameCoordinates U x j) * (δ i * frameCoordinates U v i)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ s, ∑ j ∈ s.erase i,
            |P i j * (δ j * frameCoordinates U x j) * (δ i * frameCoordinates U v i)| := by
          apply Finset.sum_le_sum
          intro i hi
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hentry i hi j hj))
    have hsum : |selectorOffSecondMap U s y x v| ≤
        E * (∑ i ∈ s, |δ i| * |frameCoordinates U v i|) *
          (∑ j ∈ s, |δ j| * |frameCoordinates U x j|) := by
      calc
        _ ≤ ∑ i ∈ s, ∑ j ∈ s.erase i,
            E * (|δ i| * |frameCoordinates U v i|) * (|δ j| * |frameCoordinates U x j|) := hraw
        _ ≤ ∑ i ∈ s, ∑ j ∈ s,
            E * (|δ i| * |frameCoordinates U v i|) * (|δ j| * |frameCoordinates U x j|) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i s)
          intro j hj hji
          positivity
        _ = ∑ i ∈ s, E * (|δ i| * |frameCoordinates U v i|) *
            (∑ j ∈ s, |δ j| * |frameCoordinates U x j|) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hv := weighted_frame_coordinate_sum_le hU s δ v
    have hx := weighted_frame_coordinate_sum_le hU s δ x
    calc
      _ ≤ E * (∑ i ∈ s, |δ i| * |frameCoordinates U v i|) *
          (∑ j ∈ s, |δ j| * |frameCoordinates U x j|) := hsum
      _ ≤ E * (Real.sqrt D * ‖v‖) * (Real.sqrt D * ‖x‖) := by gcongr
      _ = E * (Real.sqrt D) ^ 2 * ‖x‖ * ‖v‖ := by ring
      _ = E * D * ‖x‖ * ‖v‖ := by rw [Real.sq_sqrt hD0]
  have hnorm : ‖selectorOffSecondMap U s y‖ ≤ E * D := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hE0 hD0)
    intro x
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    simpa only [Real.norm_eq_abs] using hpoint x v
  have hD : D ≤ (924 / 5 : ℝ) * S := by
    dsimp [D, S, δ, α]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => carmonOmegaThree_glaeser (frameCoordinates U y i))
  calc
    _ ≤ E * D := hnorm
    _ ≤ E * ((924 / 5 : ℝ) * S) := mul_le_mul_of_nonneg_left hD hE0
    _ = (924 / 5 : ℝ) * (Real.exp 1) ^ 2 * (S * Real.exp (-S)) := by dsimp [E]; ring
    _ ≤ (924 / 5 : ℝ) * (Real.exp 1) ^ 2 * Real.exp (-1) :=
      mul_le_mul_of_nonneg_left (Real.mul_exp_neg_le_exp_neg_one S) (by positivity)
    _ = (924 / 5 : ℝ) * Real.exp 1 := by
      rw [Real.exp_neg]
      field_simp [(Real.exp_pos 1).ne']

theorem norm_second_fderiv_selectorProduct_le_595 {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (y : Point d) :
    ‖fderiv ℝ (fderiv ℝ (fun x => ∏ i ∈ s, (1 - carmonOmegaThree (frameCoordinates U x i)))) y‖ ≤ 595 := by
  rw [(hasFDerivAt_fderiv_selectorProduct U s y).fderiv]
  calc
    _ ≤ ‖selectorDiagonalSecondMap U s y‖ + ‖selectorOffSecondMap U s y‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ (462 / 5 : ℝ) + (924 / 5) * Real.exp 1 :=
      add_le_add (norm_selectorDiagonalSecondMap_le hU s y) (norm_selectorOffSecondMap_le hU s y)
    _ ≤ (462 / 5 : ℝ) + (924 / 5) * (2.7182818286 : ℝ) := by gcongr; exact Real.exp_one_lt_d9.le
    _ ≤ 595 := by norm_num

theorem norm_second_fderiv_chainSelector_pullback_le_595
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    ‖fderiv ℝ (fderiv ℝ (fun x => chainSelector carmonOmegaThree (frameCoordinates U x) k)) y‖ ≤ 595 :=
  norm_second_fderiv_selectorProduct_le_595 hU (Finset.univ.filter (k < ·)) y

/-- Complete ambient Euclidean Hessian bound for the actual correction Q. -/
theorem norm_second_fderiv_gatedCorrection_le_4100_of_orthonormal
    {d T : ℕ} {U : Fin T → Point d} (hU : Orthonormal ℝ U) (y : Point d) :
    ‖fderiv ℝ (fderiv ℝ (gatedCorrection U)) y‖ ≤ 4100 := by
  apply norm_second_gatedCorrection_le_4100_of_component_bounds hU y
  intro k hk
  exact ⟨norm_second_fderiv_chainCorrection_pullback_le_264 hU k y hk,
    norm_second_fderiv_chainSelector_pullback_le_595 hU k y,
    norm_second_fderiv_gatedResidual_le_41 hU k y⟩

end

end HeavyTailedNoise
