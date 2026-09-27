import HeavyTailedNoise.Lower.Gated.SupportResidualGate

/-!
Dimension-independent first-derivative accounting for the actual correction Q.
Inactive summands have zero derivatives; the unique active summand is bounded
using explicit frozen component estimates. The scalar cutoff derivative bound
is discharged here. This module does not assert the Hessian bound.
-/

namespace HeavyTailedNoise

open scoped BigOperators Topology

noncomputable section

theorem deriv_carmonChi (s : ℝ) :
    deriv carmonChi s = -deriv smoothstep ((s - 1 / 16) / 1000) / 1000 := by
  have ha : HasDerivAt (fun t : ℝ => (t - 1 / 16) / 1000) (1 / 1000) s := by
    convert! ((hasDerivAt_id s).sub_const (1 / 16 : ℝ)).div_const (1000 : ℝ) using 1 <;>
      norm_num
  have h := (((differentiable_smoothstep _).hasDerivAt).comp s ha).const_sub 1
  have h' : HasDerivAt carmonChi
      (-deriv smoothstep ((s - 1 / 16) / 1000) / 1000) s := by
    convert! h using 1 <;> (try simp only [carmonChi, Function.comp_def]) <;> ring
  exact h'.deriv

/-- The frozen cutoff slope constant `1.875 / 1000`, proved for the exact χ. -/
theorem abs_deriv_carmonChi_le (s : ℝ) :
    |deriv carmonChi s| ≤ (15 / 8 : ℝ) / 1000 := by
  rw [deriv_carmonChi, abs_div, abs_neg]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1000)]
  exact div_le_div_of_nonneg_right (abs_deriv_smoothstep_le _)
    (by norm_num : (0 : ℝ) ≤ 1000)

/-- A named summand of the previously defined Q. The sum identity below is
definitional, so the original Q remains authoritative. -/
def gatedCorrectionTerm {d T : ℕ} (U : Fin T → Point d) (k : Fin T) (y : Point d) : ℝ :=
  (1 - carmonChi (gatedResidual U k y)) *
    chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 (frameCoordinates U y) k

theorem gatedCorrection_eq_sum_terms {d T : ℕ} (U : Fin T → Point d) :
    gatedCorrection U = (fun y => ∑ k : Fin T, gatedCorrectionTerm U k y) := rfl

theorem contDiff_gatedCorrectionTerm_two {d T : ℕ} (U : Fin T → Point d) (k : Fin T) :
    ContDiff ℝ 2 (gatedCorrectionTerm U k) :=
  (contDiff_const.sub (contDiff_carmonChi_two.comp (contDiff_gatedResidual_two U k))).mul
    ((contDiff_actual_chainGateTerm_two k).comp (contDiff_frameCoordinates_two U))

theorem gatedCorrectionTerm_zeroTwoJet_of_inactive {d T : ℕ} {U : Fin T → Point d}
    {k : Fin T} {y : Point d}
    (hk : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k = 0) : ZeroTwoJet (gatedCorrectionTerm U k) y :=
  inactive_chainGateTerm_weighted_pullback
    contDiff_carmonPsi_two contDiff_carmonPhi_two
    contDiff_carmonOmega_two contDiff_carmonOmegaThree_two
    (contDiff_frameCoordinates_two U)
    (contDiff_const.sub (contDiff_carmonChi_two.comp (contDiff_gatedResidual_two U k)))
    (actual_chainGateTerm_zeroTwoJet_of_inactive hk)

theorem fderiv_gatedCorrection_eq_sum {d T : ℕ} (U : Fin T → Point d) (y : Point d) :
    fderiv ℝ (gatedCorrection U) y =
      ∑ k : Fin T, fderiv ℝ (gatedCorrectionTerm U k) y := by
  rw [gatedCorrection_eq_sum_terms]
  exact fderiv_fun_sum fun k _ =>
    (contDiff_gatedCorrectionTerm_two U k).differentiable (by norm_num) y

/-- Only the active summand contributes to the derivative, with no factor T. -/
theorem fderiv_gatedCorrection_eq_active {d T : ℕ} (U : Fin T → Point d) (y : Point d)
    {k : Fin T}
    (hk : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0) :
    fderiv ℝ (gatedCorrection U) y = fderiv ℝ (gatedCorrectionTerm U k) y := by
  rw [fderiv_gatedCorrection_eq_sum]
  apply Finset.sum_eq_single k
  · intro j hj hjk
    apply (gatedCorrectionTerm_zeroTwoJet_of_inactive (U := U) (k := j) (y := y) ?_).first.fderiv
    by_contra hact
    exact hjk (actual_chainGateTerm_unique_active hact hk)
  · simp

theorem fderiv_gatedCorrection_eq_zero_of_all_inactive {d T : ℕ}
    (U : Fin T → Point d) (y : Point d)
    (hzero : ∀ k, chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k = 0) : fderiv ℝ (gatedCorrection U) y = 0 := by
  rw [fderiv_gatedCorrection_eq_sum]
  apply Finset.sum_eq_zero
  intro k hk
  exact (gatedCorrectionTerm_zeroTwoJet_of_inactive (hzero k)).first.fderiv

theorem norm_actual_chainSelector_le_one {T : ℕ} (z : Fin T → ℝ) (k : Fin T) :
    ‖chainSelector carmonOmegaThree z k‖ ≤ 1 := by
  have hlo (i : Fin T) : 0 ≤ 1 - carmonOmegaThree (z i) :=
    sub_nonneg.mpr (smoothstep_le_one _)
  have hup (i : Fin T) : 1 - carmonOmegaThree (z i) ≤ 1 := by
    have h : 0 ≤ carmonOmegaThree (z i) := smoothstep_nonneg _
    linarith
  have hn : 0 ≤ chainSelector carmonOmegaThree z k := Finset.prod_nonneg (fun i _ => hlo i)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact Finset.prod_le_one₀ (fun i _ => hlo i) (fun i _ => hup i)

theorem norm_gateFactor_le_one {d T : ℕ} (U : Fin T → Point d) (k : Fin T) (y : Point d) :
    ‖1 - carmonChi (gatedResidual U k y)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (carmonChi_le_one _))]
  linarith [carmonChi_nonneg (gatedResidual U k y)]

/-- The residual derivative is bounded only where χ' is nonzero. Thus this
premise does not impose a false global bound on the quadratic residual. -/
theorem norm_fderiv_gateFactor_le {d T : ℕ} (U : Fin T → Point d) (k : Fin T) (y : Point d)
    (hσ : deriv carmonChi (gatedResidual U k y) ≠ 0 →
      ‖fderiv ℝ (gatedResidual U k) y‖ ≤ (3169 / 10 : ℝ)) :
    ‖fderiv ℝ (fun x => 1 - carmonChi (gatedResidual U k x)) y‖ ≤
      ((15 / 8 : ℝ) / 1000) * (3169 / 10) := by
  have hc := (contDiff_carmonChi_two.differentiable (by norm_num)
    (gatedResidual U k y)).hasDerivAt
  have hs := (contDiff_gatedResidual_two U k).differentiable (by norm_num) y
  have heq : fderiv ℝ (fun x => 1 - carmonChi (gatedResidual U k x)) y =
      -(deriv carmonChi (gatedResidual U k y) • fderiv ℝ (gatedResidual U k) y) :=
    ((hc.comp_hasFDerivAt y hs.hasFDerivAt).const_sub 1).fderiv
  rw [heq, norm_neg, norm_smul]
  by_cases hz : deriv carmonChi (gatedResidual U k y) = 0
  · norm_num [hz]
  · apply mul_le_mul
    · simpa only [Real.norm_eq_abs] using abs_deriv_carmonChi_le (gatedResidual U k y)
    · exact hσ hz
    · exact norm_nonneg _
    · norm_num

theorem gate_norm_fderiv_mul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => f y * g y) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖ := by
  rw [fderiv_fun_mul hf hg]
  simpa only [norm_smul] using
    norm_add_le (f x • fderiv ℝ g x) (g x • fderiv ℝ f x)

/-- The frozen single-active-term arithmetic, with exactly its constants. -/
theorem norm_fderiv_gatedCorrectionTerm_le_100 {d T : ℕ}
    (U : Fin T → Point d) (k : Fin T) (y : Point d)
    (hq : ‖chainCorrection carmonPsi carmonPhi carmonOmega 1 (frameCoordinates U y) k‖ ≤
      (487 / 100 : ℝ))
    (hdq : ‖fderiv ℝ (fun x =>
      chainCorrection carmonPsi carmonPhi carmonOmega 1 (frameCoordinates U x) k) y‖ ≤ 30)
    (hdp : ‖fderiv ℝ (fun x => chainSelector carmonOmegaThree (frameCoordinates U x) k) y‖ ≤
      (68 / 5 : ℝ))
    (hσ : deriv carmonChi (gatedResidual U k y) ≠ 0 →
      ‖fderiv ℝ (gatedResidual U k) y‖ ≤ (3169 / 10 : ℝ)) :
    ‖fderiv ℝ (gatedCorrectionTerm U k) y‖ ≤ 100 := by
  let a : Point d → ℝ := fun x => 1 - carmonChi (gatedResidual U k x)
  let q : Point d → ℝ := fun x =>
    chainCorrection carmonPsi carmonPhi carmonOmega 1 (frameCoordinates U x) k
  let p : Point d → ℝ := fun x => chainSelector carmonOmegaThree (frameCoordinates U x) k
  have ha : ContDiff ℝ 2 a :=
    contDiff_const.sub (contDiff_carmonChi_two.comp (contDiff_gatedResidual_two U k))
  have hqC : ContDiff ℝ 2 q :=
    (contDiff_chainCorrection 1 k contDiff_carmonPsi_two contDiff_carmonPhi_two
      contDiff_carmonOmega_two).comp (contDiff_frameCoordinates_two U)
  have hpC : ContDiff ℝ 2 p :=
    (contDiff_chainSelector k contDiff_carmonOmegaThree_two).comp (contDiff_frameCoordinates_two U)
  have hp : ‖p y‖ ≤ 1 := norm_actual_chainSelector_le_one _ _
  have hav : ‖a y‖ ≤ 1 := norm_gateFactor_le_one U k y
  have had : ‖fderiv ℝ a y‖ ≤ ((15 / 8 : ℝ) / 1000) * (3169 / 10) :=
    norm_fderiv_gateFactor_le U k y hσ
  have hqp : ‖fderiv ℝ (fun x => q x * p x) y‖ ≤ (487 / 100 : ℝ) * (68 / 5) + 30 := by
    calc
      _ ≤ ‖q y‖ * ‖fderiv ℝ p y‖ + ‖p y‖ * ‖fderiv ℝ q y‖ :=
        gate_norm_fderiv_mul_le (hqC.differentiable (by norm_num) y)
          (hpC.differentiable (by norm_num) y)
      _ ≤ (487 / 100 : ℝ) * (68 / 5) + 1 * 30 := by gcongr
      _ = _ := by ring
  have hv : ‖q y * p y‖ ≤ (487 / 100 : ℝ) := by
    rw [norm_mul]
    calc
      _ ≤ (487 / 100 : ℝ) * 1 := by gcongr
      _ = _ := by ring
  have heq : gatedCorrectionTerm U k = (fun x => a x * (q x * p x)) := rfl
  rw [heq]
  calc
    _ ≤ ‖a y‖ * ‖fderiv ℝ (fun x => q x * p x) y‖ +
        ‖q y * p y‖ * ‖fderiv ℝ a y‖ :=
      gate_norm_fderiv_mul_le (ha.differentiable (by norm_num) y)
        ((hqC.mul hpC).differentiable (by norm_num) y)
    _ ≤ 1 * ((487 / 100 : ℝ) * (68 / 5) + 30) +
        (487 / 100) * (((15 / 8 : ℝ) / 1000) * (3169 / 10)) := by gcongr
    _ ≤ 100 := by norm_num

/-- Conditional dimension-independent bound for the actual gradient of Q.
Each remaining pointwise premise is required only for the unique active index. -/
theorem norm_gradient_gatedCorrection_le_100 {d T : ℕ}
    (U : Fin T → Point d) (y : Point d)
    (hbounds : ∀ k : Fin T,
      chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
        (frameCoordinates U y) k ≠ 0 →
      ‖chainCorrection carmonPsi carmonPhi carmonOmega 1 (frameCoordinates U y) k‖ ≤
          (487 / 100 : ℝ) ∧
      ‖fderiv ℝ (fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
        (frameCoordinates U x) k) y‖ ≤ 30 ∧
      ‖fderiv ℝ (fun x => chainSelector carmonOmegaThree (frameCoordinates U x) k) y‖ ≤
          (68 / 5 : ℝ) ∧
      (deriv carmonChi (gatedResidual U k y) ≠ 0 →
        ‖fderiv ℝ (gatedResidual U k) y‖ ≤ (3169 / 10 : ℝ))) :
    ‖gradient (gatedCorrection U) y‖ ≤ 100 := by
  have hn : ‖gradient (gatedCorrection U) y‖ = ‖fderiv ℝ (gatedCorrection U) y‖ := by
    simp [gradient]
  rw [hn]
  by_cases ha : ∃ k : Fin T, chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
      (frameCoordinates U y) k ≠ 0
  · obtain ⟨k, hk⟩ := ha
    rw [fderiv_gatedCorrection_eq_active U y hk]
    obtain ⟨hq, hdq, hdp, hσ⟩ := hbounds k hk
    exact norm_fderiv_gatedCorrectionTerm_le_100 U k y hq hdq hdp hσ
  · have hzero : ∀ k : Fin T,
        chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
          (frameCoordinates U y) k = 0 := by simpa using ha
    rw [fderiv_gatedCorrection_eq_zero_of_all_inactive U y hzero, norm_zero]
    norm_num

/-- A tighter version of the already proved Gaussian-window estimate. It avoids
the false rounded arithmetic `exp(1) * 1.792 < 4.87`. -/
theorem carmonPhi_local_increment_abs_le_refined {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |carmonPhi t - carmonPhi 0| ≤ (3039107 / 3840000 : ℝ) := by
  have hs : Real.sqrt (Real.exp 1) ≤ (1649 / 1000 : ℝ) := by
    nlinarith [Real.sq_sqrt (Real.exp_pos 1).le, Real.sqrt_nonneg (Real.exp 1),
      Real.exp_one_lt_d9]
  have hp : carmonPhi (1 / 2) - carmonPhi 0 ≤ (3039107 / 3840000 : ℝ) := by
    rw [carmonPhi_sub]
    calc
      _ ≤ Real.sqrt (Real.exp 1) * (1843 / 3840 : ℝ) :=
        mul_le_mul_of_nonneg_left carmonPhi_half_integral_bound (Real.sqrt_nonneg _)
      _ ≤ (1649 / 1000 : ℝ) * (1843 / 3840) :=
        mul_le_mul_of_nonneg_right hs (by norm_num)
      _ = _ := by norm_num
  have hm : carmonPhi 0 - carmonPhi (-1 / 2) ≤ (3039107 / 3840000 : ℝ) := by
    rw [carmonPhi_sub]
    calc
      _ ≤ Real.sqrt (Real.exp 1) * (1843 / 3840 : ℝ) :=
        mul_le_mul_of_nonneg_left carmonPhi_neg_half_integral_bound (Real.sqrt_nonneg _)
      _ ≤ (1649 / 1000 : ℝ) * (1843 / 3840) :=
        mul_le_mul_of_nonneg_right hs (by norm_num)
      _ = _ := by norm_num
  obtain ⟨hl, hr⟩ := abs_le.mp ht
  have hml := strictMono_carmonPhi.monotone hl
  have hmr := strictMono_carmonPhi.monotone hr
  apply abs_le.mpr
  constructor <;> linarith

theorem carmonPsi_le_exp_one (t : ℝ) : carmonPsi t ≤ Real.exp 1 := by
  by_cases ht : t ≤ 1 / 2
  · rw [carmonPsi_zero_of_le ht]
    exact (Real.exp_pos 1).le
  · rw [carmonPsi_eq_exp_of_gt (lt_of_not_ge ht)]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((2 * t - 1)⁻¹)]

/-- The actual q amplitude is at most 4.87. The proof uses the refined exact
Gaussian integral estimate above, rather than rounding 1.792 down. -/
theorem norm_frontierCorrection_actual_le (a b : ℝ) :
    ‖frontierCorrection carmonPsi carmonPhi carmonOmega 1 a b‖ ≤ (487 / 100 : ℝ) := by
  by_cases ha : |a| ≤ 1 / 2
  · rw [frontierCorrection_eq_zero_of_predecessor_small
      (fun _ ht => carmonPsi_zero_of_le ht) ha, norm_zero]
    norm_num
  by_cases hb : 1 / 2 ≤ |b|
  · rw [frontierCorrection_eq_zero_of_current_large (fun _ ht => carmonOmega_one ht) hb,
      norm_zero]
    norm_num
  have ha' : (1 / 2 : ℝ) < |a| := lt_of_not_ge ha
  have hb' : |b| < (1 / 2 : ℝ) := lt_of_not_ge hb
  have hpos := frontierCorrection_pos (fun _ ht => carmonPsi_zero_of_le ht)
    (fun _ ht => carmonPsi_pos_of_gt ht) (fun _ ht => carmonOmega_lt_one ht)
    (fun _ ht => carmonPhi_correction_brackets_pos ht) ha' hb'
  rw [Real.norm_eq_abs, abs_of_nonneg hpos.le]
  have hinc := abs_le.mp (carmonPhi_local_increment_abs_le_refined hb'.le)
  have hincn := abs_le.mp (carmonPhi_local_increment_abs_le_refined
    (t := -b) (by simpa using hb'.le))
  obtain ⟨hAl, hBl⟩ := carmonPhi_correction_brackets_pos hb'
  have hAu : carmonPhi b - carmonPhi 0 + 1 ≤ 1 + (3039107 / 3840000 : ℝ) := by linarith
  have hBu : carmonPhi 0 - carmonPhi (-b) + 1 ≤ 1 + (3039107 / 3840000 : ℝ) := by linarith
  have hcut0 : 0 ≤ 1 - carmonOmega b := sub_nonneg.mpr (smoothstep_le_one _)
  have hcut1 : 1 - carmonOmega b ≤ 1 := by
    have h : 0 ≤ carmonOmega b := smoothstep_nonneg _
    linarith
  have hnum : Real.exp 1 * (1 + (3039107 / 3840000 : ℝ)) ≤ 487 / 100 := by
    calc
      _ ≤ (2.7182818286 : ℝ) * (1 + (3039107 / 3840000 : ℝ)) :=
        mul_le_mul_of_nonneg_right Real.exp_one_lt_d9.le (by norm_num)
      _ ≤ _ := by norm_num
  rcases lt_abs.mp ha' with ha' | ha'
  · have hneg : carmonPsi (-a) = 0 := carmonPsi_zero_of_le (by linarith)
    simp only [frontierCorrection, hneg, zero_mul, add_zero]
    calc
      _ ≤ Real.exp 1 * (1 + (3039107 / 3840000 : ℝ)) * 1 := by
        gcongr
        exact carmonPsi_le_exp_one a
      _ ≤ 487 / 100 := by simpa using hnum
  · have hzero : carmonPsi a = 0 := carmonPsi_zero_of_le (by linarith)
    simp only [frontierCorrection, hzero, zero_mul, zero_add]
    calc
      _ ≤ Real.exp 1 * (1 + (3039107 / 3840000 : ℝ)) * 1 := by
        gcongr
        exact carmonPsi_le_exp_one (-a)
      _ ≤ 487 / 100 := by simpa using hnum

theorem norm_actual_chainCorrection_le {T : ℕ} (z : Fin T → ℝ) (k : Fin T) :
    ‖chainCorrection carmonPsi carmonPhi carmonOmega 1 z k‖ ≤ (487 / 100 : ℝ) :=
  norm_frontierCorrection_actual_le _ _

/-- The q-amplitude and cutoff-slope premises have been discharged. The three
remaining estimates are precisely the differential bounds still needed from
the frozen geometric calculation, only at an active index. -/
theorem norm_gradient_gatedCorrection_le_100_of_derivative_bounds {d T : ℕ}
    (U : Fin T → Point d) (y : Point d)
    (hbounds : ∀ k : Fin T,
      chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1
        (frameCoordinates U y) k ≠ 0 →
      ‖fderiv ℝ (fun x => chainCorrection carmonPsi carmonPhi carmonOmega 1
        (frameCoordinates U x) k) y‖ ≤ 30 ∧
      ‖fderiv ℝ (fun x => chainSelector carmonOmegaThree (frameCoordinates U x) k) y‖ ≤
          (68 / 5 : ℝ) ∧
      (deriv carmonChi (gatedResidual U k y) ≠ 0 →
        ‖fderiv ℝ (gatedResidual U k) y‖ ≤ (3169 / 10 : ℝ))) :
    ‖gradient (gatedCorrection U) y‖ ≤ 100 := by
  apply norm_gradient_gatedCorrection_le_100 U y
  intro k hk
  exact ⟨norm_actual_chainCorrection_le _ _, hbounds k hk⟩

end

end HeavyTailedNoise
