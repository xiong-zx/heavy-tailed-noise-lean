import HeavyTailedNoise.Lower.Gated.HardProjectionBounds

/-!
Pointwise Fréchet derivative of the manuscript's radial soft projection.
The operator-norm and second-derivative bounds remain separate obligations.
-/

namespace HeavyTailedNoise

noncomputable section

theorem hasFDerivAt_softProjection_raw {d : ℕ} (R : ℝ) (x : Point d) :
    HasFDerivAt (softProjection R)
      ((Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹ •
          ContinuousLinearMap.id ℝ (Point d) +
        (((ContinuousLinearMap.toSpanSingleton ℝ
              (-((Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2)) ^ 2)⁻¹)).comp
            ((1 / (2 * Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))) •
              ((R ^ 2)⁻¹ • (2 • innerSL ℝ x)))).smulRight x)) x := by
  let b : Point d → ℝ := fun y => 1 + ‖y‖ ^ 2 / R ^ 2
  have hbpos : 0 < b x := by dsimp [b]; positivity
  have hb : HasFDerivAt b ((R ^ 2)⁻¹ • (2 • innerSL ℝ x)) x := by
    have hnorm := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have hscale := hnorm.const_smul ((R ^ 2)⁻¹)
    have hsum := (hasFDerivAt_const (1 : ℝ) x).add hscale
    convert hsum using 1
    · funext y
      dsimp [b]
      simp [div_eq_mul_inv, mul_comm]
    · simp
  have hsqrt := hb.sqrt hbpos.ne'
  have hsqrtpos : 0 < Real.sqrt (b x) := Real.sqrt_pos.mpr hbpos
  have hinv :=
    (hasFDerivAt_inv (𝕜 := ℝ) hsqrtpos.ne').comp x hsqrt
  have hprod := hinv.smul (hasFDerivAt_id x)
  have hfun : ((fun y : Point d => (Real.sqrt (b y))⁻¹) •
      (id : Point d → Point d)) = softProjection R := by
    funext y
    simp [softProjection, b]
  rw [← hfun]
  simpa [b, Function.comp_def] using hprod

/-- The readable radial Jacobian formula, with the manuscript's positive radius. -/
theorem fderiv_softProjection_apply {d : ℕ} {R : ℝ} (hR : 0 < R)
    (x v : Point d) :
    fderiv ℝ (softProjection R) x v =
      (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹ • v -
        ((inner ℝ x v) /
          (R ^ 2 * (1 + ‖x‖ ^ 2 / R ^ 2) *
            Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))) • x := by
  let B : ℝ := 1 + ‖x‖ ^ 2 / R ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  rw [(hasFDerivAt_softProjection_raw R x).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    innerSL_apply_apply, smul_smul, smul_eq_mul, nsmul_eq_mul]
  have hscalar :
      (1 / (2 * Real.sqrt B)) * (R ^ 2)⁻¹ * (2 * inner ℝ x v) *
          (-(Real.sqrt B ^ 2)⁻¹) =
        -((inner ℝ x v) / (R ^ 2 * B * Real.sqrt B)) := by
    rw [Real.sq_sqrt hB.le]
    field_simp [hR.ne', hs.ne', hB.ne']
  dsimp [B] at hscalar
  norm_num only [Nat.cast_ofNat] at *
  rw [hscalar]
  simp [B, sub_eq_add_neg, neg_smul]


end

end HeavyTailedNoise
