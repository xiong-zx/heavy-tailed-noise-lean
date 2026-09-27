import HeavyTailedNoise.Lower.Fradin.BernoulliOracle
import HeavyTailedNoise.Lower.Gated.HardProjectionSecondBound
import HeavyTailedNoise.Lower.Gated.HardObjectiveGap

/-!
One concrete Bernoulli/Carmon lift in the existing gradient-only model.
There is no new oracle model and no alternative radial projection.
-/

namespace HeavyTailedNoise.RandomizedLift

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

/-- Synthesis in the given (not necessarily orthonormal) finite frame. -/
def frameEmbed {d T : ℕ} (U : Fin T → Point d) : Point T →L[ℝ] Point d :=
  ∑ i : Fin T, (PiLp.proj 2 (fun _ : Fin T => ℝ) i).smulRight (U i)

@[simp] theorem frameEmbed_apply {d T : ℕ} (U : Fin T → Point d) (z : Point T) :
    frameEmbed U z = ∑ i : Fin T, z i • U i := by
  simp [frameEmbed]

theorem frameEmbed_adjoint_apply {d T : ℕ} (U : Fin T → Point d) (x : Point d) :
    (frameEmbed U).adjoint x = WithLp.toLp 2 (frameCoordinates U x) := by
  ext i
  have h := (frameEmbed U).adjoint_inner_left (EuclideanSpace.single i 1) x
  simpa [frameEmbed_apply, EuclideanSpace.inner_single_right,
    PiLp.single_apply, frameCoordinates, real_inner_comm] using h

theorem norm_frameEmbed_apply {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (z : Point T) : ‖frameEmbed U z‖ = ‖z‖ := by
  have hs : ‖frameEmbed U z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [frameEmbed_apply, ← real_inner_self_eq_norm_sq]
    rw [hU.inner_sum (fun i => z i) (fun i => z i) Finset.univ]
    simpa [pow_two] using (EuclideanSpace.real_norm_sq_eq z).symm
  nlinarith [norm_nonneg (frameEmbed U z), norm_nonneg z]

theorem norm_frameEmbed_le_one {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) : ‖frameEmbed U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [norm_frameEmbed_apply hU]
  simp only [one_mul, le_refl]

/-- The prescribed Euclidean coordinates of the existing soft projection. -/
def coordinates {d T : ℕ} (U : Fin T → Point d) (R : ℝ) (x : Point d) : Point T :=
  WithLp.toLp 2 (frameCoordinates U (softProjection R x))

theorem coordinates_eq_adjoint {d T : ℕ} (U : Fin T → Point d) (R : ℝ) :
    coordinates U R = fun x => (frameEmbed U).adjoint (softProjection R x) := by
  funext x
  exact (frameEmbed_adjoint_apply U _).symm

/-- Actual Carmon value plus the ambient quadratic. -/
def potential {d T : ℕ} (U : Fin T → Point d) (R η : ℝ) (x : Point d) : ℝ :=
  carmonChainValue (coordinates U R x) + (η / 2) * ‖x‖ ^ 2

/-- The ambient linear transport applied to the genuine oracle response. -/
def transport {d T : ℕ} (U : Fin T → Point d) (R : ℝ) (x : Point d) :
    Point T →L[ℝ] Point d :=
  (fderiv ℝ (softProjection R) x).adjoint.comp (frameEmbed U)

def populationGradient {d T : ℕ} (U : Fin T → Point d) (R η : ℝ)
    (x : Point d) : Point d :=
  transport U R x (carmonChainGradient (coordinates U R x)) + η • x

def response {d T : ℕ} (U : Fin T → Point d) (R η : ℝ)
    (θ : unitInterval) (x : Point d) (D : Bool) : Point d :=
  transport U R x (Fradin.bernoulliResponse θ (coordinates U R x) D) + η • x

theorem contDiff_coordinates_two {d T : ℕ} (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) : ContDiff ℝ 2 (coordinates U R) := by
  rw [coordinates_eq_adjoint]
  exact (frameEmbed U).adjoint.contDiff.comp (contDiff_softProjection_two hR)

theorem hasGradientAt_potential {d T : ℕ} (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) (η : ℝ) (x : Point d) :
    HasGradientAt (potential U R η) (populationGradient U R η x) x := by
  have hz : HasFDerivAt (coordinates U R)
      ((frameEmbed U).adjoint.comp (fderiv ℝ (softProjection R) x)) x := by
    rw [coordinates_eq_adjoint]
    exact (frameEmbed U).adjoint.hasFDerivAt.comp x
      (((contDiff_softProjection_two hR).differentiable (by norm_num)) x).hasFDerivAt
  have hc := (hasGradientAt_carmonChainValue (coordinates U R x)).hasFDerivAt.comp x hz
  have hq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (η / 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hc.add hq using 1
  · rfl
  · ext v
    simp only [populationGradient, transport, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      InnerProductSpace.toDual_apply_apply, innerSL_apply_apply, real_inner_smul_left,
      inner_add_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right, smul_eq_mul]
    ring

theorem populationGradient_eq_gradient {d T : ℕ} (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) (η : ℝ) :
    populationGradient U R η = gradient (potential U R η) := by
  funext x
  exact (hasGradientAt_potential U hR η x).unique
    (hasGradientAt_potential U hR η x).differentiableAt.hasGradientAt

theorem contDiff_potential_two {d T : ℕ} (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) (η : ℝ) : ContDiff ℝ 2 (potential U R η) := by
  exact ((contDiff_carmonChainValue_two T).comp (contDiff_coordinates_two U hR)).add
    (contDiff_const.mul (contDiff_id.norm_sq ℝ))

theorem continuous_populationGradient {d T : ℕ} (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) (η : ℝ) : Continuous (populationGradient U R η) := by
  rw [populationGradient_eq_gradient U hR η]
  exact ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
    ((contDiff_potential_two U hR η).fderiv_right (m := 1) (by norm_num)).continuous)

theorem continuous_transport {d T : ℕ} (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) : Continuous (transport U R) := by
  have hf : Continuous (fderiv ℝ (softProjection (d := d) R)) :=
    ((contDiff_softProjection_two hR).fderiv_right (m := 1) (by norm_num)).continuous
  have ha := ContinuousLinearMap.adjoint.continuous.comp hf
  exact ha.clm_comp continuous_const

theorem measurable_response {d T : ℕ} (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) (η : ℝ) (θ : unitInterval) :
    Measurable (fun z : Point d × Bool => response U R η θ z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro D
  have hz := (contDiff_coordinates_two U hR).continuous
  have hg : Continuous (fun x : Point d => Fradin.bernoulliResponse θ (coordinates U R x) D) := by
    exact ((continuous_carmonChainGradient T).comp hz).add
      ((Fradin.continuous_maskedGradient.comp hz).const_smul (Fradin.noiseFactor θ D))
  exact (((continuous_transport U hR).clm_apply hg).add
    (continuous_id.const_smul η)).measurable

def oracle {d T : ℕ} (U : Fin T → Point d) {R : ℝ} (hR : 0 < R)
    (η : ℝ) (θ : unitInterval) : GradientOracle d Bool where
  law := Fradin.bernoulliLaw θ
  law_probability := inferInstance
  response := response U R η θ
  measurable_response := measurable_response U hR η θ

theorem continuous_joint_coordinates {d T : ℕ} {R : ℝ} (hR : 0 < R) :
    Continuous (fun z : (Fin T → Point d) × Point d => coordinates z.1 R z.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin T => ℝ)).comp
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp continuous_fst).inner
    ((contDiff_softProjection_two hR).continuous.comp continuous_snd)

theorem continuous_joint_frameEmbed_apply {d T : ℕ} :
    Continuous (fun z : (Fin T → Point d) × Point T => frameEmbed z.1 z.2) := by
  simp only [frameEmbed_apply]
  apply continuous_finset_sum
  intro i hi
  exact ((PiLp.continuous_apply 2 (fun _ : Fin T => ℝ) i).comp continuous_snd).smul
    ((continuous_apply i).comp continuous_fst)

theorem continuous_joint_potential {d T : ℕ} {R : ℝ} (hR : 0 < R) (η : ℝ) :
    Continuous (fun z : (Fin T → Point d) × Point d => potential z.1 R η z.2) := by
  exact ((contDiff_carmonChainValue_two T).continuous.comp (continuous_joint_coordinates hR)).add
    (continuous_const.mul (continuous_snd.norm.pow 2))

theorem measurable_joint_populationGradient {d T : ℕ} {R : ℝ} (hR : 0 < R) (η : ℝ) :
    Measurable (fun z : (Fin T → Point d) × Point d => populationGradient z.1 R η z.2) := by
  have hcont : Continuous (Function.uncurry (fun U : Fin T → Point d => potential U R η)) :=
    continuous_joint_potential hR η
  have hf := measurable_fderiv_with_param ℝ hcont
  have hg := (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.measurable.comp hf
  have heq : (fun z : (Fin T → Point d) × Point d => populationGradient z.1 R η z.2) =
      (fun z : (Fin T → Point d) × Point d => gradient (potential z.1 R η) z.2) := by
    funext z
    exact congrFun (populationGradient_eq_gradient z.1 hR η) z.2
  rw [heq]
  exact hg

theorem measurable_joint_response {d T : ℕ} {R : ℝ} (hR : 0 < R)
    (η : ℝ) (θ : unitInterval) :
    Measurable (fun z : ((Fin T → Point d) × Point d) × Bool =>
      response z.1.1 R η θ z.1.2 z.2) := by
  apply measurable_from_prod_countable_left
  intro D
  have hz := continuous_joint_coordinates (d := d) (T := T) hR
  have hg : Continuous (fun z : (Fin T → Point d) × Point d =>
      Fradin.bernoulliResponse θ (coordinates z.1 R z.2) D) :=
    ((continuous_carmonChainGradient T).comp hz).add
      ((Fradin.continuous_maskedGradient.comp hz).const_smul (Fradin.noiseFactor θ D))
  have he : Continuous (fun z : (Fin T → Point d) × Point d =>
      frameEmbed z.1 (Fradin.bernoulliResponse θ (coordinates z.1 R z.2) D)) :=
    continuous_joint_frameEmbed_apply.comp (continuous_fst.prodMk hg)
  have hj : Continuous (fun z : (Fin T → Point d) × Point d =>
      (fderiv ℝ (softProjection R) z.2).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp
      (((contDiff_softProjection_two hR).fderiv_right (m := 1) (by norm_num)).continuous.comp continuous_snd)
  exact ((hj.clm_apply he).add (continuous_snd.const_smul η)).measurable

theorem response_sub_populationGradient {d T : ℕ} (U : Fin T → Point d)
    (R η : ℝ) (θ : unitInterval) (x : Point d) (D : Bool) :
    response U R η θ x D - populationGradient U R η x =
      transport U R x (Fradin.bernoulliResponse θ (coordinates U R x) D -
        carmonChainGradient (coordinates U R x)) := by
  simp only [response, populationGradient, map_sub]
  abel

theorem response_eq_populationGradient_add_noise {d T : ℕ} (U : Fin T → Point d)
    (R η : ℝ) (θ : unitInterval) (x : Point d) (D : Bool) :
    response U R η θ x D = populationGradient U R η x +
      Fradin.noiseFactor θ D • transport U R x (Fradin.maskedGradient (coordinates U R x)) := by
  simp only [response, populationGradient, Fradin.bernoulliResponse, map_add, map_smul]
  abel

theorem norm_transport_le_one {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (x : Point d) :
    ‖transport U R x‖ ≤ 1 := by
  calc
    _ ≤ ‖(fderiv ℝ (softProjection R) x).adjoint‖ * ‖frameEmbed U‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (by simpa using norm_fderiv_softProjection_le_one hR x)
      (norm_frameEmbed_le_one hU) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem norm_transport_apply_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (x : Point d) (z : Point T) :
    ‖transport U R x z‖ ≤ ‖z‖ := by
  exact ((transport U R x).le_opNorm z).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_transport_le_one hU hR x) (norm_nonneg z))

theorem integral_response {d T : ℕ} (U : Fin T → Point d) (R η : ℝ)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x : Point d) :
    (∫ D, response U R η θ x D ∂Fradin.bernoulliLaw θ) = populationGradient U R η x := by
  change (∫ D, transport U R x (Fradin.bernoulliResponse θ (coordinates U R x) D) +
    η • x ∂Fradin.bernoulliLaw θ) = _
  rw [integral_add (Fradin.integrable_bernoulliLaw θ _) (integrable_const _),
    (transport U R x).integral_comp_comm
      (Fradin.integrable_bernoulliResponse θ (coordinates U R x)),
    Fradin.integral_bernoulliResponse θ hθ, integral_const]
  simp [populationGradient]

theorem integrable_response {d T : ℕ} (U : Fin T → Point d) (R η : ℝ)
    (θ : unitInterval) (x : Point d) :
    Integrable (response U R η θ x) (Fradin.bernoulliLaw θ) :=
  Fradin.integrable_bernoulliLaw θ _

theorem integral_centered_rpow_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x : Point d) {p : ℝ} (hp : 1 ≤ p) :
    (∫ D, ‖response U R η θ x D - populationGradient U R η x‖ ^ p
      ∂Fradin.bernoulliLaw θ) ≤
      2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1) := by
  calc
    _ ≤ ∫ D, ‖Fradin.bernoulliResponse θ (coordinates U R x) D -
        carmonChainGradient (coordinates U R x)‖ ^ p ∂Fradin.bernoulliLaw θ := by
      apply integral_mono (Fradin.integrable_bernoulliLaw θ _)
        (Fradin.integrable_bernoulliLaw θ _)
      intro D
      dsimp only
      rw [response_sub_populationGradient]
      exact Real.rpow_le_rpow (norm_nonneg _) (norm_transport_apply_le hU hR x _) (by linarith)
    _ ≤ _ := Fradin.integral_centered_rpow_le θ hθ _ hp

theorem centered_moment_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (θ : unitInterval) (hθ : 0 < (θ : ℝ)) (x : Point d) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ D, ENNReal.ofReal (‖response U R η θ x D - populationGradient U R η x‖ ^ p)
      ∂Fradin.bernoulliLaw θ) ≤
      ENNReal.ofReal (2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Fradin.integrable_bernoulliLaw θ _)
    (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) _))]
  exact ENNReal.ofReal_le_ofReal (integral_centered_rpow_le hU hR η θ hθ x hp)

end
end HeavyTailedNoise.RandomizedLift
