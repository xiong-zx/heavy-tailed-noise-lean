import HeavyTailedNoise.Probability.RiskProtocolJointLaw
import HeavyTailedNoise.Probability.RiskThreshold
import HeavyTailedNoise.Lower.Gated.HardGaussianInstance
import HeavyTailedNoise.Lower.Gated.HardFrameMeas

/-!
Final risk and quantifier assembly for the exact shared K=1 model.

The frame law is selected from `d,T` before the algorithm. Private randomness
has an arbitrary measurable space, the experiment uses exactly `N` independent
Gaussian coordinates, and the output is the algorithm's unrestricted
response-free decision after those responses. Expected risk may be infinite.

The actual-output probability barrier remains an explicit theorem parameter.
In particular, this file does not assume or prove a stopped conditional law,
real/ideal coupling, or stage-count estimate, and introduces no project axioms.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

/-- A strict actual-output probability barrier on the independent joint
experiment gives the strict fixed-prior average-risk premise. Measurability
and the equality to the exact algorithm risk are proved by the shared protocol.
-/
theorem fixed_joint_gradient_barrier_implies_average_risk
    {d N : ℕ} {Frame Seed Private : Type*}
    [MeasurableSpace Frame] [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ Lbar ε : ℝ}
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (ν : Measure (Fin N → Seed)) [IsProbabilityMeasure ν]
    (I : Frame → Admissible d Seed p q Δ σ Lbar)
    (A : RandomAlgorithm d N Private)
    (hε : 0 < ε)
    (hseed : ∀ U, freshSeedLaw (I U).oracle N = ν)
    (hresponse : Measurable
      (fun z : Frame × (Point d × Seed) =>
        (I z.1).oracle.response z.2.1 z.2.2))
    (hgrad : Measurable
      (fun z : Frame × Point d => (I z.1).objective.grad z.2))
    (hgood : (1 / 2 : ENNReal) <
      (μ.prod (A.privateLaw.prod ν))
        {z : Frame × (Private × (Fin N → Seed)) |
          2 * ε ≤ ‖(I z.1).objective.grad
            (A.output z.2.1
              (runTranscript (I z.1).oracle A z.2.1 N z.2.2))‖}) :
    ENNReal.ofReal ε < ∫⁻ U, risk (I U) A ∂μ := by
  let loss : Frame × (Private × (Fin N → Seed)) → ENNReal :=
    fun z => ENNReal.ofReal ‖(I z.1).objective.grad
      (A.output z.2.1
        (runTranscript (I z.1).oracle A z.2.1 N z.2.2))‖
  have hmeas : Measurable loss :=
    measurable_parametric_riskValue I A hresponse hgrad
  have hset : {z | ENNReal.ofReal (2 * ε) ≤ loss z} =
      {z : Frame × (Private × (Fin N → Seed)) |
        2 * ε ≤ ‖(I z.1).objective.grad
          (A.output z.2.1
            (runTranscript (I z.1).oracle A z.2.1 N z.2.2))‖} := by
    ext z
    exact ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)
  have hthreshold : (1 / 2 : ENNReal) <
      (μ.prod (A.privateLaw.prod ν))
        {z | ENNReal.ofReal (2 * ε) ≤ loss z} := by
    rw [hset]
    exact hgood
  have hbound := lintegral_gt_half_threshold
    (μ.prod (A.privateLaw.prod ν)) loss hmeas.aemeasurable
    (by positivity : ENNReal.ofReal (2 * ε) ≠ 0)
    ENNReal.ofReal_ne_top hthreshold
  have hhalf : ENNReal.ofReal (2 * ε) * (1 / 2 : ENNReal) =
      ENNReal.ofReal ε := by
    rw [← show ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ε)]
    congr 1
    ring
  rw [hhalf] at hbound
  rw [average_risk_eq_joint_product μ ν I A hseed hresponse hgrad]
  exact hbound

/-- Only packages the existing legal hard-instance constructor with the
proof carried by an orthonormal-frame value. The objective and oracle are
exactly those of `hardGaussianAdmissible`. -/
def hardGaussianFrameFamily
    {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    {p q L ε Δ σ : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (hbudget : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ)
    (U : {v : Fin T → Point d // Orthonormal ℝ v}) :
    Admissible d (Point d) p q Δ σ L :=
  hardGaussianAdmissible hd hT U.1 U.2 hp hq hL hε hΔ hσ hbudget

section HardGaussian

variable {d T N : ℕ} {p q L ε Δ σ : ℝ}
variable (hd : 0 < d) (hT : 0 < T)
variable (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
variable (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
variable (hbudget : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ)

local notation "HardFrame" => {v : Fin T → Point d // Orthonormal ℝ v}
local notation "Ihard" =>
  hardGaussianFrameFamily hd hT hp hq hL hε hΔ hσ hbudget

/-- The hard Gaussian family has one common fresh seed law, jointly measurable
response and gradient fields. These inputs are discharged, not hypothesized.
-/
theorem hardGaussianFrameFamily_joint_inputs :
    (∀ U : HardFrame, freshSeedLaw (Ihard U).oracle N =
      Measure.pi (fun _ : Fin N => standardGaussianLaw d)) ∧
    Measurable (fun z : HardFrame × (Point d × Point d) =>
      (Ihard z.1).oracle.response z.2.1 z.2.2) ∧
    Measurable (fun z : HardFrame × Point d =>
      (Ihard z.1).objective.grad z.2) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · exact measurable_gaussianResponse_on_orthonormalFrames hT hL hε
  · exact measurable_scaledGradient_on_orthonormalFrames hT hL hε

/-- The precise remaining stochastic input is an event in the actual
full-history experiment, including its arbitrary unqueried output. -/
theorem hardGaussian_fixed_Haar_barrier_implies_average
    (hTd : T ≤ d)
    {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm d N Private)
    (hgood : (1 / 2 : ENNReal) <
      ((preselectedOrthonormalFrameLaw d T hTd).prod
        (A.privateLaw.prod
          (Measure.pi (fun _ : Fin N => standardGaussianLaw d))))
        {z : HardFrame × (Private × (Fin N → Point d)) |
          2 * ε ≤ ‖(Ihard z.1).objective.grad
            (A.output z.2.1
              (runTranscript (Ihard z.1).oracle A z.2.1 N z.2.2))‖}) :
    ENNReal.ofReal ε <
      ∫⁻ U, risk (Ihard U) A ∂preselectedOrthonormalFrameLaw d T hTd := by
  obtain ⟨hseed, hresponse, hgrad⟩ :=
    hardGaussianFrameFamily_joint_inputs (N := N)
      hd hT hp hq hL hε hΔ hσ hbudget
  exact fixed_joint_gradient_barrier_implies_average_risk
    (preselectedOrthonormalFrameLaw d T hTd)
    (Measure.pi (fun _ : Fin N => standardGaussianLaw d))
    Ihard A hε hseed hresponse hgrad hgood

universe u

/-- One fixed preselected Haar average-risk premise gives a deterministic
legal hard instance for every algorithm, and refutes the manuscript's
dimension-uniform minimax guarantee. The frame may depend on the algorithm's
rule, never on one realized private/noise tape. -/
theorem hardGaussian_fixed_Haar_average_refutes_minimax
    (hTd : T ≤ d)
    (haverage : ∀ (Private : Type u) (privateSpace : MeasurableSpace Private)
      (A : @RandomAlgorithm d N Private privateSpace),
      ENNReal.ofReal ε <
        ∫⁻ U, @risk d N (Point d) inferInstance Private privateSpace
          p q Δ σ L (Ihard U) A ∂preselectedOrthonormalFrameLaw d T hTd) :
    (∀ (Private : Type u) (privateSpace : MeasurableSpace Private)
      (A : @RandomAlgorithm d N Private privateSpace),
      ∃ U : HardFrame,
        ENNReal.ofReal ε <
          @risk d N (Point d) inferInstance Private privateSpace
            p q Δ σ L (Ihard U) A) ∧
    ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ L ε := by
  constructor
  · intro Private privateSpace A
    let : MeasurableSpace Private := privateSpace
    exact bad_orientation_of_average
      (preselectedOrthonormalFrameLaw d T hTd) Ihard A
      (haverage Private privateSpace A)
  · exact fixed_average_refutes_dimension_uniform_guarantee
      hd (preselectedOrthonormalFrameLaw d T hTd) Ihard haverage

/-- End-to-end closure from the explicit actual-output barrier, with the same
Haar law preceding *all* algorithms and arbitrary measurable private sources.
No stopped conditional-law or probability estimate is hidden in this theorem.
-/
theorem hardGaussian_fixed_Haar_barrier_refutes_minimax
    (hTd : T ≤ d)
    (hgood : ∀ (Private : Type u) (privateSpace : MeasurableSpace Private)
      (A : @RandomAlgorithm d N Private privateSpace),
      (1 / 2 : ENNReal) <
        ((preselectedOrthonormalFrameLaw d T hTd).prod
          (A.privateLaw.prod
            (Measure.pi (fun _ : Fin N => standardGaussianLaw d))))
          {z : HardFrame × (Private × (Fin N → Point d)) |
            2 * ε ≤ ‖(Ihard z.1).objective.grad
              (A.output z.2.1
                (runTranscript (Ihard z.1).oracle A z.2.1 N z.2.2))‖}) :
    (∀ (Private : Type u) (privateSpace : MeasurableSpace Private)
      (A : @RandomAlgorithm d N Private privateSpace),
      ∃ U : HardFrame,
        ENNReal.ofReal ε <
          @risk d N (Point d) inferInstance Private privateSpace
            p q Δ σ L (Ihard U) A) ∧
    ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ L ε := by
  apply hardGaussian_fixed_Haar_average_refutes_minimax
    hd hT hp hq hL hε hΔ hσ hbudget hTd
  intro Private privateSpace A
  let : MeasurableSpace Private := privateSpace
  exact hardGaussian_fixed_Haar_barrier_implies_average
    hd hT hp hq hL hε hΔ hσ hbudget hTd A
      (hgood Private privateSpace A)

end HardGaussian

end

end HeavyTailedNoise
