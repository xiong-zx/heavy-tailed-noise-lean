import HeavyTailedNoise.Model.ParametricProtocol
import HeavyTailedNoise.Probability.RiskJointTonelli

/-!
Joint-law form of the exact full-history algorithm risk. The hidden frame is
integrated outside the arbitrary private tape and the `N` fresh seeds; no
algorithm observation of those hidden variables is introduced.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

theorem average_risk_eq_joint_product
    {d N : ℕ} {Frame Seed Private : Type*}
    [MeasurableSpace Frame] [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ Lbar : ℝ}
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (ν : Measure (Fin N → Seed)) [IsProbabilityMeasure ν]
    (I : Frame → Admissible d Seed p q Δ σ Lbar)
    (A : RandomAlgorithm d N Private)
    (hseed : ∀ U, freshSeedLaw (I U).oracle N = ν)
    (hresponse : Measurable
      (fun z : Frame × (Point d × Seed) =>
        (I z.1).oracle.response z.2.1 z.2.2))
    (hgrad : Measurable
      (fun z : Frame × Point d => (I z.1).objective.grad z.2)) :
    (∫⁻ U, risk (I U) A ∂μ) =
      ∫⁻ z : Frame × (Private × (Fin N → Seed)),
        ENNReal.ofReal ‖(I z.1).objective.grad
          (A.output z.2.1
            (runTranscript (I z.1).oracle A z.2.1 N z.2.2))‖
        ∂μ.prod (A.privateLaw.prod ν) := by
  letI : IsProbabilityMeasure A.privateLaw := A.private_probability
  let loss : Frame → Private → (Fin N → Seed) → ENNReal :=
    fun U r seeds => ENNReal.ofReal ‖(I U).objective.grad
      (A.output r (runTranscript (I U).oracle A r N seeds))‖
  have hmeas : Measurable
      (fun z : Frame × (Private × (Fin N → Seed)) =>
        loss z.1 z.2.1 z.2.2) :=
    measurable_parametric_riskValue I A hresponse hgrad
  change (∫⁻ U, ∫⁻ r, ∫⁻ seeds,
    loss U r seeds ∂freshSeedLaw (I U).oracle N ∂A.privateLaw ∂μ) =
      ∫⁻ z : Frame × (Private × (Fin N → Seed)),
        loss z.1 z.2.1 z.2.2 ∂μ.prod (A.privateLaw.prod ν)
  simp_rw [hseed]
  exact lintegral_frame_private_seed_eq_joint μ A.privateLaw ν loss hmeas

end

end HeavyTailedNoise
