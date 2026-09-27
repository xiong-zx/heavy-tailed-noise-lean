import HeavyTailedNoise.Lower.Gated.HardGaussianFailureProbability
import HeavyTailedNoise.Lower.Gated.LowerRiskProbabilityBudget
import HeavyTailedNoise.Probability.PrivateEventMixture

/-!
The same fixed Haar average-risk lower bound from the actual ideal completion
tail for every fixed private tape. Private is an arbitrary measurable space;
its original law is integrated by a product-measure calculation.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

theorem hardGaussian_average_risk_gt_of_completion_tail
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hd : 0 < d) (hT : 0 < T) (hT64 : 64 ≤ T) (hTd : T ≤ d)
    (hDim : 4096 * (hardRadius T) ^ 2 ≤ ((d - T : ℕ) : ℝ))
    (hAcc : 2 * (N + 2 : ℕ) * T *
      Real.exp (-((d - T : ℕ) : ℝ) / (2048 * (hardRadius T) ^ 2)) ≤ (1 / 10 : ℝ))
    {p q L ε Δ σ : ℝ} (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (hbudget : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ)
    (A : RandomAlgorithm d N Private)
    (hcompletion : ∀ r : Private,
      (((preselectedOrthonormalFrameLaw d T hTd).prod
        (Measure.pi (fun _ : Fin N => standardGaussianLaw d))).real
        {z : IdealAccidentSample d T N |
          idealCompleted hT z.1.1
            (rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A) r z.2
            (σ / ((80 * ε) * Real.sqrt d))}) ≤ Real.exp (-(T : ℝ) / 32)) :
    ENNReal.ofReal ε < ∫⁻ U,
      risk (hardGaussianFrameFamily hd hT hp hq hL hε hΔ hσ hbudget U) A
      ∂preselectedOrthonormalFrameLaw d T hTd := by
  let : IsProbabilityMeasure A.privateLaw := A.private_probability
  let μ := preselectedOrthonormalFrameLaw d T hTd
  let ν := Measure.pi (fun _ : Fin N => standardGaussianLaw d)
  let I := hardGaussianFrameFamily hd hT hp hq hL hε hΔ hσ hbudget
  let P := μ.prod (A.privateLaw.prod ν)
  let loss : {U : Fin T → Point d // Orthonormal ℝ U} ×
      (Private × (Fin N → Point d)) → ENNReal :=
    fun z => ENNReal.ofReal ‖(I z.1).objective.grad
      (A.output z.2.1 (runTranscript (I z.1).oracle A z.2.1 N z.2.2))‖
  obtain ⟨hseed, hresponse, hgrad⟩ := hardGaussianFrameFamily_joint_inputs
    (N := N) hd hT hp hq hL hε hΔ hσ hbudget
  have hmeas : Measurable loss :=
    measurable_parametric_riskValue I A hresponse hgrad
  let E := {z | loss z < ENNReal.ofReal (2 * ε)}
  have hE : MeasurableSet E := measurableSet_lt hmeas measurable_const
  have hfixed (r : Private) : (μ.prod ν)
      {z : IdealAccidentSample d T N | (z.1, (r, z.2)) ∈ E} ≤
        ENNReal.ofReal (7 / 20 : ℝ) := by
    have hset : {z : IdealAccidentSample d T N | (z.1, (r, z.2)) ∈ E} =
        {z : IdealAccidentSample d T N |
          ‖(I z.1).objective.grad
            (A.output r (runTranscript (I z.1).oracle A r N z.2))‖ < 2 * ε} := by
      ext z
      exact ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * ε)
    rw [hset]
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (by norm_num : (0 : ℝ) ≤ 7 / 20)).2
    have hf := hardGaussian_smallOutput_probability_le hd hT hTd hDim hp hq
      hL hε hΔ hσ hbudget A r (Real.exp (-(T : ℝ) / 32)) (hcompletion r)
    have hnum := gated_completion_exp_le_quarter hT64
    exact hf.trans (by linarith)
  have hbad : P E ≤ ENNReal.ofReal (7 / 20 : ℝ) :=
    private_mixture_event_le μ A.privateLaw ν E hE _ hfixed
  have hbadReal : P.real E ≤ (7 / 20 : ℝ) :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) hbad
  have hgoodReal : (1 / 2 : ℝ) < P.real Eᶜ := by
    rw [measureReal_compl hE]
    have htotal : P.real Set.univ = 1 := by simp
    rw [htotal]
    linarith
  have hgood : (1 / 2 : ENNReal) < P Eᶜ :=
    (ENNReal.toReal_lt_toReal (by norm_num) (measure_ne_top _ _)).1
      (by simpa only [ENNReal.toReal_div, ENNReal.toReal_one,
        ENNReal.toReal_ofNat, measureReal_def] using hgoodReal)
  have hgoodSet :
      {z : {U : Fin T → Point d // Orthonormal ℝ U} ×
          (Private × (Fin N → Point d)) |
        2 * ε ≤ ‖(I z.1).objective.grad
          (A.output z.2.1 (runTranscript (I z.1).oracle A z.2.1 N z.2.2))‖} = Eᶜ := by
    ext z
    simp only [E, loss, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * ε), not_lt]
  apply fixed_joint_gradient_barrier_implies_average_risk μ ν I A hε
    hseed hresponse hgrad
  rw [hgoodSet]
  exact hgood

end

end HeavyTailedNoise
