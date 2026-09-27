import HeavyTailedNoise.Lower.Gated.ScaledOutputFailure
import HeavyTailedNoise.Lower.Gated.IdealQueryJointMeas
import HeavyTailedNoise.Lower.Gated.LowerBoundMinimaxAssembly

/-!
Actual scaled-output failure probability, with the ideal completion tail
as the single remaining stochastic input. The accident estimate is supplied
by the checked same-prior theorem, not an independent hypothesis.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

theorem hardGaussian_smallOutput_probability_le
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hd : 0 < d) (hT : 0 < T) (hTd : T ≤ d)
    (hDim : 4096 * (hardRadius T) ^ 2 ≤ ((d - T : ℕ) : ℝ))
    {p q L ε Δ σ : ℝ} (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (hbudget : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ)
    (A : RandomAlgorithm d N Private) (r : Private)
    (β : ℝ)
    (hcompletion :
      (((preselectedOrthonormalFrameLaw d T hTd).prod
        (Measure.pi (fun _ : Fin N => standardGaussianLaw d))).real
        {z : IdealAccidentSample d T N |
          idealCompleted hT z.1.1
            (rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A) r z.2
            (σ / ((80 * ε) * Real.sqrt d))}) ≤ β) :
    (((preselectedOrthonormalFrameLaw d T hTd).prod
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d))).real
      {z : IdealAccidentSample d T N |
        ‖(hardGaussianFrameFamily hd hT hp hq hL hε hΔ hσ hbudget z.1).objective.grad
          (A.output r (runTranscript
            (hardGaussianFrameFamily hd hT hp hq hL hε hΔ hσ hbudget z.1).oracle
            A r N z.2))‖ < 2 * ε}) ≤
      β + 2 * (N + 2 : ℕ) * T *
        Real.exp (-((d - T : ℕ) : ℝ) / (2048 * (hardRadius T) ^ 2)) := by
  let P := (preselectedOrthonormalFrameLaw d T hTd).prod
    (Measure.pi (fun _ : Fin N => standardGaussianLaw d))
  let B := rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A
  let a := σ / ((80 * ε) * Real.sqrt d)
  let C : Set (IdealAccidentSample d T N) :=
    {z | idealCompleted hT z.1.1 B r z.2 a}
  let E : Set (IdealAccidentSample d T N) :=
    {z | ∃ t ≤ N, idealPrefixAccidentAt hT z.1.1 B r z.2 a t}
  have hsubset :
      {z : IdealAccidentSample d T N |
        ‖(hardGaussianFrameFamily hd hT hp hq hL hε hΔ hσ hbudget z.1).objective.grad
          (A.output r (runTranscript
            (hardGaussianFrameFamily hd hT hp hq hL hε hΔ hσ hbudget z.1).oracle
            A r N z.2))‖ < 2 * ε} ⊆ C ∪ E := by
    intro z hz
    exact hardGaussian_smallOutput_implies_completion_or_horizon_accident
      hd hT z.1.1 z.1.2 hp hq hL hε hΔ hσ hbudget A r z.2 hz
  have hacc : P.real E ≤ 2 * (N + 2 : ℕ) * T *
      Real.exp (-((d - T : ℕ) : ℝ) / (2048 * (hardRadius T) ^ 2)) :=
    idealPrefixAccident_horizon_probability hT hTd hDim B r a
  exact (measureReal_mono hsubset).trans
    ((measureReal_union_le C E).trans (add_le_add hcompletion hacc))

end

end HeavyTailedNoise
