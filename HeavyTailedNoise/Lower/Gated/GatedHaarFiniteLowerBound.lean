import HeavyTailedNoise.Lower.Gated.IdealHaarCompletionBound
import HeavyTailedNoise.Lower.Gated.HardGaussianAverageFromCompletion
import HeavyTailedNoise.Lower.Gated.GatedPublicParameters

/-!
Public finite-q strict-K=1 lower-bound entry point. T, d and the entire Haar
family are fixed from L, Δ, ε, σ, N before the arbitrary randomized algorithm.
No conditional-law, mean, concentration, or event-probability premise is left.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

set_option autoImplicit false

def gatedHaarPhysicalFamily
    {p q L Δ ε σ : ℝ} (N : ℕ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσε : ε ≤ σ)
    (hT64 : 64 ≤ gatedChainLength (L * Δ / ε ^ 2))
    (U : {v : Fin (gatedChainLength (L * Δ / ε ^ 2)) →
      Point (gatedFullDimensionChoice (gatedChainLength (L * Δ / ε ^ 2)) N (σ / ε)) //
        Orthonormal ℝ v}) :
    Admissible
      (gatedFullDimensionChoice (gatedChainLength (L * Δ / ε ^ 2)) N (σ / ε))
      (Point (gatedFullDimensionChoice (gatedChainLength (L * Δ / ε ^ 2)) N (σ / ε)))
      p q Δ σ L := by
  let T := gatedChainLength (L * Δ / ε ^ 2)
  have hT : 0 < T := by dsimp [T]; omega
  have hd := (gatedFullDimensionChoice_basic T N (σ / ε)).1
  have hσ : 0 ≤ σ := hε.le.trans hσε
  have hgap : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ := by
    dsimp [T]
    rw [gatedChainLength_eq_physical_floor]
    exact gatedChainLength_budget L ε Δ hL hε hΔ.le
  exact hardGaussianFrameFamily hd hT hp hq hL hε hΔ hσ hgap U

theorem gatedHaar_fixed_prior_average_risk_lower_bound
    {p q L Δ ε σ : ℝ} (N : ℕ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσε : ε ≤ σ)
    (hT64 : 64 ≤ gatedChainLength (L * Δ / ε ^ 2))
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * ((σ / ε) / 80) ^ 2 / (16 * 300 ^ 2)))
    (hN : (N : ℝ) ≤ gatedPublicRateConstant * (L * Δ / ε ^ 2) * (σ / ε) ^ 2)
    {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm
      (gatedFullDimensionChoice (gatedChainLength (L * Δ / ε ^ 2)) N (σ / ε)) N Private) :
    let T := gatedChainLength (L * Δ / ε ^ 2)
    let d := gatedFullDimensionChoice T N (σ / ε)
    let hTd : T ≤ d := by
      have hdim := (gatedFullDimensionChoice_basic T N (σ / ε)).2.1
      omega
    ENNReal.ofReal ε < ∫⁻ U,
      risk (gatedHaarPhysicalFamily N hp hq hL hΔ hε hσε hT64 U) A
      ∂preselectedOrthonormalFrameLaw d T hTd := by
  dsimp only
  let T := gatedChainLength (L * Δ / ε ^ 2)
  let S := σ / ε
  let d := gatedFullDimensionChoice T N S
  obtain ⟨hApos, hT, hfloor, hgap, hS1, hS, hamp, hd, hdim, hNd, hm2,
      hlog, haccdim, hacc, hdecision, hresponse⟩ :=
    gatedPublicParameters L Δ ε σ N hL hΔ hε hσε hT64 hlarge hN
  have hTd : T ≤ d := by
    change 2 * T ≤ d at hdim
    omega
  have hσ : 0 ≤ σ := hε.le.trans hσε
  have hcompletion (r : Private) :
      (((preselectedOrthonormalFrameLaw d T hTd).prod
        (Measure.pi (fun _ : Fin N => standardGaussianLaw d))).real
        {z : IdealAccidentSample d T N |
          idealCompleted hT z.1.1
            (rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A) r z.2
            (σ / ((80 * ε) * Real.sqrt d))}) ≤ Real.exp (-(T : ℝ) / 32) := by
    have hc := idealHaar_completion_probability_bound hT hdim hS hlarge hlog hresponse
      (rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A) r
    simpa only [hamp] using hc
  have hmain := hardGaussian_average_risk_gt_of_completion_tail
    hd hT hT64 hTd haccdim hacc hp hq hL hε hΔ hσ hgap A hcompletion
  simpa only [gatedHaarPhysicalFamily] using hmain

theorem gatedHaar_bad_legal_instance
    {p q L Δ ε σ : ℝ} (N : ℕ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσε : ε ≤ σ)
    (hT64 : 64 ≤ gatedChainLength (L * Δ / ε ^ 2))
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * ((σ / ε) / 80) ^ 2 / (16 * 300 ^ 2)))
    (hN : (N : ℝ) ≤ gatedPublicRateConstant * (L * Δ / ε ^ 2) * (σ / ε) ^ 2)
    {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm
      (gatedFullDimensionChoice (gatedChainLength (L * Δ / ε ^ 2)) N (σ / ε)) N Private) :
    ∃ U, ENNReal.ofReal ε <
      risk (gatedHaarPhysicalFamily N hp hq hL hΔ hε hσε hT64 U) A := by
  let T := gatedChainLength (L * Δ / ε ^ 2)
  let d := gatedFullDimensionChoice T N (σ / ε)
  have hTd : T ≤ d := by
    have hdim := (gatedFullDimensionChoice_basic T N (σ / ε)).2.1
    omega
  exact bad_orientation_of_average (preselectedOrthonormalFrameLaw d T hTd)
    (gatedHaarPhysicalFamily N hp hq hL hΔ hε hσε hT64) A
    (gatedHaar_fixed_prior_average_risk_lower_bound
      N hp hq hL hΔ hε hσε hT64 hlarge hN A)

universe u

theorem gatedHaar_refutes_dimension_uniform_guarantee
    {p q L Δ ε σ : ℝ} (N : ℕ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσε : ε ≤ σ)
    (hT64 : 64 ≤ gatedChainLength (L * Δ / ε ^ 2))
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * ((σ / ε) / 80) ^ 2 / (16 * 300 ^ 2)))
    (hN : (N : ℝ) ≤ gatedPublicRateConstant * (L * Δ / ε ^ 2) * (σ / ε) ^ 2) :
    ¬ HasDimensionUniformGuarantee.{u, 0} N p q Δ σ L ε := by
  let T := gatedChainLength (L * Δ / ε ^ 2)
  let d := gatedFullDimensionChoice T N (σ / ε)
  have hd : 0 < d := (gatedFullDimensionChoice_basic T N (σ / ε)).1
  have hTd : T ≤ d := by
    have hdim := (gatedFullDimensionChoice_basic T N (σ / ε)).2.1
    omega
  apply fixed_average_refutes_dimension_uniform_guarantee hd
    (preselectedOrthonormalFrameLaw d T hTd)
    (gatedHaarPhysicalFamily N hp hq hL hΔ hε hσε hT64)
  intro Private privateSpace A
  let : MeasurableSpace Private := privateSpace
  exact gatedHaar_fixed_prior_average_risk_lower_bound
    N hp hq hL hΔ hε hσε hT64 hlarge hN A

end

end HeavyTailedNoise
