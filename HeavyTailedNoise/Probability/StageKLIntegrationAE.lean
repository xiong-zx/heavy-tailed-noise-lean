import HeavyTailedNoise.Probability.StageKLIntegration
import HeavyTailedNoise.Probability.StageAzumaAE

/-!
The stopped-stage tail implication with almost-everywhere conditional-mean
identification. This is the version usable with ordinary conditional
expectations; it keeps the deterministic response horizon.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem completion_tail_of_stage_pinhole_ae
    {Ω Prefix EventSpace : Type*}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    [MeasurableSpace EventSpace]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (T n₀ : ℕ) (hn₀ : 0 < n₀)
    (length : Ω → Fin T → ℕ) (X Y : ℕ → Ω → ℝ)
    (complete : Set Ω)
    (hbudget : ∀ ω ∈ complete,
      4 * (∑ j, length ω j) ≤ T * n₀)
    (hindicator : ∀ ω,
      (∑ i ∈ Finset.range T, X i ω) =
        ((Finset.univ.filter fun j : Fin T => length ω j ≤ n₀).card : ℝ))
    (Pstage : ℕ → Prefix → Measure EventSpace)
    (Estage : ℕ → Prefix → Set EventSpace)
    (stoppedPrefix : ℕ → Ω → Prefix)
    (hshort : ∀ i < T, ∀ s,
      (Pstage i s (Estage i s)).toReal ≤ 1 / 2)
    (hcenter : ∀ i < T, ∀ᵐ ω ∂μ,
      X i ω ≤ (Pstage i (stoppedPrefix i ω)
        (Estage i (stoppedPrefix i ω))).toReal + Y i ω)
    (h_adapted : StronglyAdapted ℱ Y)
    (h₀ : HasSubgaussianMGF (Y 0) 1 μ)
    (h_cond : ∀ i < T - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) 1 μ) :
    μ.real complete ≤ Real.exp (-(T : ℝ) / 32) := by
  have hdom : ∀ i < T, ∀ᵐ ω ∂μ,
      X i ω ≤ (1 : ℝ) / 2 + Y i ω := by
    intro i hi
    filter_upwards [hcenter i hi] with ω hω
    exact hω.trans
      (add_le_add_left (hshort i hi (stoppedPrefix i ω)) _)
  exact (measureReal_mono
    (completion_forces_short_indicator_sum T n₀ hn₀ length X complete
      hbudget hindicator)).trans
    (stage_count_tail_of_subgaussian_domination_ae μ ℱ X Y T
      h_adapted h₀ h_cond hdom)

end

end HeavyTailedNoise
