import HeavyTailedNoise.Upper.K1.KernelBatch

/-!
One whole fresh runtime batch for a fixed source lag.  `kernelPhi P k` is a
single vector-valued transform of each returned residual.  Its high bands
share every response and are never treated as independent random variables.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Given the entire pre-batch history, the centered mean of the shared
`Φ_k` batch is zero. No current response is included in the history. -/
theorem kernelBatch_centered_condExp
    {d : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) (k : ℕ)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x w : History → Point d) (hx : Measurable x) (hw : Measurable w) :
    (historyLaw.prod (freshSeedLaw O P.n))[
      (fun z : History × (Fin P.n → Seed) =>
        upperResidualBatchMean O (kernelPhi P k) (x z.1) (w z.1) z.2 -
          upperResidualSourceMean O (kernelPhi P k) (x z.1) (w z.1)) |
      MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace History)]
      =ᵐ[historyLaw.prod (freshSeedLaw O P.n)] 0 := by
  exact upperResidualBatchMean_centered_condExp O
    (kernelPhi P k) (measurable_kernelPhi P k)
    (kernelPhiBound P k) (fun z => kernelPhi_norm_le P k z)
    historyLaw x w hx hw P.n_pos

/-- The exact shared-source whole-batch variance input for the manuscript:
the right side squares the complete correlated `Φ_k` vector from one seed. -/
theorem kernelBatch_secondMoment_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (k : ℕ) (x w : Point d) :
    (∫ seeds : Fin P.n → Seed,
      ‖upperResidualBatchMean O (kernelPhi P k) x w seeds -
        upperResidualSourceMean O (kernelPhi P k) x w‖ ^ 2
      ∂freshSeedLaw O P.n) ≤
      (P.n : ℝ)⁻¹ * ∫ ξ,
        ‖kernelPhi P k (O.response x ξ - w)‖ ^ 2 ∂O.law := by
  have href := upperResidualBatchMean_secondMoment_le_reference
    (b := P.n) O (kernelPhi P k) (measurable_kernelPhi P k)
    (kernelPhiBound P k) (fun z => kernelPhi_norm_le P k z)
    x w w P.n_pos
  simpa only [sub_self, kernelPhi_zero_input, sub_zero] using href

end

end HeavyTailedNoise.UpperK1
