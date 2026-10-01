import HeavyTailedNoise.Upper.K1.StationarityPhysicalConditional
import HeavyTailedNoise.Upper.K1.StationarityActualInitial

/-!
The physical-schedule risk bound for the one actual run. Its initial point,
runtime steps, query positions, and measurability are discharged by the
logged algorithm path. The remaining average estimator-error bound is an
explicit analytical premise, not an oracle or algorithm assumption.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem Admissible.paperSchedule_risk_le_of_actual_estimator_error
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hchle : ch ≤ 1 / 4)
    (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    ((P.T : ENNReal)⁻¹ *
      (∫⁻ seeds : Fin (responseCount P) → Seed,
        ENNReal.ofReal
          (∑ t ∈ Finset.range P.T,
            ‖actualRuntimeEstimate P I.oracle seeds t -
              I.objective.grad (actualRuntimePoint P I.oracle seeds t)‖)
        ∂freshSeedLaw I.oracle (responseCount P)) ≤
      ENNReal.ofReal (ε / 8)) →
    risk I (algorithm P) ≤ ENNReal.ofReal ε := by
  dsimp only
  intro herror
  let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  exact Admissible.paperSchedule_risk_le_of_average_estimate_error
    I ε Ctail ch κ Cb CI hε hch hchle hCb hCI
    (actualRuntimePoint P I.oracle)
    (actualRuntimeEstimate P I.oracle)
    (actualRuntimePoint_zero P I.oracle)
    (fun seeds t ht => actualRuntimePoint_step P I.oracle seeds t ht)
    (fun seeds r => actualRuntimePoint_eq_canonicalQuery P I.oracle seeds r)
    (measurable_actualRuntimePoint_at P I.oracle)
    herror

end

end HeavyTailedNoise.UpperK1
