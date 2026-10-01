import HeavyTailedNoise.Upper.K1.StationarityPhysicalBudget

/-!
Conditional expected stationarity under the literal manuscript schedule.
The physical horizon and step-size budget are discharged here. The actual
path identification and the average completed-estimator error remain explicit
inputs for the subsequent upper-rate theorem.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem Admissible.paperSchedule_risk_le_of_average_estimate_error
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hchle : ch ≤ 1 / 4)
    (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    ∀ (x hhat : (Fin (responseCount P) → Seed) → ℕ → Point d),
      (∀ seeds, x seeds 0 = 0) →
      (∀ seeds (t : ℕ), t < P.T →
        x seeds (t + 1) = x seeds t - P.h • direction (hhat seeds t)) →
      (∀ seeds (r : Fin P.T),
        x seeds r.val = canonicalRuntimePoint P I.oracle r seeds) →
      (∀ r : Fin P.T, Measurable (fun seeds => x seeds r.val)) →
      ((P.T : ENNReal)⁻¹ *
        (∫⁻ seeds : Fin (responseCount P) → Seed,
          ENNReal.ofReal
            (∑ t ∈ Finset.range P.T,
              ‖hhat seeds t - I.objective.grad (x seeds t)‖)
          ∂freshSeedLaw I.oracle (responseCount P)) ≤
        ENNReal.ofReal (ε / 8)) →
      risk I (algorithm P) ≤ ENNReal.ofReal ε := by
  dsimp only
  intro x hhat hx0 hstep hxQuery hxMeas herror
  let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  have hh : 0 < P.h := by
    dsimp [P, paperSchedule, paperStep]
    exact div_pos (mul_pos hch hε) I.Lbar_pos
  have hK : 0 ≤ (P.T : ℝ) * ε / 2 := by positivity
  have hdescent : Δ + (P.T : ℝ) * Lbar * P.h ^ 2 ≤
      P.h * ((P.T : ℝ) * ε / 2) := by
    simpa only [P, paperSchedule] using
      paperStep_descent_budget I.Lbar_pos hε hch hchle
  have hbudget : (P.T : ENNReal)⁻¹ *
        ENNReal.ofReal ((P.T : ℝ) * ε / 2) +
      2 * ENNReal.ofReal (ε / 8) ≤ ENNReal.ofReal ε :=
    stationarity_uniform_ratio_budget (T := P.T) P.T_pos hε.le
  exact Admissible.risk_le_of_average_estimate_error P I
    hε hh hK hdescent hbudget x hhat hx0 hstep hxQuery hxMeas herror

end

end HeavyTailedNoise.UpperK1
