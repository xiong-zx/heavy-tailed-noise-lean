import HeavyTailedNoise.Model.Basic

/-!
Algorithm-independent strict-K=1 batch interface. One fresh seed contributes
exactly one returned gradient vector; deterministic reuse of that vector does
not make a second oracle query. This file does not encode an EMA update or
choose its batch size.
-/

namespace HeavyTailedNoise

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The `i`th batch coordinate queries the oracle once, at the pre-batch
decision `x`, with only the `i`th fresh seed. -/
def upperBatchResponses {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (x : Point d) (seeds : Fin b → Seed) :
    Fin b → Point d := fun i => O.response x (seeds i)

theorem measurable_upperBatchResponses
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) (x : History → Point d)
    (hx : Measurable x) :
    Measurable (fun z : History × (Fin b → Seed) =>
      upperBatchResponses O (x z.1) z.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact O.measurable_response.comp
    ((hx.comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

/-- Arithmetic mean of the returned batch, defined for every size; the
unbiasedness theorem below requires a nonempty batch. -/
def upperBatchMean {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (x : Point d) (seeds : Fin b → Seed) : Point d :=
  (b : ℝ)⁻¹ • ∑ i : Fin b, O.response x (seeds i)

theorem measurable_upperBatchMean
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) (x : History → Point d)
    (hx : Measurable x) :
    Measurable (fun z : History × (Fin b → Seed) =>
      upperBatchMean O (x z.1) z.2) := by
  have hresponse := measurable_upperBatchResponses (b := b) O x hx
  unfold upperBatchMean
  have hsum : Measurable (fun z : History × (Fin b → Seed) =>
      ∑ i : Fin b, O.response (x z.1) (z.2 i)) := by
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_apply i).comp hresponse
  exact (measurable_const : Measurable
    (fun _ : History × (Fin b → Seed) => (b : ℝ)⁻¹)).smul hsum

theorem upperBatchMean_integrable
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (x : Point d)
    (hInt : Integrable (O.response x) O.law) :
    Integrable (upperBatchMean O x)
      (Measure.pi (fun _ : Fin b => O.law)) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  have hsum : Integrable
      (fun seeds : Fin b → Seed => ∑ i : Fin b, O.response x (seeds i))
      (Measure.pi (fun _ : Fin b => O.law)) := by
    apply integrable_finset_sum
    intro i hi
    exact integrable_comp_eval hInt
  have hfun : ((b : ℝ)⁻¹ •
      (fun seeds : Fin b → Seed => ∑ i : Fin b, O.response x (seeds i))) =
      upperBatchMean O x := by
    funext seeds
    rfl
  rw [← hfun]
  exact hsum.smul (b : ℝ)⁻¹

/-- Fixed-decision unbiasedness of the one-response-per-seed batch mean. -/
theorem upperBatchMean_unbiased
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (x g : Point d) (hb : 0 < b)
    (hInt : Integrable (O.response x) O.law)
    (hUnbiased : (∫ ξ, O.response x ξ ∂O.law) = g) :
    (∫ seeds : Fin b → Seed, upperBatchMean O x seeds
      ∂Measure.pi (fun _ : Fin b => O.law)) = g := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  have hcoord (i : Fin b) : Integrable
      (fun seeds : Fin b → Seed => O.response x (seeds i))
      (Measure.pi (fun _ : Fin b => O.law)) :=
    integrable_comp_eval hInt
  calc
    (∫ seeds : Fin b → Seed, upperBatchMean O x seeds
        ∂Measure.pi (fun _ : Fin b => O.law)) =
        (b : ℝ)⁻¹ •
          ∫ seeds : Fin b → Seed, ∑ i : Fin b, O.response x (seeds i)
            ∂Measure.pi (fun _ : Fin b => O.law) := by
              change (∫ seeds : Fin b → Seed,
                (b : ℝ)⁻¹ • ∑ i : Fin b, O.response x (seeds i)
                  ∂Measure.pi (fun _ : Fin b => O.law)) = _
              rw [integral_smul]
    _ = (b : ℝ)⁻¹ •
        ∑ i : Fin b, ∫ seeds : Fin b → Seed, O.response x (seeds i)
          ∂Measure.pi (fun _ : Fin b => O.law) := by
            rw [integral_finsetSum]
            intro i hi
            exact hcoord i
    _ = (b : ℝ)⁻¹ • ∑ _i : Fin b, g := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_comp_eval hInt.aestronglyMeasurable, hUnbiased]
    _ = g := by
      have hbReal : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
      simp only [Finset.sum_const, Finset.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℝ b g, smul_smul,
        inv_mul_cancel₀ hbReal, one_smul]

end

end HeavyTailedNoise
