import HeavyTailedNoise.Model.Basic

/-!
Moment facts for independent fresh batches in the shared gradient-only oracle model.
The history is sampled before the batch, so a measurable decision based on that history
is fixed when a fresh seed coordinate is integrated. No batch-average decay is claimed.
-/

open MeasureTheory

noncomputable section

namespace HeavyTailedNoise

/-- Each coordinate of an independent fresh batch retains the oracle's centered `p` moment. -/
theorem Admissible.freshBatch_coordinate_centered_moment
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (n : ℕ) (i : Fin n) (x : Point d) :
    (∫⁻ seeds : Fin n → Seed,
      ENNReal.ofReal (‖I.oracle.response x (seeds i) - I.objective.grad x‖ ^ p)
      ∂freshSeedLaw I.oracle n) ≤ ENNReal.ofReal (σ ^ p) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  have hresp : Measurable (I.oracle.response x) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hmoment : Measurable
      (fun ξ : Seed => ENNReal.ofReal (‖I.oracle.response x ξ - I.objective.grad x‖ ^ p)) := by
    fun_prop
  have hpush :=
    (measurePreserving_eval (fun _ : Fin n => I.oracle.law) i).lintegral_comp hmoment
  change (∫⁻ seeds : Fin n → Seed,
      ENNReal.ofReal (‖I.oracle.response x (seeds i) - I.objective.grad x‖ ^ p)
      ∂Measure.pi (fun _ : Fin n => I.oracle.law)) ≤ ENNReal.ofReal (σ ^ p)
  rw [hpush]
  exact I.centered_moment x

/-- A measurable pre-batch decision obeys the same centered moment bound after averaging
its fresh, independent batch coordinate over arbitrary probability-distributed history. -/
theorem Admissible.predictable_freshBatch_coordinate_centered_moment
    {d : ℕ} {Seed History : Type*} [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x : History → Point d) (_hx : Measurable x)
    (n : ℕ) (i : Fin n) :
    (∫⁻ h : History, ∫⁻ seeds : Fin n → Seed,
      ENNReal.ofReal (‖I.oracle.response (x h) (seeds i) - I.objective.grad (x h)‖ ^ p)
      ∂freshSeedLaw I.oracle n ∂historyLaw) ≤ ENNReal.ofReal (σ ^ p) := by
  calc
    (∫⁻ h : History, ∫⁻ seeds : Fin n → Seed,
        ENNReal.ofReal (‖I.oracle.response (x h) (seeds i) - I.objective.grad (x h)‖ ^ p)
        ∂freshSeedLaw I.oracle n ∂historyLaw)
      ≤ ∫⁻ _h : History, ENNReal.ofReal (σ ^ p) ∂historyLaw := by
        apply lintegral_mono
        intro h
        exact I.freshBatch_coordinate_centered_moment n i (x h)
    _ = ENNReal.ofReal (σ ^ p) := by simp

end HeavyTailedNoise
