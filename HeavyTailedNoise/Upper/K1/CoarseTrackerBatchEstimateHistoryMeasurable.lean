import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchEstimateMeasurable

/-!
The completed estimate is jointly measurable in the complete pre-batch
history and a fresh independent response block. The estimator itself is the
single function defined in `CoarseTrackerBatchEstimateMeasurable`.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem measurable_batchEstimateOnHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (u : Fin P.T) :
    Measurable (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
      batchEstimateOnHistory P O u z.1 z.2) := by
  have hstate : Measurable (fun H : BatchHistory P d u =>
      stateAt P (batchStart P u.val) H.2) :=
    (measurable_stateAt P (batchStart P u.val)).comp measurable_snd
  have hresponse : Measurable
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        upperBatchResponses O (batchDecision P u z.1) z.2) :=
    measurable_upperBatchResponses O (batchDecision P u)
      (measurable_batchDecision P u)
  have hpair : Measurable
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        (stateAt P (batchStart P u.val) z.1.2,
          upperBatchResponses O (batchDecision P u z.1) z.2)) :=
    (hstate.comp measurable_fst).prodMk hresponse
  have hcompose := (measurable_batchEstimateFromResponses P u).comp hpair
  simpa only [Function.comp_def, batchEstimateOnHistory] using hcompose

end

end HeavyTailedNoise.UpperK1
