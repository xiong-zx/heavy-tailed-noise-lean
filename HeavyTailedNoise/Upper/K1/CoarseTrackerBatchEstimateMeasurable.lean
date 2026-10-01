import HeavyTailedNoise.Upper.K1.CoarseTrackerFullBatch

/-!
Measurability of the unique completed-batch estimate, first as a function of
one state and returned-vector block, then as a function of pre-batch history
and independent fresh seeds. The oracle is evaluated only at the frozen
pre-batch decision.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem measurable_batchEstimateFromResponses {d : ℕ} (u : Fin P.T) :
    Measurable (fun z : State d P.J × (Fin P.n → Point d) =>
      batchEstimateFromResponses P u z.1 z.2) := by
  let k := P.n - 1
  let pre : State d P.J × (Fin P.n → Point d) → State d P.J := fun z =>
    foldResponses P (batchStart P u.val) z.1 k
      (fun i : Fin k => z.2 (prefixResponseIndex P i))
  let last : State d P.J × (Fin P.n → Point d) → Point d := fun z =>
    z.2 (lastResponseIndex P)
  let accumulated : State d P.J × (Fin P.n → Point d) →
      Point d × (Fin P.J → Point d) := fun z =>
    accumulateResponse P (pre z) (last z)
  let updated : State d P.J × (Fin P.n → Point d) → Fin P.J → Point d :=
    fun z => updatedBands P (pre z) (accumulated z).2
  have hprefix : Measurable
      (fun z : State d P.J × (Fin P.n → Point d) =>
        (fun i : Fin k => z.2 (prefixResponseIndex P i))) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (prefixResponseIndex P i)).comp measurable_snd
  have hpre : Measurable pre :=
    (measurable_foldResponses P (batchStart P u.val) k).comp
      (measurable_fst.prodMk hprefix)
  have hlast : Measurable last :=
    (measurable_pi_apply (lastResponseIndex P)).comp measurable_snd
  have hacc : Measurable accumulated :=
    (measurable_accumulateResponse P).comp (hpre.prodMk hlast)
  have hupdated : Measurable updated :=
    measurable_updatedBands P hpre (measurable_snd.comp hacc)
  have hlow : Measurable (fun z => (accumulated z).1) :=
    measurable_fst.comp hacc
  change Measurable (fun z => completedBatchEstimate P
    (pre z) (accumulated z).1 (updated z))
  exact measurable_completedBatchEstimate P hpre hlow hupdated

def batchEstimateOnHistory {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u : Fin P.T)
    (H : BatchHistory P d u) (seeds : Fin P.n → Seed) : Point d :=
  batchEstimateFromResponses P u
    (stateAt P (batchStart P u.val) H.2)
    (upperBatchResponses O (batchDecision P u H) seeds)

end

end HeavyTailedNoise.UpperK1
