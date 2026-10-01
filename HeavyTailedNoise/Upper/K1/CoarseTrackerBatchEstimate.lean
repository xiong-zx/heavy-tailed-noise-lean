import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchTerminal

/-!
The completed direction estimate as a measurable function of one pre-batch
state and all `n` returned vectors. Its calculation calls the three unique
helpers owned by `Algorithm.step`; no estimator formula is copied here.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

def lastResponseIndex : Fin P.n :=
  ⟨P.n - 1, by have hn := P.n_pos; omega⟩

def prefixResponseIndex (i : Fin (P.n - 1)) : Fin P.n :=
  ⟨i.val, lt_trans i.isLt (lastResponseIndex P).isLt⟩

/-- Reconstruct the last-response estimate from an entire returned-vector
block, using exactly the current algorithm's state fold and helpers. -/
def batchEstimateFromResponses {d : ℕ} (u : Fin P.T)
    (s : State d P.J) (ys : Fin P.n → Point d) : Point d :=
  let k := P.n - 1
  let pre := foldResponses P (batchStart P u.val) s k
    (fun i : Fin k => ys (prefixResponseIndex P i))
  let last := ys (lastResponseIndex P)
  let accumulated := accumulateResponse P pre last
  let updated := updatedBands P pre accumulated.2
  completedBatchEstimate P pre accumulated.1 updated

theorem measurable_accumulateResponse {d : ℕ} :
    Measurable (fun z : State d P.J × Point d =>
      accumulateResponse P z.1 z.2) := by
  dsimp [accumulateResponse, lowSum, highSums, center]
  fun_prop

theorem measurable_completedBatchEstimate {d : ℕ} {α : Type*}
    [MeasurableSpace α] {s : α → State d P.J}
    {low : α → Point d} {updated : α → Fin P.J → Point d}
    (hs : Measurable s) (hlow : Measurable low)
    (hupdated : Measurable updated) :
    Measurable (fun z => completedBatchEstimate P (s z) (low z) (updated z)) := by
  have hcenter : Measurable (fun z => center P (s z)) := by
    dsimp [center]
    fun_prop
  have hsum : Measurable (fun z => ∑ j, updated z j) := by
    apply Finset.measurable_sum
    intro j hj
    exact (measurable_pi_apply j).comp hupdated
  have hcoef : Measurable (fun _ : α => (P.n : ℝ)⁻¹) := measurable_const
  change Measurable (fun z => center P (s z) +
    (P.n : ℝ)⁻¹ • low z + ∑ j, updated z j)
  exact (hcenter.add (hcoef.smul hlow)).add hsum

end

end HeavyTailedNoise.UpperK1
