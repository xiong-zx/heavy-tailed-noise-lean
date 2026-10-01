import HeavyTailedNoise.Upper.K1.ActualBatchConditionalMean
import HeavyTailedNoise.Upper.K1.ActualBatchMomentTransfer

/-!
An earlier whole-batch kernel error is observable from the complete
transcript before a later runtime batch. This is the filtration fact needed
to use the later batch's proved conditional mean zero without conditioning
inside either shared batch.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

private theorem batchStart_le_of_lt (u v : Fin P.T) (huv : u.val < v.val) :
    batchStart P u.val ≤ batchStart P v.val := by
  have hmul := Nat.mul_le_mul_right P.n (Nat.le_of_lt huv)
  dsimp [batchStart]
  omega

private theorem batchResponseIndex_lt_laterStart
    (u v : Fin P.T) (huv : u.val < v.val) (j : Fin P.n) :
    (batchResponseIndex P u j).val < batchStart P v.val := by
  have hnext : u.val + 1 ≤ v.val := huv
  have hmul : (u.val + 1) * P.n ≤ v.val * P.n :=
    Nat.mul_le_mul_right P.n hnext
  have hend : batchStart P u.val + P.n ≤ batchStart P v.val := by
    calc
      batchStart P u.val + P.n =
          1 + initialResponses P + (u.val * P.n + P.n) := by
            dsimp [batchStart]
            omega
      _ = 1 + initialResponses P + (u.val + 1) * P.n := by
        rw [Nat.succ_mul]
      _ ≤ 1 + initialResponses P + v.val * P.n :=
        Nat.add_le_add_left hmul _
      _ = batchStart P v.val := rfl
  exact (batchResponseIndex_lt_end P u j).trans_le hend

/-- Earlier whole-batch response `j` is already part of the transcript
available before later batch `v`. -/
def earlierResponseIndex (u v : Fin P.T) (huv : u.val < v.val)
    (j : Fin P.n) : Fin (batchStart P v.val) :=
  ⟨(batchResponseIndex P u j).val,
    batchResponseIndex_lt_laterStart P u v huv j⟩

/-- Restrict a later complete pre-batch transcript to the full history that
preceded an earlier batch. The private index is retained. -/
def earlierHistory (u v : Fin P.T) (huv : u.val < v.val)
    {d : ℕ} (H : BatchHistory P d v) : BatchHistory P d u :=
  (H.1, fun i => H.2 (i.castLE (batchStart_le_of_lt P u v huv)))

theorem measurable_earlierHistory (u v : Fin P.T) (huv : u.val < v.val)
    {d : ℕ} : Measurable (earlierHistory (d := d) P u v huv) := by
  have hprefix : Measurable
      (fun H : BatchHistory P d v =>
        (fun i : Fin (batchStart P u.val) =>
          H.2 (i.castLE (batchStart_le_of_lt P u v huv)))) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (i.castLE
      (batchStart_le_of_lt P u v huv))).comp measurable_snd
  exact measurable_fst.prodMk hprefix

/-- On an actual run, restricting the later pre-batch transcript reproduces
the earlier full pre-batch history exactly. -/
theorem earlierHistory_actual_eq {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u v : Fin P.T) (huv : u.val < v.val)
    (r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    earlierHistory P u v huv (batchHistoryOfRun P O v (r, seeds)) =
      batchHistoryOfRun P O u (r, seeds) := by
  let A := algorithm (d := d) P
  have hU : batchStart P u.val ≤ responseCount P :=
    Nat.le_of_lt (outputIndex P u).isLt
  have hV : batchStart P v.val ≤ responseCount P :=
    Nat.le_of_lt (outputIndex P v).isLt
  unfold earlierHistory batchHistoryOfRun
  congr 1
  funext i
  have hleft := runTranscript_prefix_le O A r
    (batchStart P v.val) (responseCount P) hV seeds
    (i.castLE (batchStart_le_of_lt P u v huv))
  have hright := runTranscript_prefix_le O A r
    (batchStart P u.val) (responseCount P) hU seeds i
  have hindex :
      (i.castLE (batchStart_le_of_lt P u v huv)).castLE hV =
        i.castLE hU := Fin.ext rfl
  rw [hindex] at hleft
  exact hleft.symm.trans hright

/-- The earlier batch's logged response is accessible at the corresponding
coordinate of the later pre-batch transcript. -/
theorem earlier_logged_response_actual_eq {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u v : Fin P.T) (huv : u.val < v.val)
    (r : Fin P.T) (seeds : Fin (responseCount P) → Seed)
    (j : Fin P.n) :
    ((batchHistoryOfRun P O v (r, seeds)).2
      (earlierResponseIndex P u v huv j)).2 =
      (runTranscript O (algorithm (d := d) P) r (responseCount P)
        seeds (batchResponseIndex P u j)).2 := by
  let A := algorithm (d := d) P
  have hV : batchStart P v.val ≤ responseCount P :=
    Nat.le_of_lt (outputIndex P v).isLt
  have hprefix := runTranscript_prefix_le O A r
    (batchStart P v.val) (responseCount P) hV seeds
    (earlierResponseIndex P u v huv j)
  have hindex : (earlierResponseIndex P u v huv j).castLE hV =
      batchResponseIndex P u j := Fin.ext rfl
  rw [hindex] at hprefix
  exact congrArg Prod.snd hprefix.symm

/-- The earlier centered `Φ_k` batch error as a measurable function of the
later *complete pre-batch* history, using logged responses rather than seeds. -/
def earlierKernelErrorFromHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u v : Fin P.T) (huv : u.val < v.val) (k : ℕ)
    (H : BatchHistory P d v) : Point d :=
  let Hu := earlierHistory P u v huv H
  let x := batchDecision P u Hu
  let w := batchCenter P u Hu
  (P.n : ℝ)⁻¹ • ∑ j : Fin P.n,
    kernelPhi P k ((H.2 (earlierResponseIndex P u v huv j)).2 - w)
    - upperResidualSourceMean O (kernelPhi P k) x w

theorem measurable_earlierKernelErrorFromHistory
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u v : Fin P.T)
    (huv : u.val < v.val) (k : ℕ) :
    Measurable (earlierKernelErrorFromHistory P O u v huv k) := by
  let x : BatchHistory P d v → Point d :=
    batchDecision P u ∘ earlierHistory P u v huv
  let w : BatchHistory P d v → Point d :=
    batchCenter P u ∘ earlierHistory P u v huv
  have hx : Measurable x :=
    (measurable_batchDecision P u).comp
      (measurable_earlierHistory P u v huv)
  have hw : Measurable w :=
    (measurable_batchCenter P u).comp
      (measurable_earlierHistory P u v huv)
  have hsum : Measurable (fun H : BatchHistory P d v =>
      ∑ j : Fin P.n,
        kernelPhi P k
          ((H.2 (earlierResponseIndex P u v huv j)).2 - w H)) := by
    apply Finset.measurable_sum
    intro j hj
    have hresponse : Measurable (fun H : BatchHistory P d v =>
        (H.2 (earlierResponseIndex P u v huv j)).2) :=
      measurable_snd.comp ((measurable_pi_apply
        (earlierResponseIndex P u v huv j)).comp measurable_snd)
    exact (measurable_kernelPhi P k).comp (hresponse.sub hw)
  have hmean : Measurable (fun H : BatchHistory P d v =>
      upperResidualSourceMean O (kernelPhi P k) (x H) (w H)) :=
    measurable_upperResidualSourceMean O (kernelPhi P k)
      (measurable_kernelPhi P k) x w hx hw
  exact ((measurable_const : Measurable
    (fun _ : BatchHistory P d v => (P.n : ℝ)⁻¹)).smul hsum).sub hmean

/-- Earlier actual batch error is exactly the function of later pre-batch
history defined above; no earlier seed becomes an algorithm observation. -/
theorem actualKernelBatchError_eq_earlierHistory
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u v : Fin P.T)
    (huv : u.val < v.val) (k : ℕ)
    (r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    actualKernelBatchError P O u k (r, seeds) =
      earlierKernelErrorFromHistory P O u v huv k
        (batchHistoryOfRun P O v (r, seeds)) := by
  let Hv := batchHistoryOfRun P O v (r, seeds)
  have hHu := earlierHistory_actual_eq P O u v huv r seeds
  have hsum :
      (∑ j : Fin P.n,
        kernelPhi P k
          (O.response
            (batchDecision P u (batchHistoryOfRun P O u (r, seeds)))
            (batchSeedBlock P u seeds j) -
            batchCenter P u (batchHistoryOfRun P O u (r, seeds)))) =
      ∑ j : Fin P.n,
        kernelPhi P k
          (((Hv.2 (earlierResponseIndex P u v huv j)).2) -
            batchCenter P u (batchHistoryOfRun P O u (r, seeds))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← batch_logged_response_eq_oracle P O r u seeds j,
      ← earlier_logged_response_actual_eq P O u v huv r seeds j]
  unfold actualKernelBatchError kernelBatchErrorAtHistory
    earlierKernelErrorFromHistory upperResidualBatchMean
  rw [hHu]
  rw [hsum]

end

end HeavyTailedNoise.UpperK1
