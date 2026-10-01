import HeavyTailedNoise.Upper.K1.CoarseTrackerBoundaryProcess
import HeavyTailedNoise.Upper.Foundations.CoarseTrackerIncrementCompositionMeasurable
import HeavyTailedNoise.Upper.Foundations.MeasurablePairReadout

/-!
The heavy-tailed initial error is retained inside each later pre-batch
history.  This makes the shifted Lyapunov weight predictable before the
whole current batch, including its first response.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- The marginal of the established history × whole-batch product law is
the actual pre-batch history law. -/
theorem measurePreserving_actualBatchHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) :
    MeasurePreserving (batchHistoryOfRun (d := d) P O u)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))
      (batchPastHistoryLaw P O u) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw O P.n) :=
    freshSeedLaw_probability O P.n
  let μpast := batchPastHistoryLaw P O u
  let μbatch := freshSeedLaw O P.n
  have hfst : MeasurePreserving
      (Prod.fst : BatchHistory P d u × (Fin P.n → Seed) → BatchHistory P d u)
      (μpast.prod μbatch) μpast :=
    measurePreserving_fst
  have hjoint := measurePreserving_actualHistory_currentBatch P O u
  have hcomp := hfst.comp hjoint
  simpa only [Function.comp_def] using hcomp

theorem firstBatchStart_le (u : Fin P.T) :
    batchStart P 0 ≤ batchStart P u.val := by
  dsimp [batchStart]
  omega

def firstRuntimeHistory {d : ℕ} (u : Fin P.T)
    (H : BatchHistory P d u) :
    BatchHistory P d ⟨0, P.T_pos⟩ :=
  (H.1, fun i => H.2 (i.castLE (firstBatchStart_le P u)))

theorem measurable_firstRuntimeHistory {d : ℕ} (u : Fin P.T) :
    Measurable (firstRuntimeHistory (d := d) P u) := by
  have hprefix : Measurable
      (fun H : BatchHistory P d u =>
        (fun i : Fin (batchStart P 0) =>
          H.2 (i.castLE (firstBatchStart_le P u)))) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (i.castLE
      (firstBatchStart_le P u))).comp measurable_snd
  exact measurable_fst.prodMk hprefix

irreducible_def initialTrackerOnHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (H : BatchHistory P d u) : ℝ :=
  trackerError I
    (batchDecision P ⟨0, P.T_pos⟩ (firstRuntimeHistory P u H))
    (batchCenter P ⟨0, P.T_pos⟩ (firstRuntimeHistory P u H))

/-- Truncating a real pre-batch transcript at the first runtime boundary
recovers the exact same first history as if it had been read directly. -/
theorem firstRuntimeHistory_actual_eq {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    firstRuntimeHistory P u (batchHistoryOfRun P O u z) =
      batchHistoryOfRun P O ⟨0, P.T_pos⟩ z := by
  apply Prod.ext
  · rfl
  · funext i
    have hU := runTranscript_prefix_le O (algorithm (d := d) P) z.1
      (batchStart P u.val) (responseCount P)
      (batchStart_le_responseCount_of_le P u.val
        (Nat.le_of_lt u.isLt)) z.2
      (i.castLE (firstBatchStart_le P u))
    have h0 := runTranscript_prefix_le O (algorithm (d := d) P) z.1
      (batchStart P 0) (responseCount P)
      (batchStart_le_responseCount_of_le P 0 P.T_pos.le) z.2 i
    have hindex :
        ((i.castLE (firstBatchStart_le P u)).castLE
          (batchStart_le_responseCount_of_le P u.val
            (Nat.le_of_lt u.isLt))) =
        i.castLE (batchStart_le_responseCount_of_le P 0 P.T_pos.le) :=
      Fin.ext rfl
    rw [hindex] at hU
    exact hU.symm.trans h0

theorem initialTrackerOnHistory_actual_eq {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    initialTrackerOnHistory P I u (batchHistoryOfRun P I.oracle u z) =
      actualTrackerAtBoundary P I 0 z := by
  rw [initialTrackerOnHistory, firstRuntimeHistory_actual_eq P I.oracle u z]
  exact (actualTrackerAtBoundary_eq_history P I ⟨0, P.T_pos⟩ z).symm

irreducible_def shiftedWeightOnHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b C lam : ℝ) (H : BatchHistory P d u) : ℝ :=
  Real.exp (lam *
    (trackerError I (batchDecision P u H) (batchCenter P u H) -
      initialTrackerOnHistory P I u H - (b + C)))

theorem measurable_shiftedWeightOnHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b C lam : ℝ) :
    Measurable (shiftedWeightOnHistory P I u b C lam) := by
  let R : Point d × Point d → ℝ := fun a => trackerError I a.1 a.2
  let x : BatchHistory P d u → Point d := batchDecision P u
  let w : BatchHistory P d u → Point d := batchCenter P u
  let x₀ : BatchHistory P d u → Point d := fun H =>
    batchDecision P ⟨0, P.T_pos⟩ (firstRuntimeHistory P u H)
  let w₀ : BatchHistory P d u → Point d := fun H =>
    batchCenter P ⟨0, P.T_pos⟩ (firstRuntimeHistory P u H)
  have hR : Measurable R := measurable_trackerError I
  have hx : Measurable x := measurable_batchDecision P u
  have hw : Measurable w := measurable_batchCenter P u
  have hfirst := measurable_firstRuntimeHistory (d := d) P u
  have hx₀ : Measurable x₀ :=
    (measurable_batchDecision P ⟨0, P.T_pos⟩).comp hfirst
  have hw₀ : Measurable w₀ :=
    (measurable_batchCenter P ⟨0, P.T_pos⟩).comp hfirst
  have hcurrent : Measurable (fun H => R (x H, w H)) :=
    measurable_pair_readout R hR x w hx hw
  have hinitial : Measurable (fun H => R (x₀ H, w₀ H)) :=
    measurable_pair_readout R hR x₀ w₀ hx₀ hw₀
  have hbase : Measurable (fun H =>
      Real.exp (lam * (R (x H, w H) -
        R (x₀ H, w₀ H) - (b + C)))) :=
    Real.measurable_exp.comp
    (measurable_const.mul
      ((hcurrent.sub hinitial).sub
        measurable_const))
  have hfun : shiftedWeightOnHistory P I u b C lam =
      (fun H => Real.exp (lam * (R (x H, w H) -
        R (x₀ H, w₀ H) - (b + C)))) := by
    funext H
    rw [shiftedWeightOnHistory, initialTrackerOnHistory]
  rw [hfun]
  exact hbase

theorem shiftedWeightOnHistory_actual_eq {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b C lam : ℝ)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    shiftedWeightOnHistory P I u b C lam
      (batchHistoryOfRun P I.oracle u z) =
    shiftedTrackerWeight (actualTrackerAtBoundary P I) b C lam u.val z := by
  simp only [shiftedWeightOnHistory, shiftedTrackerWeight,
    initialTrackerOnHistory_actual_eq P I u z,
    actualTrackerAtBoundary_eq_history P I u z]

irreducible_def stoppedWeightOnHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b C lam : ℝ) (H : BatchHistory P d u) : ℝ :=
  if b ≤ trackerError I (batchDecision P u H) (batchCenter P u H)
  then shiftedWeightOnHistory P I u b C lam H
  else 0

theorem measurable_stoppedWeightOnHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b C lam : ℝ) :
    Measurable (stoppedWeightOnHistory P I u b C lam) := by
  let R : Point d × Point d → ℝ := fun a => trackerError I a.1 a.2
  let x : BatchHistory P d u → Point d := batchDecision P u
  let w : BatchHistory P d u → Point d := batchCenter P u
  have hR : Measurable R := measurable_trackerError I
  have hx : Measurable x := measurable_batchDecision P u
  have hw : Measurable w := measurable_batchCenter P u
  have hcurrent : Measurable (fun H => R (x H, w H)) :=
    measurable_pair_readout R hR x w hx hw
  have hlarge : MeasurableSet
      {H : BatchHistory P d u | b ≤ R (x H, w H)} :=
    measurableSet_le measurable_const hcurrent
  have hbase : Measurable (fun H : BatchHistory P d u =>
      if b ≤ R (x H, w H) then shiftedWeightOnHistory P I u b C lam H
      else 0) :=
    Measurable.ite hlarge
      (measurable_shiftedWeightOnHistory P I u b C lam) measurable_const
  have hfun : stoppedWeightOnHistory P I u b C lam =
      (fun H => if b ≤ R (x H, w H) then
        shiftedWeightOnHistory P I u b C lam H else 0) := by
    funext H
    rw [stoppedWeightOnHistory]
  rw [hfun]
  exact hbase

theorem stoppedWeightOnHistory_nonneg {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b C lam : ℝ) (H : BatchHistory P d u) :
    0 ≤ stoppedWeightOnHistory P I u b C lam H := by
  rw [stoppedWeightOnHistory]
  split_ifs
  · rw [shiftedWeightOnHistory]
    exact (Real.exp_pos _).le
  · exact le_refl 0

theorem stoppedWeightOnHistory_large {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b C lam : ℝ) (H : BatchHistory P d u)
    (hpos : stoppedWeightOnHistory P I u b C lam H ≠ 0) :
    b ≤ trackerError I (batchDecision P u H) (batchCenter P u H) := by
  by_contra hnot
  have hzero : stoppedWeightOnHistory P I u b C lam H = 0 := by
    simp [stoppedWeightOnHistory, hnot]
  exact hpos hzero

theorem stoppedWeightOnHistory_actual_eq {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b C lam : ℝ)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    stoppedWeightOnHistory P I u b C lam
      (batchHistoryOfRun P I.oracle u z) =
    if b ≤ actualTrackerAtBoundary P I u.val z then
      shiftedTrackerWeight (actualTrackerAtBoundary P I) b C lam u.val z
    else 0 := by
  rw [stoppedWeightOnHistory,
    ← actualTrackerAtBoundary_eq_history P I u z,
    shiftedWeightOnHistory_actual_eq P I u b C lam z]

theorem stoppedWeight_mul_increment_actual_eq {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b C lam : ℝ)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    stoppedWeightOnHistory P I u b C lam
        (batchHistoryOfRun P I.oracle u z) *
      Real.exp (lam * trackerIncrementOnHistory P I u
        (batchHistoryOfRun P I.oracle u z)
        (batchSeedBlock P u z.2)) =
    if b ≤ actualTrackerAtBoundary P I u.val z then
      shiftedTrackerWeight (actualTrackerAtBoundary P I) b C lam
        (u.val + 1) z
    else 0 := by
  rw [stoppedWeightOnHistory_actual_eq P I u b C lam z]
  split_ifs with hlarge
  · rw [← actualTrackerAtBoundary_increment_eq P I u z]
    dsimp [shiftedTrackerWeight]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp

/-- The stopped predictable weight is integrable under the actual
pre-batch-history law, inherited from the bounded-increment exponential
weight on the full global run. -/
theorem stoppedWeightOnHistory_integrable {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b lam : ℝ) (hlam : 0 ≤ lam)
    (hbeta : 0 ≤ P.beta) (hh : 0 ≤ P.h) :
    Integrable
      (stoppedWeightOnHistory P I u b
        (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h) lam)
      (batchPastHistoryLaw P I.oracle u) := by
  let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  let f := stoppedWeightOnHistory P I u b C lam
  let V := shiftedTrackerWeight (actualTrackerAtBoundary P I) b C lam u.val
  have hV : Integrable V μ :=
    actualTrackerShiftedWeight_integrable P I b lam hlam hbeta hh
      u.val (Nat.le_of_lt u.isLt)
  have hfmeas : Measurable f :=
    measurable_stoppedWeightOnHistory P I u b C lam
  have hhistory : Measurable (batchHistoryOfRun P I.oracle u) :=
    measurable_batchHistoryOfRun P I.oracle u
  have hfcomp : Integrable (f ∘ batchHistoryOfRun P I.oracle u) μ := by
    have hbound (z : Fin P.T × (Fin (responseCount P) → Seed)) :
        ‖f (batchHistoryOfRun P I.oracle u z)‖ ≤ ‖V z‖ := by
      change ‖stoppedWeightOnHistory P I u b C lam
        (batchHistoryOfRun P I.oracle u z)‖ ≤
        ‖shiftedTrackerWeight (actualTrackerAtBoundary P I)
          b C lam u.val z‖
      rw [stoppedWeightOnHistory_actual_eq P I u b C lam z]
      by_cases hlarge : b ≤ actualTrackerAtBoundary P I u.val z
      · simp only [if_pos hlarge, le_refl]
      · simp only [if_neg hlarge, norm_zero]
        exact norm_nonneg _
    exact Integrable.mono hV
      (hfmeas.comp hhistory).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hmap := measurePreserving_actualBatchHistory P I.oracle u
  have htarget : Integrable f (Measure.map
      (batchHistoryOfRun P I.oracle u) μ) :=
    (integrable_map_measure hfmeas.aestronglyMeasurable
      hhistory.aemeasurable).2 hfcomp
  rw [hmap.map_eq] at htarget
  exact htarget

/-- The full-batch exponential multiplier preserves integrability of the
predictable stopped weight because every tracker increment is capped. -/
theorem stoppedWeight_batchProduct_integrable {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (b lam : ℝ) (hlam : 0 ≤ lam)
    (hbeta : 0 ≤ P.beta) (hh : 0 ≤ P.h) :
    Integrable
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        stoppedWeightOnHistory P I u b
          (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h) lam z.1 *
        Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2))
      ((batchPastHistoryLaw P I.oracle u).prod
        (freshSeedLaw I.oracle P.n)) := by
  let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
  let f := stoppedWeightOnHistory P I u b C lam
  let μpast := batchPastHistoryLaw P I.oracle u
  let μbatch := freshSeedLaw I.oracle P.n
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure μbatch := freshSeedLaw_probability I.oracle P.n
  have hfInt : Integrable f μpast :=
    stoppedWeightOnHistory_integrable P I u b lam hlam hbeta hh
  have hfProd : Integrable (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
      f z.1) (μpast.prod μbatch) :=
    (measurePreserving_fst (μ := μpast) (ν := μbatch)).integrable_comp_of_integrable
      hfInt
  have hχ : Measurable (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
      trackerIncrementOnHistory P I u z.1 z.2) := by
    let x : BatchHistory P d u × (Fin P.n → Seed) → Point d :=
      fun z => batchDecision P u z.1
    let w : BatchHistory P d u × (Fin P.n → Seed) → Point d :=
      fun z => batchCenter P u z.1
    let estimate : BatchHistory P d u × (Fin P.n → Seed) → Point d :=
      fun z => batchEstimateOnHistory P I.oracle u z.1 z.2
    let y : BatchHistory P d u × (Fin P.n → Seed) → Point d :=
      fun z => I.oracle.response (x z) (z.2 ⟨0, P.n_pos⟩)
    have hx : Measurable x :=
      (measurable_batchDecision P u).comp measurable_fst
    have hw : Measurable w :=
      (measurable_batchCenter P u).comp measurable_fst
    have hestimate : Measurable estimate :=
      measurable_batchEstimateOnHistory P I.oracle u
    have hfirst : Measurable
        (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
          z.2 ⟨0, P.n_pos⟩) :=
      (measurable_pi_apply (⟨0, P.n_pos⟩ : Fin P.n)).comp measurable_snd
    have hy : Measurable y :=
      I.oracle.measurable_response.comp (hx.prodMk hfirst)
    have hexplicit : Measurable (fun z => trackerError I
        (x z - P.h • direction (estimate z))
        (coarseCenter P (w z) (y z)) - trackerError I (x z) (w z)) :=
      measurable_trackerIncrement_composition P
        (fun a : Point d × Point d => trackerError I a.1 a.2)
        (measurable_trackerError I)
        x w estimate y hx hw hestimate hy
    have hfun : (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        trackerIncrementOnHistory P I u z.1 z.2) =
      (fun z => trackerError I
        (x z - P.h • direction (estimate z))
        (coarseCenter P (w z) (y z)) - trackerError I (x z) (w z)) := by
      funext z
      rw [trackerIncrementOnHistory]
    rw [hfun]
    exact hexplicit
  have hgmeas : Measurable
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        f z.1 * Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2)) :=
    ((measurable_stoppedWeightOnHistory P I u b C lam).comp measurable_fst).mul
      (Real.measurable_exp.comp
        (measurable_const.mul hχ))
  have hbound (z : BatchHistory P d u × (Fin P.n → Seed)) :
      ‖f z.1 * Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2)‖ ≤
        Real.exp (lam * C) * f z.1 := by
    have hf0 := stoppedWeightOnHistory_nonneg P I u b C lam z.1
    have hχ := trackerIncrementOnHistory_abs_le P I u z.1 z.2 hbeta hh
    have hχle : trackerIncrementOnHistory P I u z.1 z.2 ≤ C :=
      (le_abs_self _).trans hχ
    have hexp : Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2) ≤
        Real.exp (lam * C) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hχle hlam)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hf0,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      f z.1 * Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2) ≤
          f z.1 * Real.exp (lam * C) :=
        mul_le_mul_of_nonneg_left hexp hf0
      _ = Real.exp (lam * C) * f z.1 := mul_comm _ _
  exact Integrable.mono' (hfProd.const_mul (Real.exp (lam * C)))
    hgmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

end

end HeavyTailedNoise.UpperK1
