import HeavyTailedNoise.Upper.K1.BatchSeedProduct

/-!
The pre-batch transcript is a function of the private output index and seed
coordinates strictly before the runtime batch. Its query and center do not
read any current-batch or future seed.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Embed one strict pre-batch seed index into the past component of the
canonical three-way split. -/
def pastSeedIndexOfFin (u : Fin P.T)
    (i : Fin (batchStart P u.val)) : PastSeedIndex P u :=
  ⟨⟨i.val, lt_trans i.isLt (outputIndex P u).isLt⟩, i.isLt⟩

/-- Reconstruct the full returned transcript before `u` from exactly the
private index and the seed coordinates in the past factor. -/
def batchHistoryFromPast {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u : Fin P.T)
    (z : Fin P.T × (PastSeedIndex P u → Seed)) : BatchHistory P d u :=
  (z.1, runTranscript O (algorithm (d := d) P) z.1 (batchStart P u.val)
    (fun i => z.2 (pastSeedIndexOfFin P u i)))

theorem measurable_batchHistoryFromPast {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (u : Fin P.T) :
    Measurable (batchHistoryFromPast (d := d) P O u) := by
  have hprefix : Measurable
      (fun z : Fin P.T × (PastSeedIndex P u → Seed) =>
        (fun i : Fin (batchStart P u.val) =>
          z.2 (pastSeedIndexOfFin P u i))) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (pastSeedIndexOfFin P u i)).comp
      measurable_snd
  exact measurable_fst.prodMk
    ((measurable_runTranscript O (algorithm (d := d) P)
      (batchStart P u.val)).comp (measurable_fst.prodMk hprefix))

/-- The actual history built from a global iid seed path is exactly the
history reconstructed from its past factor after splitting. -/
theorem batchHistoryOfRun_eq_fromPast {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    batchHistoryOfRun P O u (r, seeds) =
      batchHistoryFromPast P O u (r, (splitBatchSeedPath P u seeds).1) := by
  unfold batchHistoryOfRun batchHistoryFromPast
  congr 1

theorem measurable_batchDecisionFromPast {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (u : Fin P.T) :
    Measurable (fun z : Fin P.T × (PastSeedIndex P u → Seed) =>
      batchDecision P u (batchHistoryFromPast P O u z)) :=
  (measurable_batchDecision P u).comp (measurable_batchHistoryFromPast P O u)

theorem measurable_batchCenterFromPast {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (u : Fin P.T) :
    Measurable (fun z : Fin P.T × (PastSeedIndex P u → Seed) =>
      batchCenter P u (batchHistoryFromPast P O u z)) :=
  (measurable_batchCenter P u).comp (measurable_batchHistoryFromPast P O u)

theorem batchDecisionOfRun_eq_fromPast {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    batchDecision P u (batchHistoryOfRun P O u (r, seeds)) =
      batchDecision P u
        (batchHistoryFromPast P O u (r, (splitBatchSeedPath P u seeds).1)) := by
  rw [batchHistoryOfRun_eq_fromPast P O u r seeds]

theorem batchCenterOfRun_eq_fromPast {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    batchCenter P u (batchHistoryOfRun P O u (r, seeds)) =
      batchCenter P u
        (batchHistoryFromPast P O u (r, (splitBatchSeedPath P u seeds).1)) := by
  rw [batchHistoryOfRun_eq_fromPast P O u r seeds]

end

end HeavyTailedNoise.UpperK1
