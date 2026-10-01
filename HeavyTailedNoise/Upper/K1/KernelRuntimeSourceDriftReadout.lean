import HeavyTailedNoise.Upper.K1.KernelRuntimeSourceMeanDrift
import HeavyTailedNoise.Upper.K1.CoarseTrackerBoundaryProcess

/-!
Opaque analysis readouts of the unique canonical run.  They do not define
another algorithm or tracker update.  Keeping these readouts opaque avoids
unfolding the complete paper schedule, transcript, and high-band sum while
transporting a pathwise bound through an outer integral.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

irreducible_def actualHighBandSourceDrift
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (s : ℝ) (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) : ℝ :=
  let H := batchHistoryOfRun P O u z
  let x := batchDecision P u H
  let w := batchCenter P u H
  let x' := point P (stateAt P (batchEndTime P u)
    (batchEndTranscript P O z.1 u z.2))
  let w' := center P (stateAt P (batchEndTime P u)
    (batchEndTranscript P O z.1 u z.2))
  ∑ j : Fin P.J,
    (12 * (2 : ℝ) ^ j.val) ^ s *
      ‖upperResidualSourceMean O (highBand P j) x' w' -
        upperResidualSourceMean O (highBand P j) x w‖

irreducible_def actualTrackerPairScale
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) : ℝ :=
  (2 * σ + actualTrackerAtBoundary P I u.val z) +
    actualTrackerAtBoundary P I (u.val + 1) z

theorem actualPre_grad_sub_center_norm_eq_trackerBoundary
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    ‖I.objective.grad
        (batchDecision P u (batchHistoryOfRun P I.oracle u z)) -
      batchCenter P u (batchHistoryOfRun P I.oracle u z)‖ =
      actualTrackerAtBoundary P I u.val z := by
  calc
    _ = trackerError I
        (batchDecision P u (batchHistoryOfRun P I.oracle u z))
        (batchCenter P u (batchHistoryOfRun P I.oracle u z)) := by
      change ‖I.objective.grad
          (batchDecision P u (batchHistoryOfRun P I.oracle u z)) -
        batchCenter P u (batchHistoryOfRun P I.oracle u z)‖ =
        ‖batchCenter P u (batchHistoryOfRun P I.oracle u z) -
          I.objective.grad
            (batchDecision P u (batchHistoryOfRun P I.oracle u z))‖
      exact norm_sub_rev _ _
    _ = actualTrackerAtBoundary P I u.val z :=
      (actualTrackerAtBoundary_eq_history P I u z).symm

theorem actualPost_grad_sub_center_norm_eq_trackerBoundary
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    ‖I.objective.grad
        (point P (stateAt P (batchEndTime P u)
          (batchEndTranscript P I.oracle z.1 u z.2))) -
      center P (stateAt P (batchEndTime P u)
        (batchEndTranscript P I.oracle z.1 u z.2))‖ =
      actualTrackerAtBoundary P I (u.val + 1) z := by
  calc
    _ = trackerError I
        (point P (stateAt P (batchEndTime P u)
          (batchEndTranscript P I.oracle z.1 u z.2)))
        (center P (stateAt P (batchEndTime P u)
          (batchEndTranscript P I.oracle z.1 u z.2))) := by
      change ‖I.objective.grad
          (point P (stateAt P (batchEndTime P u)
            (batchEndTranscript P I.oracle z.1 u z.2))) -
        center P (stateAt P (batchEndTime P u)
          (batchEndTranscript P I.oracle z.1 u z.2))‖ =
        ‖center P (stateAt P (batchEndTime P u)
            (batchEndTranscript P I.oracle z.1 u z.2)) -
          I.objective.grad
            (point P (stateAt P (batchEndTime P u)
              (batchEndTranscript P I.oracle z.1 u z.2)))‖
      exact norm_sub_rev _ _
    _ = actualTrackerAtBoundary P I (u.val + 1) z :=
      (actualTrackerAtBoundary_succ_eq_batchEnd P I u z).symm

end

end HeavyTailedNoise.UpperK1
