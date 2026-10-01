import HeavyTailedNoise.Upper.K1.KernelRuntimeSourceDriftReadout

/-!
One source-mean sequence read from the canonical full transcript.  Time
`t+1` denotes the source mean at runtime boundary `t`, so the move
`u+1 → u+2` is exactly the source drift across completed batch `u`.
This adds no oracle calls or independent band copies.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

irreducible_def actualBandSourceAtBoundary
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (j : Fin P.J) (t : ℕ)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) : Point d :=
  if ht : t ≤ P.T then
    let st := stateAt P (batchStart P t)
      (boundaryTranscript P O t ht z)
    upperResidualSourceMean O (highBand P j)
      (point P st) (center P st)
  else 0

theorem measurable_actualBandSourceAtBoundary
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (j : Fin P.J) (t : ℕ) :
    Measurable (actualBandSourceAtBoundary P O j t) := by
  by_cases ht : t ≤ P.T
  · have hstate : Measurable
        (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
          stateAt P (batchStart P t)
            (boundaryTranscript P O t ht z)) :=
      (measurable_stateAt P (batchStart P t)).comp
        (measurable_boundaryTranscript P O t ht)
    have hx := measurable_fst.comp hstate
    have hw := (measurable_fst.comp (measurable_snd.comp hstate))
    have hmean := measurable_upperResidualSourceMean O (highBand P j)
      (measurable_highBand P j) _ _ hx hw
    change Measurable (fun z =>
      upperResidualSourceMean O (highBand P j)
        (point P (stateAt P (batchStart P t)
          (boundaryTranscript P O t ht z)))
        (center P (stateAt P (batchStart P t)
          (boundaryTranscript P O t ht z)))) at hmean
    change Measurable (fun z => actualBandSourceAtBoundary P O j t z)
    simpa only [actualBandSourceAtBoundary, dif_pos ht] using hmean
  · change Measurable (fun z => actualBandSourceAtBoundary P O j t z)
    simpa only [actualBandSourceAtBoundary, dif_neg ht] using
      (measurable_const : Measurable
        (fun _ : Fin P.T × (Fin (responseCount P) → Seed) =>
          (0 : Point d)))

def actualBandSourceSequence
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (z : Fin P.T × (Fin (responseCount P) → Seed))
    (j : Fin P.J) : ℕ → Point d
  | 0 => 0
  | t + 1 => actualBandSourceAtBoundary P O j t z

theorem measurable_actualBandSourceSequence
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (j : Fin P.J) (t : ℕ) :
    Measurable (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
      actualBandSourceSequence P O z j t) := by
  cases t with
  | zero => simpa [actualBandSourceSequence] using
      (measurable_const : Measurable
        (fun _ : Fin P.T × (Fin (responseCount P) → Seed) =>
          (0 : Point d)))
  | succ t => simpa only [actualBandSourceSequence] using
      (measurable_actualBandSourceAtBoundary P O j t)

theorem actualBandSourceAtBoundary_eq_batchStart
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (j : Fin P.J)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    actualBandSourceAtBoundary P O j u.val z =
      upperResidualSourceMean O (highBand P j)
        (batchDecision P u (batchHistoryOfRun P O u z))
        (batchCenter P u (batchHistoryOfRun P O u z)) := by
  have hu : u.val ≤ P.T := Nat.le_of_lt u.isLt
  rw [actualBandSourceAtBoundary, dif_pos hu]
  rw [boundaryTranscript_eq_batchHistory P O u z]
  rfl

theorem actualBandSourceAtBoundary_eq_batchEnd
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (j : Fin P.J)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    actualBandSourceAtBoundary P O j (u.val + 1) z =
      upperResidualSourceMean O (highBand P j)
        (point P (stateAt P (batchEndTime P u)
          (batchEndTranscript P O z.1 u z.2)))
        (center P (stateAt P (batchEndTime P u)
          (batchEndTranscript P O z.1 u z.2))) := by
  have hu : u.val + 1 ≤ P.T := Nat.succ_le_iff.mpr u.isLt
  have htime := batchStart_succ_eq_batchEndTime P u
  have htrans := boundaryTranscript_succ_eq_batchEndTranscript P O u z
  have hstate := stateAt_transcript_cast P htime
    (boundaryTranscript P O (u.val + 1) hu z)
  rw [htrans] at hstate
  rw [actualBandSourceAtBoundary, dif_pos hu]
  rw [← hstate]

/-- The dyadic source-motion readout is exactly the weighted move of the
single actual source-mean sequence, at every runtime batch. -/
theorem actualBandSourceSequence_weighted_move_eq_drift
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (s : ℝ)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    (∑ j : Fin P.J,
      (12 * (2 : ℝ) ^ j.val) ^ s *
        ‖actualBandSourceSequence P O z j (u.val + 2) -
          actualBandSourceSequence P O z j (u.val + 1)‖) =
      actualHighBandSourceDrift P O s u z := by
  rw [actualHighBandSourceDrift]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [actualBandSourceSequence]
  rw [actualBandSourceAtBoundary_eq_batchEnd P O j u z,
    actualBandSourceAtBoundary_eq_batchStart P O j u z]

theorem measurable_actualHighBandSourceDrift
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (s : ℝ) (u : Fin P.T) :
    Measurable (actualHighBandSourceDrift P O s u) := by
  have hsum : Measurable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        ∑ j : Fin P.J,
          (12 * (2 : ℝ) ^ j.val) ^ s *
            ‖actualBandSourceSequence P O z j (u.val + 2) -
              actualBandSourceSequence P O z j (u.val + 1)‖) := by
    apply Finset.measurable_sum
    intro j hj
    exact measurable_const.mul
      (((measurable_actualBandSourceSequence P O j (u.val + 2)).sub
        (measurable_actualBandSourceSequence P O j (u.val + 1))).norm)
  have heq : (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
      ∑ j : Fin P.J,
        (12 * (2 : ℝ) ^ j.val) ^ s *
          ‖actualBandSourceSequence P O z j (u.val + 2) -
            actualBandSourceSequence P O z j (u.val + 1)‖) =
      actualHighBandSourceDrift P O s u := by
    funext z
    exact actualBandSourceSequence_weighted_move_eq_drift P O s u z
  rw [← heq]
  exact hsum

theorem actualHighBandSourceDrift_nonneg
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (s : ℝ) (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    0 ≤ actualHighBandSourceDrift P O s u z := by
  rw [actualHighBandSourceDrift]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg
      (Real.rpow_nonneg (by positivity :
        (0 : ℝ) ≤ 12 * (2 : ℝ) ^ j.val) _)
      (norm_nonneg _)

end

end HeavyTailedNoise.UpperK1
