import HeavyTailedNoise.Upper.K1.MeanDriftActualSource
import HeavyTailedNoise.Upper.K1.RuntimeNoisePrivateIndependence

/-!
The private output index is response-free, so the actual source-mean drift
is a function of the original global oracle seed tape alone.  This reuses
the transcript-independence certificate shared with runtime kernel noise.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem boundaryTranscript_private_independent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (t : ℕ) (ht : t ≤ P.T) (r r' : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) :
    boundaryTranscript P O t ht (r, seeds) =
      boundaryTranscript P O t ht (r', seeds) := by
  funext i
  exact congrFun
    (runTranscript_private_independent P O r r'
      (responseCount P) seeds)
    (i.castLE (batchStart_le_responseCount_of_le P t ht))

theorem actualBandSourceAtBoundary_private_independent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (j : Fin P.J) (t : ℕ)
    (r r' : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    actualBandSourceAtBoundary P O j t (r, seeds) =
      actualBandSourceAtBoundary P O j t (r', seeds) := by
  by_cases ht : t ≤ P.T
  · rw [actualBandSourceAtBoundary, actualBandSourceAtBoundary,
      dif_pos ht, dif_pos ht,
      boundaryTranscript_private_independent P O t ht r r' seeds]
  · simp only [actualBandSourceAtBoundary, dif_neg ht]

theorem actualBandSourceSequence_private_independent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (j : Fin P.J) (t : ℕ)
    (r r' : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    actualBandSourceSequence P O (r, seeds) j t =
      actualBandSourceSequence P O (r', seeds) j t := by
  cases t with
  | zero => rfl
  | succ t =>
      exact actualBandSourceAtBoundary_private_independent
        P O j t r r' seeds

theorem batchEndTranscript_private_independent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (u r r' : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) :
    batchEndTranscript P O r u seeds =
      batchEndTranscript P O r' u seeds := by
  funext i
  exact congrFun
    (runTranscript_private_independent P O r r'
      (responseCount P) seeds)
    (i.castLE (batchEndTime_le_responseCount P u))

theorem actualHighBandSourceDrift_private_independent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (s : ℝ)
    (u r r' : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) :
    actualHighBandSourceDrift P O s u (r, seeds) =
      actualHighBandSourceDrift P O s u (r', seeds) := by
  have hpre := batchHistoryOfRun_transcript_private_independent
    P O u r r' seeds
  have hpost := batchEndTranscript_private_independent
    P O u r r' seeds
  rw [actualHighBandSourceDrift, actualHighBandSourceDrift]
  simp only [batchDecision, batchCenter]
  rw [hpre, hpost]

end

end HeavyTailedNoise.UpperK1
