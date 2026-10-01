import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchEstimateHistoryMeasurable
import HeavyTailedNoise.Upper.K1.BatchSeedProduct

/-!
The actual adaptive run, restricted to one complete runtime batch. Its
pre-batch state comes from the full earlier transcript, and each current
returned vector is the oracle response at that frozen query point. This file
uses the existing `runTranscript` and the unique `Algorithm.step` fold.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

def batchEndTime (u : Fin P.T) : ℕ := batchStart P u.val + P.n

theorem batchEndTime_le_responseCount (u : Fin P.T) :
    batchEndTime P u ≤ responseCount P := by
  have hu : u.val + 1 ≤ P.T := Nat.succ_le_iff.mpr u.isLt
  have hmul := Nat.mul_le_mul_right P.n hu
  dsimp [batchEndTime, batchStart, responseCount]
  rw [Nat.succ_mul] at hmul
  omega

/-- Restrict the actual full log to the end of the selected runtime batch. -/
def batchEndTranscript {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (r u : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) :
    Transcript d (batchEndTime P u) :=
  fun i => (runTranscript O (algorithm (d := d) P) r
    (responseCount P) seeds) (i.castLE (batchEndTime_le_responseCount P u))

theorem batchEndTranscript_prefix_eq_history {d : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (r u : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) :
    transcriptPrefix (batchStart P u.val) P.n
      (batchEndTranscript P O r u seeds) =
        (batchHistoryOfRun P O u (r, seeds)).2 := by
  funext i
  have hstart : batchStart P u.val ≤ responseCount P :=
    Nat.le_trans (Nat.le_add_right _ _) (batchEndTime_le_responseCount P u)
  have hlog := runTranscript_prefix_le O (algorithm (d := d) P) r
    (batchStart P u.val) (responseCount P) hstart seeds i
  calc
    (transcriptPrefix (batchStart P u.val) P.n
        (batchEndTranscript P O r u seeds)) i =
        (runTranscript O (algorithm (d := d) P) r
          (responseCount P) seeds) (i.castLE hstart) := by
            dsimp [transcriptPrefix, batchEndTranscript]
            exact congrArg
              (runTranscript O (algorithm (d := d) P) r (responseCount P) seeds)
              (Fin.ext rfl)
    _ = runTranscript O (algorithm (d := d) P) r
        (batchStart P u.val)
        (fun j => seeds (j.castLE hstart)) i := hlog
    _ = (batchHistoryOfRun P O u (r, seeds)).2 i := by
      dsimp [batchHistoryOfRun]

theorem batchEndTranscript_responses_eq_oracle {d : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (r u : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) :
    transcriptBlockResponses (batchStart P u.val) P.n
      (batchEndTranscript P O r u seeds) =
        upperBatchResponses O
          (batchDecision P u (batchHistoryOfRun P O u (r, seeds)))
          (batchSeedBlock P u seeds) := by
  funext j
  have hindex :
      ((⟨batchStart P u.val + j.val, by
          have hj := j.isLt
          dsimp [batchEndTime]
          omega⟩ : Fin (batchEndTime P u)).castLE
        (batchEndTime_le_responseCount P u)) =
          batchResponseIndex P u j := Fin.ext rfl
  change (runTranscript O (algorithm (d := d) P) r (responseCount P) seeds
    ((⟨batchStart P u.val + j.val, by
      have hj := j.isLt
      dsimp [batchEndTime]
      omega⟩ : Fin (batchEndTime P u)).castLE
      (batchEndTime_le_responseCount P u))).2 = _
  rw [hindex]
  exact batch_logged_response_eq_oracle P O r u seeds j

/-- The actual post-batch state equals the local fold from its strict
pre-batch state with exactly the `n` newly returned vectors. -/
theorem actualBatch_state_eq_fold {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (r u : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    stateAt P (batchEndTime P u) (batchEndTranscript P O r u seeds) =
      foldResponses P (batchStart P u.val)
        (stateAt P (batchStart P u.val)
          (batchHistoryOfRun P O u (r, seeds)).2)
        P.n
        (upperBatchResponses O
          (batchDecision P u (batchHistoryOfRun P O u (r, seeds)))
          (batchSeedBlock P u seeds)) := by
  have h := stateAt_eq_foldResponses P (batchStart P u.val) P.n
    (batchEndTranscript P O r u seeds)
  simpa only [batchEndTime, batchEndTranscript_prefix_eq_history P O r u seeds,
    batchEndTranscript_responses_eq_oracle P O r u seeds] using h

end

end HeavyTailedNoise.UpperK1
