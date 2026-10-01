import HeavyTailedNoise.Upper.K1.CoarseTrackerActualMemoryUpdate

/-!
The high-band memory at each genuine runtime boundary of the one logged
algorithm. The total extension beyond `T` serves only analysis. At `t<T`,
its recurrence is exactly the `Algorithm.step` EMA with the same full seed
tape and current shared batch.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

def actualRuntimeMemory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (j : Fin P.J)
    (t : ℕ) : Point d :=
  let z : Fin P.T × (Fin (responseCount P) → Seed) :=
    ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
  if ht : t ≤ P.T then
    memories P (stateAt P (batchStart P t)
      (boundaryTranscript P O t ht z)) j
  else 0

theorem actualRuntimeMemory_succ {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (j : Fin P.J)
    (t : ℕ) (ht : t < P.T) :
    actualRuntimeMemory P O seeds j (t + 1) =
      (1 - P.alpha j) • actualRuntimeMemory P O seeds j t +
        P.alpha j • upperResidualBatchMean O (highBand P j)
          (batchDecision P (⟨t, ht⟩ : Fin P.T)
            (batchHistoryOfRun P O ⟨t, ht⟩
              ((⟨0, P.T_pos⟩ : Fin P.T), seeds)))
          (batchCenter P (⟨t, ht⟩ : Fin P.T)
            (batchHistoryOfRun P O ⟨t, ht⟩
              ((⟨0, P.T_pos⟩ : Fin P.T), seeds)))
          (batchSeedBlock P ⟨t, ht⟩ seeds) := by
  let u : Fin P.T := ⟨t, ht⟩
  let r : Fin P.T := ⟨0, P.T_pos⟩
  let z : Fin P.T × (Fin (responseCount P) → Seed) := (r, seeds)
  let H := batchHistoryOfRun P O u z
  have ht0 : t ≤ P.T := Nat.le_of_lt ht
  have ht1 : t + 1 ≤ P.T := Nat.succ_le_iff.mpr ht
  have hpre := boundaryTranscript_eq_batchHistory P O u z
  have hpost := boundaryTranscript_succ_eq_batchEndTranscript P O u z
  have htime := batchStart_succ_eq_batchEndTime P u
  have hbefore : actualRuntimeMemory P O seeds j t =
      memories P (stateAt P (batchStart P u.val) H.2) j := by
    simp only [actualRuntimeMemory, dif_pos ht0]
    rw [hpre]
  have hafter : actualRuntimeMemory P O seeds j (t + 1) =
      memories P (stateAt P (batchEndTime P u)
        (batchEndTranscript P O r u seeds)) j := by
    simp only [actualRuntimeMemory, dif_pos ht1]
    rw [← stateAt_transcript_cast P htime
      (boundaryTranscript P O (u.val + 1) ht1 z)]
    rw [hpost]
  have hrec := actualBatch_memory_eq_highEMA P O r u seeds j
  calc
    actualRuntimeMemory P O seeds j (t + 1) =
        memories P (stateAt P (batchEndTime P u)
          (batchEndTranscript P O r u seeds)) j := hafter
    _ = (1 - P.alpha j) •
          memories P (stateAt P (batchStart P u.val) H.2) j +
        P.alpha j • upperResidualBatchMean O (highBand P j)
          (batchDecision P u H) (batchCenter P u H)
          (batchSeedBlock P u seeds) := hrec
    _ = (1 - P.alpha j) • actualRuntimeMemory P O seeds j t +
        P.alpha j • upperResidualBatchMean O (highBand P j)
          (batchDecision P u H) (batchCenter P u H)
          (batchSeedBlock P u seeds) := by rw [hbefore]

end

end HeavyTailedNoise.UpperK1
