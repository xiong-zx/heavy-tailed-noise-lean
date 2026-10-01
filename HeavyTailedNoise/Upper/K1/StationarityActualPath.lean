import HeavyTailedNoise.Upper.K1.StationarityCanonicalMeasurable
import HeavyTailedNoise.Upper.K1.CoarseTrackerActualTerminal
import HeavyTailedNoise.Upper.K1.CoarseTrackerBoundaryProcess

/-!
The actual runtime point and completed direction estimate on the canonical
oracle seed tape. The private output index is fixed only because it never
affects queries. Boundary transcripts and their pre-batch/next-batch
identities are imported from the unique tracker path module.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- The actual boundary point through the last runtime boundary, extended
constantly afterward solely to make a total analysis sequence. -/
def actualRuntimePoint {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ) : Point d :=
  let z : Fin P.T × (Fin (responseCount P) → Seed) :=
    (⟨0, P.T_pos⟩, seeds)
  if ht : t ≤ P.T then
    point P (stateAt P (batchStart P t)
      (boundaryTranscript P O t ht z))
  else
    point P (stateAt P (batchStart P P.T)
      (boundaryTranscript P O P.T (le_refl _) z))

/-- The actual completed estimate for a runtime batch; after the horizon its
zero extension is an analysis convention and draws no response. -/
def actualRuntimeEstimate {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (t : ℕ) : Point d :=
  if ht : t < P.T then
    let u : Fin P.T := ⟨t, ht⟩
    let z : Fin P.T × (Fin (responseCount P) → Seed) :=
      (⟨0, P.T_pos⟩, seeds)
    batchEstimateOnHistory P O u
      (batchHistoryOfRun P O u z) (batchSeedBlock P u seeds)
  else 0

/-- At every responsive runtime decision, the analysis point is exactly the
canonical query used by the existing uniform-output risk identity. -/
theorem actualRuntimePoint_eq_canonicalQuery {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (r : Fin P.T) :
    actualRuntimePoint P O seeds r.val =
      canonicalRuntimePoint P O r seeds := by
  let z : Fin P.T × (Fin (responseCount P) → Seed) :=
    (⟨0, P.T_pos⟩, seeds)
  have hpre := boundaryTranscript_eq_batchHistory P O r z
  have hseed : (batchHistoryOfRun P O r z).2 =
      runTranscript O (algorithm (d := d) P) (⟨0, P.T_pos⟩ : Fin P.T)
        (batchStart P r.val)
        (fun j : Fin (batchStart P r.val) =>
          seeds ⟨j.val, lt_trans j.isLt (outputIndex P r).isLt⟩) := by
    dsimp [batchHistoryOfRun, z]
    apply congrArg (fun f : Fin (batchStart P r.val) → Seed =>
      runTranscript O (algorithm (d := d) P)
        (⟨0, P.T_pos⟩ : Fin P.T) (batchStart P r.val) f)
    funext j
    exact congrArg seeds (Fin.ext rfl)
  simp only [actualRuntimePoint, dif_pos (Nat.le_of_lt r.isLt)]
  rw [hpre, hseed]
  rfl

theorem measurable_actualRuntimePoint_at {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (r : Fin P.T) :
    Measurable (fun seeds : Fin (responseCount P) → Seed =>
      actualRuntimePoint P O seeds r.val) := by
  have heq : (fun seeds : Fin (responseCount P) → Seed =>
      actualRuntimePoint P O seeds r.val) =
      canonicalRuntimePoint P O r := by
    funext seeds
    exact actualRuntimePoint_eq_canonicalQuery P O seeds r
  rw [heq]
  exact measurable_canonicalRuntimePoint P O r

/-- The genuine algorithm makes precisely the manuscript's normalized step
at every `t<T`. The center update and shared-batch estimate are supplied by
the already verified actual-batch terminal identity. -/
theorem actualRuntimePoint_step {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed)
    (t : ℕ) (ht : t < P.T) :
    actualRuntimePoint P O seeds (t + 1) =
      actualRuntimePoint P O seeds t -
        P.h • direction (actualRuntimeEstimate P O seeds t) := by
  let u : Fin P.T := ⟨t, ht⟩
  let z : Fin P.T × (Fin (responseCount P) → Seed) :=
    (⟨0, P.T_pos⟩, seeds)
  let H := batchHistoryOfRun P O u z
  have ht0 : t ≤ P.T := Nat.le_of_lt ht
  have ht1 : t + 1 ≤ P.T := Nat.succ_le_iff.mpr ht
  have hpre := boundaryTranscript_eq_batchHistory P O u z
  have hpost := boundaryTranscript_succ_eq_batchEndTranscript P O u z
  have htime := batchStart_succ_eq_batchEndTime P u
  have hx : actualRuntimePoint P O seeds t = batchDecision P u H := by
    simp only [actualRuntimePoint, dif_pos ht0]
    rw [hpre]
    rfl
  have hxnext : actualRuntimePoint P O seeds (t + 1) =
      point P (stateAt P (batchEndTime P u)
        (batchEndTranscript P O z.1 u z.2)) := by
    simp only [actualRuntimePoint, dif_pos ht1]
    rw [← stateAt_transcript_cast P htime
      (boundaryTranscript P O (u.val + 1) ht1 z)]
    rw [hpost]
  have hestimate : actualRuntimeEstimate P O seeds t =
      batchEstimateOnHistory P O u H (batchSeedBlock P u seeds) := by
    simp only [actualRuntimeEstimate, dif_pos ht]
    rfl
  have hterminal := actualBatch_terminal_point_center P O z.1 u z.2
  calc
    actualRuntimePoint P O seeds (t + 1) =
        point P (stateAt P (batchEndTime P u)
          (batchEndTranscript P O z.1 u z.2)) := hxnext
    _ = batchDecision P u H - P.h • direction
          (batchEstimateOnHistory P O u H (batchSeedBlock P u seeds)) := hterminal.1
    _ = actualRuntimePoint P O seeds t -
          P.h • direction (actualRuntimeEstimate P O seeds t) := by
            rw [hx, hestimate]

end

end HeavyTailedNoise.UpperK1
