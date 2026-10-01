import HeavyTailedNoise.Upper.K1.CoarseTrackerActualMemoryProcess
import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialMemoryState
import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialFirstCenter

/-!
The initial high-band memories of the one logged algorithm use the global
seed tape. The first response fixes the clipping center. The optional
initialization block begins at global response index one and contains no
copy of that first seed.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- In the absent-initialization branch, every high-band memory at the first
runtime boundary is exactly zero. This includes `q=1` with nonempty bands. -/
theorem actualRuntimeMemory_zero_of_no_initial {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (j : Fin P.J)
    (hzero : initialResponses P = 0) :
    actualRuntimeMemory P O seeds j 0 = 0 := by
  let r : Fin P.T := ⟨0, P.T_pos⟩
  let H₀ := boundaryTranscript P O 0 (Nat.zero_le P.T) (r, seeds)
  have htime : batchStart P 0 = 1 := by simp [batchStart, hzero]
  let H : Transcript d 1 := fun i => H₀ (i.cast htime.symm)
  have hstate : stateAt P (batchStart P 0) H₀ = stateAt P 1 H :=
    (stateAt_transcript_cast P htime H₀).symm
  have hreadout : actualRuntimeMemory P O seeds j 0 =
      memories P (stateAt P (batchStart P 0) H₀) j := by
    simp only [actualRuntimeMemory, dif_pos (Nat.zero_le P.T)]
    rfl
  rw [hreadout, hstate]
  exact congrFun (stateAt_one_memories_zero P H) j

/-- A present initialization batch is the actual sample mean centered at
the response to seed zero. The `i`th summand uses global seed `1+i`. -/
theorem actualRuntimeMemory_zero_eq_initialBatch {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (j : Fin P.J)
    (hpos : 0 < initialResponses P) :
    actualRuntimeMemory P O seeds j 0 =
      upperResidualBatchMean O (highBand P j) 0
        (O.response 0 (seeds ⟨0, responseCount_pos P⟩))
        (initialSeedBlock P seeds) := by
  let r : Fin P.T := ⟨0, P.T_pos⟩
  let H₀ := boundaryTranscript P O 0 (Nat.zero_le P.T) (r, seeds)
  have htime : batchStart P 0 = 1 + initialResponses P := by
    simp [batchStart]
  let H : Transcript d (1 + initialResponses P) :=
    fun i => H₀ (i.cast htime.symm)
  have hstate : stateAt P (batchStart P 0) H₀ =
      stateAt P (1 + initialResponses P) H :=
    (stateAt_transcript_cast P htime H₀).symm
  have hcoord (i : Fin (1 + initialResponses P)) :
      H i = (runTranscript O (algorithm (d := d) P) r
        (responseCount P) seeds)
          ⟨i.val, by
            have hi := i.isLt
            dsimp [responseCount] at hi ⊢
            omega⟩ := by
    dsimp [H, H₀, boundaryTranscript]
    exact congrArg
      (runTranscript O (algorithm (d := d) P) r
        (responseCount P) seeds) (Fin.ext rfl)
  have hfirst :
      (H ⟨0, by omega⟩).2 =
        O.response 0 (seeds ⟨0, responseCount_pos P⟩) := by
    rw [hcoord]
    exact first_logged_response_eq_oracle P O r seeds
  have hcenter :
      center P (stateAt P 1
        (transcriptPrefix 1 (initialResponses P) H)) =
        O.response 0 (seeds ⟨0, responseCount_pos P⟩) := by
    rw [(stateAt_firstResponse_point_center P
      (transcriptPrefix 1 (initialResponses P) H)).2]
    simpa only [transcriptPrefix] using hfirst
  have hblock (i : Fin (initialResponses P)) :
      (transcriptBlockResponses 1 (initialResponses P) H) i =
        O.response 0 (initialSeedBlock P seeds i) := by
    change (H ⟨1 + i.val, by omega⟩).2 = _
    rw [hcoord]
    exact initial_logged_response_eq_oracle P O r seeds i
  have hmem := stateAt_initial_memory_of_pos P hpos H j
  change memories P (stateAt P (1 + initialResponses P) H) j = _ at hmem
  rw [hcenter] at hmem
  simp_rw [hblock] at hmem
  have hreadout : actualRuntimeMemory P O seeds j 0 =
      memories P (stateAt P (batchStart P 0) H₀) j := by
    simp only [actualRuntimeMemory, dif_pos (Nat.zero_le P.T)]
    rfl
  rw [hreadout, hstate]
  simpa only [upperResidualBatchMean] using hmem

end

end HeavyTailedNoise.UpperK1
