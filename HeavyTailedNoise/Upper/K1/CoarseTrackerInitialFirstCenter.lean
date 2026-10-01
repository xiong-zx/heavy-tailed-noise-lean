import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialLoggedBatch

/-!
The coarse center at the first runtime boundary is the actual first oracle
response at point zero. Later optional initialization seeds do not affect it.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem first_logged_response_eq_oracle {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    (runTranscript O (algorithm (d := d) P) r
      (responseCount P) seeds ⟨0, responseCount_pos P⟩).2 =
      O.response 0 (seeds ⟨0, responseCount_pos P⟩) := by
  have hcount : 1 ≤ responseCount P := responseCount_pos P
  let seeds1 : Fin 1 → Seed := fun i => seeds (i.castLE hcount)
  have hprefix := runTranscript_prefix_le O (algorithm (d := d) P) r
    1 (responseCount P) hcount seeds (⟨0, by norm_num⟩ : Fin 1)
  have hindex : (⟨0, by norm_num⟩ : Fin 1).castLE hcount =
      (⟨0, responseCount_pos P⟩ : Fin (responseCount P)) := Fin.ext rfl
  rw [hindex] at hprefix
  have hpair := hprefix.trans (algorithm_last_response P O r 0 seeds1)
  have hy := congrArg Prod.snd hpair
  change (runTranscript O (algorithm (d := d) P) r
    (responseCount P) seeds ⟨0, responseCount_pos P⟩).2 =
      O.response (query P 0
        (runTranscript O (algorithm (d := d) P) r 0
          (fun i : Fin 0 => seeds1 i.castSucc)))
        (seeds1 (Fin.last 0)) at hy
  rw [query_zero] at hy
  have hseed : seeds1 (Fin.last 0) =
      seeds ⟨0, responseCount_pos P⟩ := by
    change seeds ((Fin.last 0).castLE hcount) = _
    congr 1
  rw [hseed] at hy
  exact hy

theorem firstRuntime_center_eq_firstResponse {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    center P (stateAt P (batchStart P 0)
      (boundaryTranscript P O 0 (Nat.zero_le P.T) z)) =
      O.response 0 (z.2 ⟨0, responseCount_pos P⟩) := by
  let H := boundaryTranscript P O 0 (Nat.zero_le P.T) z
  have hcenter := (stateAt_firstRuntime_point_center P H).2
  calc
    center P (stateAt P (batchStart P 0)
        (boundaryTranscript P O 0 (Nat.zero_le P.T) z)) =
        (H ⟨0, by dsimp [batchStart]; omega⟩).2 := hcenter
    _ = (runTranscript O (algorithm (d := d) P) z.1
          (responseCount P) z.2 ⟨0, responseCount_pos P⟩).2 := by
            dsimp only [H, boundaryTranscript]
            exact congrArg Prod.snd (congrArg
              (runTranscript O (algorithm (d := d) P) z.1
                (responseCount P) z.2) (Fin.ext rfl))
    _ = O.response 0 (z.2 ⟨0, responseCount_pos P⟩) :=
      first_logged_response_eq_oracle P O z.1 z.2

end

end HeavyTailedNoise.UpperK1
