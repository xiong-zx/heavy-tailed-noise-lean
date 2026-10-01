import HeavyTailedNoise.Upper.K1.StationarityActualPath
import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialState

/-!
The genuine algorithm starts its runtime trajectory at zero. The optional
initialization responses alter memories, not the point. The state fact is
imported from the unique initialization analysis.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualRuntimePoint_zero {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) :
    actualRuntimePoint P O seeds 0 = 0 := by
  have hstate := (stateAt_firstRuntime_point_center P
    (boundaryTranscript P O 0 (Nat.zero_le P.T)
      ((⟨0, P.T_pos⟩ : Fin P.T), seeds))).1
  simpa [actualRuntimePoint] using hstate

end

end HeavyTailedNoise.UpperK1
