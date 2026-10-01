import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialMemoryState

/-!
Every optional initialization response is queried at the original point
zero. This is a pathwise consequence of the one algorithm's state fold;
the initial first response sets only the coarse center.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem initial_query_zero {d : ℕ} (k : ℕ)
    (hk : k ≤ initialResponses P)
    (H : Transcript d (1 + k)) :
    query P (1 + k) H = 0 := by
  change point P (stateAt P (1 + k) H) = 0
  have hfold := stateAt_eq_foldResponses P 1 k H
  rw [hfold]
  have hstart := stateAt_firstResponse_point_center P
    (transcriptPrefix 1 k H)
  have hfreeze := foldResponses_initial_point_center P
    (stateAt P 1 (transcriptPrefix 1 k H)) k hk
    (transcriptBlockResponses 1 k H)
  exact hfreeze.1.trans hstart.1

end

end HeavyTailedNoise.UpperK1
