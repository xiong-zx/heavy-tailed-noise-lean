import HeavyTailedNoise.Upper.K1.CoarseTrackerActualState
import HeavyTailedNoise.Upper.K1.BatchSeedProduct

/-!
A consecutive returned-vector block in the actual `stateAt` recursion is
exactly the fold of the unique `Algorithm.step` over those vectors. The block
is represented by entries of the existing gradient-only transcript, without
another oracle interface.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

def transcriptPrefix {d : ℕ} (t k : ℕ)
    (H : Transcript d (t + k)) : Transcript d t :=
  fun i => H ⟨i.val, by omega⟩

def transcriptBlockResponses {d : ℕ} (t k : ℕ)
    (H : Transcript d (t + k)) : Fin k → Point d :=
  fun j => (H ⟨t + j.val, by omega⟩).2

@[simp] theorem transcriptPrefix_zero {d : ℕ} (t : ℕ)
    (H : Transcript d (t + 0)) : transcriptPrefix t 0 H = H := by
  funext i
  rfl

theorem transcriptPrefix_of_succ {d : ℕ} (t k : ℕ)
    (H : Transcript d (t + (k + 1))) :
    transcriptPrefix t k (fun i : Fin (t + k) => H i.castSucc) =
      transcriptPrefix t (k + 1) H := by
  funext i
  dsimp [transcriptPrefix]

theorem transcriptBlockResponses_of_succ {d : ℕ} (t k : ℕ)
    (H : Transcript d (t + (k + 1))) :
    transcriptBlockResponses t k (fun i : Fin (t + k) => H i.castSucc) =
      (fun j : Fin k => (transcriptBlockResponses t (k + 1) H) j.castSucc) := by
  funext j
  dsimp [transcriptBlockResponses]

theorem transcriptBlockResponses_last {d : ℕ} (t k : ℕ)
    (H : Transcript d (t + (k + 1))) :
    (transcriptBlockResponses t (k + 1) H) (Fin.last k) =
      (H (Fin.last (t + k))).2 := by
  dsimp [transcriptBlockResponses]
  exact congrArg Prod.snd (congrArg H (Fin.ext rfl))

/-- Exact append identity for any transcript. It remains valid when the
recorded query positions are inconsistent, because the algorithm reads only
the returned vectors to rebuild its state. -/
theorem stateAt_eq_foldResponses {d : ℕ} (t k : ℕ)
    (H : Transcript d (t + k)) :
    stateAt P (t + k) H =
      foldResponses P t (stateAt P t (transcriptPrefix t k H)) k
        (transcriptBlockResponses t k H) := by
  induction k with
  | zero =>
      simp [foldResponses, transcriptPrefix_zero]
  | succ k ih =>
      let Hprev : Transcript d (t + k) := fun i => H i.castSucc
      have hprev := ih Hprev
      change step P (t + k) (stateAt P (t + k) Hprev)
        (H (Fin.last (t + k))).2 = _
      rw [hprev, foldResponses_succ]
      rw [← transcriptPrefix_of_succ t k H,
        ← transcriptBlockResponses_of_succ t k H,
        transcriptBlockResponses_last]

end

end HeavyTailedNoise.UpperK1
