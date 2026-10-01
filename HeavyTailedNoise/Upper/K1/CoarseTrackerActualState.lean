import HeavyTailedNoise.Upper.K1.BatchPathFiltration
import HeavyTailedNoise.Upper.Foundations.CoarseTrackerFreshBatchDrift

/-!
The current algorithm's state transition along one consecutive response
block. This reconstructs the state through the unique `Algorithm.step` rather
than introducing a second center or direction update. Later results identify
the block with an actual runtime batch and its pre-batch transcript.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Repeatedly apply the actual response-by-response state transition after
the given global response index. Each entry is a returned vector, not a new
oracle call made by this definition. -/
def foldResponses {d : ℕ} (start : ℕ) (s : State d P.J) :
    (k : ℕ) → (Fin k → Point d) → State d P.J
  | 0, _ => s
  | k + 1, ys =>
      step P (start + k)
        (foldResponses start s k (fun i => ys i.castSucc))
        (ys (Fin.last k))

@[simp] theorem foldResponses_zero {d : ℕ} (start : ℕ) (s : State d P.J)
    (ys : Fin 0 → Point d) : foldResponses P start s 0 ys = s := rfl

theorem foldResponses_succ {d : ℕ} (start : ℕ) (s : State d P.J)
    (k : ℕ) (ys : Fin (k + 1) → Point d) :
    foldResponses P start s (k + 1) ys =
      step P (start + k)
        (foldResponses P start s k (fun i => ys i.castSucc))
        (ys (Fin.last k)) := rfl

/-- Any measurable pre-block state and returned-vector block determine a
measurable post-block state. -/
theorem measurable_foldResponses {d : ℕ} (start k : ℕ) :
    Measurable (fun z : State d P.J × (Fin k → Point d) =>
      foldResponses P start z.1 k z.2) := by
  induction k with
  | zero =>
      exact measurable_fst
  | succ k ih =>
      have hprefix : Measurable
          (fun z : State d P.J × (Fin (k + 1) → Point d) =>
            (z.1, (fun i : Fin k => z.2 i.castSucc))) := by
        apply measurable_fst.prodMk
        apply measurable_pi_iff.mpr
        intro i
        exact (measurable_pi_apply i.castSucc).comp measurable_snd
      have hlast : Measurable
          (fun z : State d P.J × (Fin (k + 1) → Point d) =>
            z.2 (Fin.last k)) :=
        (measurable_pi_apply (Fin.last k)).comp measurable_snd
      change Measurable (fun z : State d P.J × (Fin (k + 1) → Point d) =>
        step P (start + k)
          (foldResponses P start z.1 k (fun i => z.2 i.castSucc))
          (z.2 (Fin.last k)))
      simpa only [Function.comp_def] using
        (measurable_step P (start + k)).comp ((ih.comp hprefix).prodMk hlast)

end

end HeavyTailedNoise.UpperK1
