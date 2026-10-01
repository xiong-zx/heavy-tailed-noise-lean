import HeavyTailedNoise.Upper.K1.CoarseTrackerActualTerminal
import HeavyTailedNoise.Upper.Foundations.CoarseTracker

/-!
The exact canonical batch terminal point and center move by deterministic
amounts.  The center uses the first response of the same completed batch,
but clipping caps its move pathwise; no independence or moment of that
response is needed.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualBatch_terminal_motion_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (r u : Fin P.T) (seeds : Fin (responseCount P) → Seed)
    (hh : 0 ≤ P.h) (hbeta : 0 ≤ P.beta) :
    let H := batchHistoryOfRun P O u (r, seeds)
    ‖point P (stateAt P (batchEndTime P u)
        (batchEndTranscript P O r u seeds)) -
      batchDecision P u H‖ ≤ P.h ∧
    ‖center P (stateAt P (batchEndTime P u)
        (batchEndTranscript P O r u seeds)) -
      batchCenter P u H‖ ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ := by
  dsimp only
  let H := batchHistoryOfRun P O u (r, seeds)
  let block := batchSeedBlock P u seeds
  have hterminal := actualBatch_terminal_point_center P O r u seeds
  constructor
  · rw [hterminal.1]
    exact normalized_step_norm_le P
      (batchDecision P u H)
      (batchEstimateOnHistory P O u H block) hh
  · rw [hterminal.2]
    exact coarseCenter_increment_norm_le P
      (batchCenter P u H)
      (O.response (batchDecision P u H)
        (block ⟨0, P.n_pos⟩)) hbeta

/-- The same-seed q-WAS displacement factor for adjacent canonical batch
states is deterministic, despite the first response being reused in the
center update. -/
theorem actualBatch_terminal_qwas_displacement_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (r u : Fin P.T) (seeds : Fin (responseCount P) → Seed)
    (hh : 0 ≤ P.h) (hbeta : 0 ≤ P.beta) :
    let H := batchHistoryOfRun P I.oracle u (r, seeds)
    Lbar * ‖point P (stateAt P (batchEndTime P u)
        (batchEndTranscript P I.oracle r u seeds)) -
      batchDecision P u H‖ +
      ‖center P (stateAt P (batchEndTime P u)
        (batchEndTranscript P I.oracle r u seeds)) -
        batchCenter P u H‖ ≤
      Lbar * P.h +
        P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ := by
  dsimp only
  have hmotion := actualBatch_terminal_motion_le P I.oracle r u seeds hh hbeta
  exact add_le_add
    (mul_le_mul_of_nonneg_left hmotion.1 I.Lbar_pos.le)
    hmotion.2

end

end HeavyTailedNoise.UpperK1
