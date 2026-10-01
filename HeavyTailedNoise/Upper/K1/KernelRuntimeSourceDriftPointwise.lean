import HeavyTailedNoise.Upper.K1.KernelRuntimeSourceDriftReadout

/-!
The physical same-seed drift bound expressed through opaque readouts of
the one canonical full transcript.  This isolates the exact product-path
and tracker-error equalities from the later outer integral.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

theorem paperSchedule_actualHighBandSourceDrift_pointwise
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    let s := paperSexp p q
    let ν := paperNu σ ε
    let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
    let K : ℝ := 2 * C / ν ^ s
    let B : ℝ := Lbar * P.h +
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
    ∀ (u : Fin P.T)
      (z : Fin P.T × (Fin (responseCount P) → Seed)),
      actualHighBandSourceDrift P I.oracle s u z ≤
        K * B * (actualTrackerPairScale P I u z) ^ s := by
  dsimp only
  intro u z
  rcases z with ⟨r, seeds⟩
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let z : Fin P.T × (Fin (responseCount P) → Seed) := (r, seeds)
  let s := paperSexp p q
  let ν := paperNu σ ε
  let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
  let K : ℝ := 2 * C / ν ^ s
  let B : ℝ := Lbar * P.h +
    P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  let H := batchHistoryOfRun P I.oracle u z
  let x := batchDecision P u H
  let w := batchCenter P u H
  let x' := point P (stateAt P (batchEndTime P u)
    (batchEndTranscript P I.oracle r u seeds))
  let w' := center P (stateAt P (batchEndTime P u)
    (batchEndTranscript P I.oracle r u seeds))
  have hpre : ‖I.objective.grad x - w‖ =
      actualTrackerAtBoundary P I u.val z :=
    actualPre_grad_sub_center_norm_eq_trackerBoundary P I u z
  have hpost : ‖I.objective.grad x' - w'‖ =
      actualTrackerAtBoundary P I (u.val + 1) z :=
    actualPost_grad_sub_center_norm_eq_trackerBoundary P I u z
  have hpath :=
    (paperSchedule_actualBatch_highBand_sourceMean_drift_le
      p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hp hq hε (by norm_num) hCb hCI I) r u seeds
  have hpath' : actualHighBandSourceDrift P I.oracle s u z ≤
      K * (((σ + ‖I.objective.grad x' - w'‖) +
        (σ + ‖I.objective.grad x - w‖)) ^ s * B) := by
    rw [actualHighBandSourceDrift]
    exact hpath
  have hscale : (σ + ‖I.objective.grad x' - w'‖) +
      (σ + ‖I.objective.grad x - w‖) =
        actualTrackerPairScale P I u z := by
    rw [hpost, hpre, actualTrackerPairScale]
    ring
  calc
    actualHighBandSourceDrift P I.oracle s u z ≤
        K * (((σ + ‖I.objective.grad x' - w'‖) +
          (σ + ‖I.objective.grad x - w‖)) ^ s * B) := hpath'
    _ = K * B * (actualTrackerPairScale P I u z) ^ s := by
      rw [hscale]
      ring

end

end HeavyTailedNoise.UpperK1
