import HeavyTailedNoise.Upper.K1.KernelSourceMeanPhysicalMean
import HeavyTailedNoise.Upper.K1.KernelRuntimeCenterMove

/-!
The weighted high-band source-mean increment along one genuine completed
runtime batch.  The source means at the two endpoint states are compared
using the same auxiliary seed.  The actual center move is capped pathwise,
so the q-WAS displacement factor is deterministic even though the first
current response is reused by the center update.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem paperSchedule_actualBatch_highBand_sourceMean_drift_le
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    ∀ (r u : Fin P.T) (seeds : Fin (responseCount P) → Seed),
      let H := batchHistoryOfRun P I.oracle u (r, seeds)
      let x := batchDecision P u H
      let w := batchCenter P u H
      let x' := point P (stateAt P (batchEndTime P u)
        (batchEndTranscript P I.oracle r u seeds))
      let w' := center P (stateAt P (batchEndTime P u)
        (batchEndTranscript P I.oracle r u seeds))
      let s := paperSexp p q
      let ν := paperNu σ ε
      let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
      (∑ j : Fin P.J,
        (12 * (2 : ℝ) ^ j.val) ^ s *
          ‖upperResidualSourceMean I.oracle (highBand P j) x' w' -
            upperResidualSourceMean I.oracle (highBand P j) x w‖) ≤
        (2 * C / ν ^ s) *
          (((σ + ‖I.objective.grad x' - w'‖) +
              (σ + ‖I.objective.grad x - w‖)) ^ s *
            (Lbar * P.h +
              P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)) := by
  dsimp only
  intro r u seeds
  let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  let H := batchHistoryOfRun P I.oracle u (r, seeds)
  let x := batchDecision P u H
  let w := batchCenter P u H
  let x' := point P (stateAt P (batchEndTime P u)
    (batchEndTranscript P I.oracle r u seeds))
  let w' := center P (stateAt P (batchEndTime P u)
    (batchEndTranscript P I.oracle r u seeds))
  let s := paperSexp p q
  let ν := paperNu σ ε
  let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
  let K : ℝ := 2 * C / ν ^ s
  let A : ℝ := (σ + ‖I.objective.grad x' - w'‖) +
    (σ + ‖I.objective.grad x - w‖)
  let B : ℝ := Lbar * P.h +
    P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  have hh : 0 ≤ P.h := by
    dsimp [P, paperSchedule, paperStep]
    exact div_nonneg (mul_nonneg hch.le hε.le) I.Lbar_pos.le
  have hbeta : 0 ≤ P.beta := by
    dsimp [P, paperSchedule, paperBeta]
    positivity
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos (lt_trans zero_lt_one hp)
    apply sub_pos.mpr
    exact (div_lt_iff₀ (lt_trans zero_lt_one hq)).2
      (by simpa using hq)
  have hν : 0 < ν := paperNu_pos (σ := σ) hε
  have htwo : 1 < (2 : ℝ) ^ s :=
    Real.one_lt_rpow (by norm_num) hs
  have hC : 0 ≤ C := by
    dsimp [C]
    exact (div_pos (Real.rpow_pos_of_pos (by norm_num) s)
      (sub_pos.mpr htwo)).le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (add_nonneg I.sigma_nonneg (norm_nonneg _))
      (add_nonneg I.sigma_nonneg (norm_nonneg _))
  have hMean :
      (∑ j : Fin P.J,
        (12 * (2 : ℝ) ^ j.val) ^ s *
          ‖upperResidualSourceMean I.oracle (highBand P j) x' w' -
            upperResidualSourceMean I.oracle (highBand P j) x w‖) ≤
        K * (A ^ s *
          (Lbar * ‖x' - x‖ + ‖w' - w‖)) := by
    simpa only [P, K, A, C, ν, s] using
      (paperSchedule_highBand_sourceMean_drift_le_physical
        p q Δ σ Lbar ε Ctail ch κ Cb CI
        hp hq hε hch hCb hCI I x x' w w')
  have hMove : Lbar * ‖x' - x‖ + ‖w' - w‖ ≤ B := by
    simpa only [x, x', w, w', H, B] using
      (actualBatch_terminal_qwas_displacement_le P I r u seeds
        hh hbeta)
  calc
    (∑ j : Fin P.J,
      (12 * (2 : ℝ) ^ j.val) ^ s *
        ‖upperResidualSourceMean I.oracle (highBand P j) x' w' -
          upperResidualSourceMean I.oracle (highBand P j) x w‖) ≤
        K * (A ^ s *
          (Lbar * ‖x' - x‖ + ‖w' - w‖)) := hMean
    _ ≤ K * (A ^ s * B) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hMove (Real.rpow_nonneg hA _)) hK

end

end HeavyTailedNoise.UpperK1
