import HeavyTailedNoise.Upper.K1.KernelSourceMeanPhysicalDrift

/-!
The fixed-endpoint physical bound on the weighted high-band source-mean
increment.  All high bands of each auxiliary seed remain correlated.  The
bound is pointwise in the four endpoint vectors, so the adaptive runtime
history can be substituted only in a later conditional-expectation layer.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem paperSchedule_highBand_sourceMean_drift_le_physical
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar)
    (x x' w w' : Point d) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
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
          (Lbar * ‖x' - x‖ + ‖w' - w‖)) := by
  dsimp only
  have hmean := paperSchedule_highBand_sourceMean_drift_le_mixed
    p q Δ σ Lbar ε Ctail ch κ Cb CI
    hp hq hε hch hCb hCI I x x' w w'
  have hphys := paperSchedule_kernel_mix_integral_le_physical
    p q Δ σ Lbar ε Ctail ch κ Cb CI
    hp hq hε hch hCb hCI I x x' w w'
  exact hmean.trans hphys

end

end HeavyTailedNoise.UpperK1
