import HeavyTailedNoise.Upper.K1.EMADriftAverage
import HeavyTailedNoise.Upper.K1.ActualEstimatorKernelIdentity

/-!
The actual estimator's high-band EMA mean lag vanishes exactly in each of
the manuscript's no-lag endpoint branches.  These are pointwise identities
on the original oracle seed tape, including the first runtime time.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualMeanLag_of_alpha_one
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed)
    (hα : ∀ j : Fin P.J, P.alpha j = 1) (t : ℕ) :
    actualMeanLag P O seeds t = 0 := by
  change aggregateMeanLag P
    (fun j v => actualBandSourceMean P O seeds j (v - 1)) t = 0
  exact aggregateMeanLag_of_alpha_one P _ hα t

theorem actualMeanLag_no_bands
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed)
    (hJ : P.J = 0) (t : ℕ) :
    actualMeanLag P O seeds t = 0 := by
  change aggregateMeanLag P
    (fun j v => actualBandSourceMean P O seeds j (v - 1)) t = 0
  exact aggregateMeanLag_no_bands P _ hJ t

theorem paperSchedule_actualMeanLag_q_one
    (p Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    (hκ : 0 < κ) (hκle : κ ≤ 1)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) :
    let P := paperSchedule p 1 Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
    ∀ (seeds : Fin (responseCount P) → Seed) (t : ℕ),
      actualMeanLag P O seeds t = 0 := by
  dsimp only
  intro seeds t
  let P := paperSchedule p 1 Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  apply actualMeanLag_of_alpha_one P O seeds
  intro j
  change paperAlpha p 1 κ j.val = 1
  exact paperAlpha_q_one p κ hκ hκle j.val

end

end HeavyTailedNoise.UpperK1
