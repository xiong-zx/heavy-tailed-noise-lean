import HeavyTailedNoise.Upper.K1.KernelWeightedShellDrift
import HeavyTailedNoise.Analysis.Smoothness

/-!
One auxiliary oracle seed couples two source residuals. The mean increment of
each high band is formed before summing dyadic weights; all bands of that seed
remain correlated. The mixed-product integrability boundary is explicit here
and is discharged later by q-WAS/Hölder and endpoint residual p moments.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The same-seed weighted source-mean drift is bounded by the expectation of
the pointwise active-dyadic increment. This theorem never invokes an
absolute residual q moment. -/
theorem paperSchedule_highBand_sourceMean_drift_le_of_mix_integrable
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar)
    (x x' w w' : Point d)
    (hMixInt : Integrable (fun ξ : Seed =>
      2 * ‖(I.oracle.response x' ξ - w') -
        (I.oracle.response x ξ - w)‖ *
        (((2 : ℝ) ^ paperSexp p q /
          ((2 : ℝ) ^ paperSexp p q - 1)) *
          (min ((max ‖I.oracle.response x' ξ - w'‖
              ‖I.oracle.response x ξ - w‖) / paperNu σ ε)
            (12 * (2 : ℝ) ^ paperJ p σ ε Ctail)) ^ paperSexp p q))
      I.oracle.law) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    (∑ j : Fin P.J,
      (12 * (2 : ℝ) ^ j.val) ^ paperSexp p q *
        ‖upperResidualSourceMean I.oracle (highBand P j) x' w' -
          upperResidualSourceMean I.oracle (highBand P j) x w‖) ≤
      ∫ ξ : Seed,
        2 * ‖(I.oracle.response x' ξ - w') -
          (I.oracle.response x ξ - w)‖ *
          (((2 : ℝ) ^ paperSexp p q /
            ((2 : ℝ) ^ paperSexp p q - 1)) *
            (min ((max ‖I.oracle.response x' ξ - w'‖
                ‖I.oracle.response x ξ - w‖) / paperNu σ ε)
              (12 * (2 : ℝ) ^ paperJ p σ ε Ctail)) ^ paperSexp p q)
        ∂I.oracle.law := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  let s := paperSexp p q
  let ν := paperNu σ ε
  let X : Seed → Point d := fun ξ => I.oracle.response x ξ - w
  let Y : Seed → Point d := fun ξ => I.oracle.response x' ξ - w'
  let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
  let U : ℝ := 12 * (2 : ℝ) ^ P.J
  let F : Seed → ℝ := fun ξ =>
    2 * ‖Y ξ - X ξ‖ * (C *
      (min ((max ‖Y ξ‖ ‖X ξ‖) / ν) U) ^ s)
  have hsource (j : Fin P.J) (a b : Point d) :
      Integrable (fun ξ => highBand P j (I.oracle.response a ξ - b))
        I.oracle.law :=
    upperResidualSource_integrable I.oracle (highBand P j)
      (measurable_highBand P j)
      (P.tau j.succ + P.tau j.castSucc)
      (fun z => highBand_norm_le P j z) a b
  have hdiff (j : Fin P.J) : Integrable
      (fun ξ => highBand P j (Y ξ) - highBand P j (X ξ))
      I.oracle.law := (hsource j x' w').sub (hsource j x w)
  have hweight (j : Fin P.J) :
      0 ≤ (12 * (2 : ℝ) ^ j.val) ^ s :=
    Real.rpow_nonneg (by positivity) _
  have hterm (j : Fin P.J) :
      (12 * (2 : ℝ) ^ j.val) ^ s *
        ‖upperResidualSourceMean I.oracle (highBand P j) x' w' -
          upperResidualSourceMean I.oracle (highBand P j) x w‖ ≤
      ∫ ξ, (12 * (2 : ℝ) ^ j.val) ^ s *
        ‖highBand P j (Y ξ) - highBand P j (X ξ)‖
        ∂I.oracle.law := by
    have hmean : upperResidualSourceMean I.oracle (highBand P j) x' w' -
        upperResidualSourceMean I.oracle (highBand P j) x w =
        ∫ ξ, highBand P j (Y ξ) - highBand P j (X ξ)
          ∂I.oracle.law := by
      unfold upperResidualSourceMean
      rw [integral_sub (hsource j x' w') (hsource j x w)]
    rw [hmean, integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_integral_le_integral_norm _) (hweight j)
  have hsumInt : Integrable
      (fun ξ => ∑ j : Fin P.J,
        (12 * (2 : ℝ) ^ j.val) ^ s *
          ‖highBand P j (Y ξ) - highBand P j (X ξ)‖)
      I.oracle.law := by
    apply integrable_finset_sum
    intro j hj
    exact (hdiff j).norm.const_mul _
  calc
    (∑ j : Fin P.J,
      (12 * (2 : ℝ) ^ j.val) ^ s *
        ‖upperResidualSourceMean I.oracle (highBand P j) x' w' -
          upperResidualSourceMean I.oracle (highBand P j) x w‖) ≤
      ∑ j : Fin P.J,
        ∫ ξ, (12 * (2 : ℝ) ^ j.val) ^ s *
          ‖highBand P j (Y ξ) - highBand P j (X ξ)‖
          ∂I.oracle.law := by
            apply Finset.sum_le_sum
            intro j hj
            exact hterm j
    _ = ∫ ξ, ∑ j : Fin P.J,
          (12 * (2 : ℝ) ^ j.val) ^ s *
            ‖highBand P j (Y ξ) - highBand P j (X ξ)‖
          ∂I.oracle.law := by
            rw [integral_finsetSum]
            intro j hj
            exact (hdiff j).norm.const_mul _
    _ ≤ ∫ ξ, F ξ ∂I.oracle.law := by
      apply integral_mono hsumInt
      · simpa only [F, X, Y, C, U, ν, s, P, paperSchedule] using hMixInt
      · intro ξ
        exact paperSchedule_weighted_highBand_sub_sum_le
          p q Δ σ Lbar ε Ctail ch κ Cb CI
          hp hq hε hch hCb hCI (Y ξ) (X ξ)
    _ = _ := by rfl

end

end HeavyTailedNoise.UpperK1
