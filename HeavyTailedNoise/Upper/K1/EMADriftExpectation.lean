import HeavyTailedNoise.Upper.K1.EMADriftActual
import HeavyTailedNoise.Upper.K1.MeanDriftScale

/-!
Finite-horizon expectation of the true high-band source-mean EMA lag under
the original private-index × global-seed product law.  The time sum is
bounded by `T κ C_D(p,q) ε`; the terminal scalar EMA mass is discarded only
after its nonnegativity is proved.  No band independence is used.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem paperSchedule_actualAggregateMeanLag_lintegral_sum_le
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hκ : 0 < κ) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
    let μ := (algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw I.oracle (responseCount P))
    (∫⁻ z : Fin P.T × (Fin (responseCount P) → Seed),
      ENNReal.ofReal
        (∑ t ∈ Finset.range P.T,
          ‖aggregateMeanLag P
            (actualBandSourceSequence P I.oracle z) t‖) ∂μ) ≤
      ENNReal.ofReal κ * (P.T : ENNReal) *
        ENNReal.ofReal (paperMeanDriftConstant p q * ε) := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  let s := paperSexp p q
  let D : ℝ := paperMeanDriftConstant p q * ε
  have hsource0 (u : ℕ)
      (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      0 ≤ actualSourceDriftAt P I.oracle s u z := by
    by_cases hu : u < P.T
    · rw [actualSourceDriftAt_eq P I.oracle s u hu z]
      exact actualHighBandSourceDrift_nonneg P I.oracle s ⟨u, hu⟩ z
    · rw [actualSourceDriftAt, dif_neg hu]
  have hpoint (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      ENNReal.ofReal
        (∑ t ∈ Finset.range P.T,
          ‖aggregateMeanLag P
            (actualBandSourceSequence P I.oracle z) t‖) ≤
      ENNReal.ofReal κ *
        (∑ u ∈ Finset.range P.T,
          ENNReal.ofReal (actualSourceDriftAt P I.oracle s u z)) := by
    have hreal := paperSchedule_actualAggregateMeanLag_sum_le_sourceDrift
      p q Δ σ Lbar ε Ctail κ Cb CI hε hCb hCI hκ I.oracle z
    calc
      ENNReal.ofReal
          (∑ t ∈ Finset.range P.T,
            ‖aggregateMeanLag P
              (actualBandSourceSequence P I.oracle z) t‖) ≤
          ENNReal.ofReal
            (κ * (∑ u ∈ Finset.range P.T,
              actualSourceDriftAt P I.oracle s u z)) :=
            ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal κ *
          ENNReal.ofReal
            (∑ u ∈ Finset.range P.T,
              actualSourceDriftAt P I.oracle s u z) := by
            rw [ENNReal.ofReal_mul hκ.le]
      _ = ENNReal.ofReal κ *
          (∑ u ∈ Finset.range P.T,
            ENNReal.ofReal (actualSourceDriftAt P I.oracle s u z)) := by
            rw [ENNReal.ofReal_sum_of_nonneg
              (fun u _ => hsource0 u z)]
  have hmeas (u : ℕ) : Measurable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        ENNReal.ofReal (actualSourceDriftAt P I.oracle s u z)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_actualSourceDriftAt P I.oracle s u)
  have hone (u : ℕ) (hu : u ∈ Finset.range P.T) :
      (∫⁻ z, ENNReal.ofReal
        (actualSourceDriftAt P I.oracle s u z) ∂μ) ≤
      ENNReal.ofReal D := by
    have hu' : u < P.T := Finset.mem_range.mp hu
    let uu : Fin P.T := ⟨u, hu'⟩
    have hphysical :=
      paperSchedule_actualBatch_highBand_sourceMean_drift_epsilon_le
        p q Δ σ Lbar ε Ctail κ Cb CI hp hq hε hCb hCI I uu
    calc
      (∫⁻ z, ENNReal.ofReal
        (actualSourceDriftAt P I.oracle s u z) ∂μ) =
          (∫⁻ z, ENNReal.ofReal
            (actualHighBandSourceDrift P I.oracle s uu z) ∂μ) := by
              apply lintegral_congr
              intro z
              rw [actualSourceDriftAt_eq P I.oracle s u hu' z]
      _ ≤ ENNReal.ofReal D := hphysical
  calc
    (∫⁻ z, ENNReal.ofReal
      (∑ t ∈ Finset.range P.T,
        ‖aggregateMeanLag P
          (actualBandSourceSequence P I.oracle z) t‖) ∂μ) ≤
        ∫⁻ z, ENNReal.ofReal κ *
          (∑ u ∈ Finset.range P.T,
            ENNReal.ofReal (actualSourceDriftAt P I.oracle s u z)) ∂μ :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal κ *
        (∑ u ∈ Finset.range P.T,
          ∫⁻ z, ENNReal.ofReal
            (actualSourceDriftAt P I.oracle s u z) ∂μ) := by
      rw [lintegral_const_mul' (ENNReal.ofReal κ) _ (by simp)]
      rw [lintegral_finsetSum (Finset.range P.T)
        (fun u _ => hmeas u)]
    _ ≤ ENNReal.ofReal κ *
        (∑ _u ∈ Finset.range P.T, ENNReal.ofReal D) := by
      gcongr with u hu
      exact hone u hu
    _ = ENNReal.ofReal κ * (P.T : ENNReal) * ENNReal.ofReal D := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

end

end HeavyTailedNoise.UpperK1
