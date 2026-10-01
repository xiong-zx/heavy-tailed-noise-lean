import HeavyTailedNoise.Upper.K1.EMADriftExpectation
import HeavyTailedNoise.Upper.K1.EMADriftCanonical
import HeavyTailedNoise.Upper.K1.MeanDriftPrivate

/-!
The true estimator's EMA mean-lag time sum under the original seed-only
law.  The private output index disappears by the already verified
response-free transcript rule, and the boundary source sequence is
identified with the one in the canonical estimator decomposition.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem measurable_aggregate_actualBoundaryMeanLag
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ) :
    Measurable (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
      aggregateMeanLag P (actualBandSourceSequence P O z) t) := by
  have heq : (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
      aggregateMeanLag P (actualBandSourceSequence P O z) t) =
      (fun z => -∑ u ∈ Finset.range t,
        ∑ j : Fin P.J,
          (1 - P.alpha j) ^ (t - u) •
            (actualBandSourceSequence P O z j (u + 2) -
              actualBandSourceSequence P O z j (u + 1))) := by
    funext z
    exact aggregateMeanLag_eq_source_moves P
      (actualBandSourceSequence P O z) t
  rw [heq]
  apply Measurable.neg
  apply Finset.measurable_sum
  intro u hu
  apply Finset.measurable_sum
  intro j hj
  exact (measurable_const : Measurable
    (fun _ : Fin P.T × (Fin (responseCount P) → Seed) =>
      ((1 - P.alpha j) ^ (t - u) : ℝ))).smul
    ((measurable_actualBandSourceSequence P O j (u + 2)).sub
      (measurable_actualBandSourceSequence P O j (u + 1)))

theorem paperSchedule_actualMeanLag_seed_lintegral_sum_le
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hκ : 0 < κ) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
    (∫⁻ seeds : Fin (responseCount P) → Seed,
      ENNReal.ofReal
        (∑ t ∈ Finset.range P.T,
          ‖actualMeanLag P I.oracle seeds t‖)
      ∂freshSeedLaw I.oracle (responseCount P)) ≤
      ENNReal.ofReal κ * (P.T : ENNReal) *
        ENNReal.ofReal (paperMeanDriftConstant p q * ε) := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  let r₀ : Fin P.T := ⟨0, P.T_pos⟩
  let f : Fin P.T × (Fin (responseCount P) → Seed) → ENNReal :=
    fun z => ENNReal.ofReal
      (∑ t ∈ Finset.range P.T,
        ‖aggregateMeanLag P
          (actualBandSourceSequence P I.oracle z) t‖)
  have hf : Measurable f := by
    dsimp [f]
    apply ENNReal.measurable_ofReal.comp
    apply Finset.measurable_sum
    intro t ht
    exact (measurable_aggregate_actualBoundaryMeanLag P I.oracle t).norm
  have hind (r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
      f (r, seeds) = f (r₀, seeds) := by
    have hsrc : actualBandSourceSequence P I.oracle (r, seeds) =
        actualBandSourceSequence P I.oracle (r₀, seeds) := by
      funext j t
      exact actualBandSourceSequence_private_independent
        P I.oracle j t r r₀ seeds
    simp only [f, hsrc]
  have hproduct := paperSchedule_actualAggregateMeanLag_lintegral_sum_le
    p q Δ σ Lbar ε Ctail κ Cb CI hp hq hε hκ hCb hCI I
  have htransport := lintegral_private_independent P I.oracle f hf r₀ hind
  have hcanonical (seeds : Fin (responseCount P) → Seed) :
      (∑ t ∈ Finset.range P.T,
        ‖actualMeanLag P I.oracle seeds t‖) =
      (∑ t ∈ Finset.range P.T,
        ‖aggregateMeanLag P
          (actualBandSourceSequence P I.oracle (r₀, seeds)) t‖) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [actualMeanLag_eq_boundarySourceLag P I.oracle seeds t
      (Finset.mem_range.mp ht)]
  change (∫⁻ seeds, ENNReal.ofReal
    (∑ t ∈ Finset.range P.T,
      ‖actualMeanLag P I.oracle seeds t‖)
      ∂freshSeedLaw I.oracle (responseCount P)) ≤ _
  calc
    (∫⁻ seeds, ENNReal.ofReal
      (∑ t ∈ Finset.range P.T,
        ‖actualMeanLag P I.oracle seeds t‖)
      ∂freshSeedLaw I.oracle (responseCount P)) =
        ∫⁻ seeds, f (r₀, seeds)
          ∂freshSeedLaw I.oracle (responseCount P) := by
            apply lintegral_congr
            intro seeds
            rw [hcanonical seeds]
    _ = (∫⁻ z, f z ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P)))) := htransport.symm
    _ ≤ ENNReal.ofReal κ * (P.T : ENNReal) *
        ENNReal.ofReal (paperMeanDriftConstant p q * ε) := hproduct

/-- For finite `q>1`, the actual source-mean EMA lag contributes at most
`κ C_D(p,q) ε` to the normalized time-average estimator error. -/
theorem paperSchedule_actualMeanLag_seed_average_le
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hκ : 0 < κ) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
    (P.T : ENNReal)⁻¹ *
      (∫⁻ seeds : Fin (responseCount P) → Seed,
        ENNReal.ofReal
          (∑ t ∈ Finset.range P.T,
            ‖actualMeanLag P I.oracle seeds t‖)
        ∂freshSeedLaw I.oracle (responseCount P)) ≤
      ENNReal.ofReal
        (paperMeanDriftConstant p q * κ * ε) := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  let D := paperMeanDriftConstant p q
  have hT0 : (P.T : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt P.T_pos)
  have hTtop : (P.T : ENNReal) ≠ ⊤ := by simp
  have hbound := paperSchedule_actualMeanLag_seed_lintegral_sum_le
    p q Δ σ Lbar ε Ctail κ Cb CI hp hq hε hκ hCb hCI I
  calc
    (P.T : ENNReal)⁻¹ *
        (∫⁻ seeds : Fin (responseCount P) → Seed,
          ENNReal.ofReal
            (∑ t ∈ Finset.range P.T,
              ‖actualMeanLag P I.oracle seeds t‖)
          ∂freshSeedLaw I.oracle (responseCount P)) ≤
        (P.T : ENNReal)⁻¹ *
          (ENNReal.ofReal κ * (P.T : ENNReal) *
            ENNReal.ofReal (D * ε)) :=
              by simpa only [mul_comm] using
                (mul_le_mul_right hbound ((P.T : ENNReal)⁻¹))
    _ = ENNReal.ofReal κ * ENNReal.ofReal (D * ε) := by
      calc
        _ = (P.T : ENNReal)⁻¹ *
            ((P.T : ENNReal) *
              (ENNReal.ofReal κ * ENNReal.ofReal (D * ε))) := by
                ac_rfl
        _ = ENNReal.ofReal κ * ENNReal.ofReal (D * ε) :=
          ENNReal.inv_mul_cancel_left hT0 hTtop
    _ = ENNReal.ofReal (D * κ * ε) := by
      rw [← ENNReal.ofReal_mul hκ.le]
      congr 1
      ring

end

end HeavyTailedNoise.UpperK1
