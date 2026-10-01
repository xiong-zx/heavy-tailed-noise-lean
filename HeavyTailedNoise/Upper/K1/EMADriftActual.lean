import HeavyTailedNoise.Upper.K1.EMADriftAverage
import HeavyTailedNoise.Upper.K1.MeanDriftActualSource

/-!
The deterministic EMA lag inequality instantiated on the one genuine
adaptive transcript and the same-source high-band drift readout.  The
randomness remains the original private choice and one global seed tape.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

irreducible_def actualSourceDriftAt
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (s : ℝ) (u : ℕ)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) : ℝ :=
  if hu : u < P.T then
    actualHighBandSourceDrift P O s ⟨u, hu⟩ z
  else 0

theorem actualSourceDriftAt_eq
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (s : ℝ) (u : ℕ)
    (hu : u < P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    actualSourceDriftAt P O s u z =
      actualHighBandSourceDrift P O s ⟨u, hu⟩ z := by
  rw [actualSourceDriftAt, dif_pos hu]

theorem measurable_actualSourceDriftAt
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (s : ℝ) (u : ℕ) :
    Measurable (actualSourceDriftAt P O s u) := by
  by_cases hu : u < P.T
  · change Measurable (fun z => actualSourceDriftAt P O s u z)
    simp only [actualSourceDriftAt, dif_pos hu]
    exact measurable_actualHighBandSourceDrift P O s ⟨u, hu⟩
  · change Measurable (fun z => actualSourceDriftAt P O s u z)
    simp only [actualSourceDriftAt, dif_neg hu]
    exact measurable_const

theorem paperSchedule_actualAggregateMeanLag_sum_le_sourceDrift
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    (hκ : 0 < κ)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
    ∀ z : Fin P.T × (Fin (responseCount P) → Seed),
      (∑ t ∈ Finset.range P.T,
        ‖aggregateMeanLag P (actualBandSourceSequence P O z) t‖) ≤
      κ * (∑ u ∈ Finset.range P.T,
        actualSourceDriftAt P O (paperSexp p q) u z) := by
  dsimp only
  intro z
  let P := paperSchedule p q Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  let s := paperSexp p q
  let μsrc := actualBandSourceSequence P O z
  have haverage := paperSchedule_aggregateMeanLag_sum_le_weighted_moves
    p q Δ σ Lbar ε Ctail κ Cb CI hε hCb hCI hκ μsrc
  change (∑ t ∈ Finset.range P.T, ‖aggregateMeanLag P μsrc t‖) ≤
    κ * (∑ u ∈ Finset.range P.T,
      ∑ j : Fin P.J,
        (12 * (2 : ℝ) ^ j.val) ^ s *
          ‖μsrc j (u + 2) - μsrc j (u + 1)‖) at haverage
  have hmove :
      (∑ u ∈ Finset.range P.T,
        ∑ j : Fin P.J,
          (12 * (2 : ℝ) ^ j.val) ^ s *
            ‖μsrc j (u + 2) - μsrc j (u + 1)‖) =
      (∑ u ∈ Finset.range P.T,
        actualSourceDriftAt P O s u z) := by
    apply Finset.sum_congr rfl
    intro u hu
    have hu : u < P.T := Finset.mem_range.mp hu
    let uu : Fin P.T := ⟨u, hu⟩
    calc
      (∑ j : Fin P.J,
        (12 * (2 : ℝ) ^ j.val) ^ s *
          ‖μsrc j (u + 2) - μsrc j (u + 1)‖) =
          actualHighBandSourceDrift P O s uu z := by
            exact actualBandSourceSequence_weighted_move_eq_drift
              P O s uu z
      _ = actualSourceDriftAt P O s u z :=
        (actualSourceDriftAt_eq P O s u hu z).symm
  rw [hmove] at haverage
  exact haverage

end

end HeavyTailedNoise.UpperK1
