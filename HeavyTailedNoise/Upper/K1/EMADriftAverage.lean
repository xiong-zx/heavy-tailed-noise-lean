import HeavyTailedNoise.Upper.K1.EMADriftScalar
import HeavyTailedNoise.Upper.K1.EMAAggregateLag

/-!
The exact finite-horizon EMA lag of arbitrary vector source means is
controlled by the same dyadically weighted source motion that appears in
the actual shared-seed drift theorem.  This is deterministic; probability
and the genuine trajectory are attached in a separate bridge.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- Literal `α_j=min(1,(κ t_j^s)⁻¹)` supplies the precise retention weight
needed by the finite telescoping identity, including `α_j=1`. -/
theorem paperAlpha_retention_le_weight
    (p q κ : ℝ) (hκ : 0 < κ) (j : ℕ) :
    1 - paperAlpha p q κ j ≤
      paperAlpha p q κ j *
        (κ * (12 * (2 : ℝ) ^ j) ^ paperSexp p q) := by
  let A : ℝ := (12 * (2 : ℝ) ^ j) ^ paperSexp p q
  let x : ℝ := κ * A
  have hA : 0 < A := by
    dsimp [A]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hx : 0 < x := mul_pos hκ hA
  change 1 - min 1 x⁻¹ ≤ min 1 x⁻¹ * x
  rcases le_total x 1 with hsmall | hlarge
  · have hinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx).2 hsmall
    rw [min_eq_left hinv]
    have hnonneg : 0 ≤ x := hx.le
    nlinarith
  · have hinv : x⁻¹ ≤ 1 := (inv_le_one₀ hx).2 hlarge
    rw [min_eq_right hinv]
    have hnonneg : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.le
    have hcancel : x⁻¹ * x = 1 := inv_mul_cancel₀ hx.ne'
    linarith

private theorem band_lag_mass_sum_le
    {q : ℝ} (P : Schedule q) (j : Fin P.J)
    (D : ℕ → ℝ) (hD : ∀ u, 0 ≤ D u)
    (W : ℝ) (hα : 0 < P.alpha j)
    (hαle : P.alpha j ≤ 1)
    (hret : 1 - P.alpha j ≤ P.alpha j * W) :
    (∑ t ∈ Finset.range P.T,
      emaDriftMass (1 - P.alpha j) D t) ≤
      W * (∑ u ∈ Finset.range P.T, D u) := by
  apply emaDriftMass_sum_le (1 - P.alpha j) W D P.T
  · linarith
  · linarith [hα]
  · nlinarith [hret]
  · exact hD

/-- The finite time average of the genuine EMA retention formula has no
factor `J` and no infinite tail.  The same source move is counted once with
its actual band coefficient, so cross-band correlations are untouched. -/
theorem paperSchedule_aggregateMeanLag_sum_le_weighted_moves
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    (hκ : 0 < κ)
    {d : ℕ}
    (μsrc : Fin (paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI).J →
      ℕ → Point d) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
    let s := paperSexp p q
    (∑ t ∈ Finset.range P.T, ‖aggregateMeanLag P μsrc t‖) ≤
      κ * (∑ u ∈ Finset.range P.T,
        ∑ j : Fin P.J,
          (12 * (2 : ℝ) ^ j.val) ^ s *
            ‖μsrc j (u + 2) - μsrc j (u + 1)‖) := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  let s := paperSexp p q
  let D : Fin P.J → ℕ → ℝ :=
    fun j u => ‖μsrc j (u + 2) - μsrc j (u + 1)‖
  let W : Fin P.J → ℝ :=
    fun j => κ * (12 * (2 : ℝ) ^ j.val) ^ s
  have hD (j : Fin P.J) (u : ℕ) : 0 ≤ D j u := norm_nonneg _
  have hband (j : Fin P.J) :
      (∑ t ∈ Finset.range P.T,
        emaDriftMass (1 - P.alpha j) (D j) t) ≤
        W j * (∑ u ∈ Finset.range P.T, D j u) := by
    have hα : 0 < P.alpha j := by
      change 0 < paperAlpha p q κ j.val
      exact paperAlpha_pos hκ j.val
    have hαle : P.alpha j ≤ 1 := by
      change paperAlpha p q κ j.val ≤ 1
      exact paperAlpha_le_one p q κ j.val
    have hret : 1 - P.alpha j ≤ P.alpha j * W j := by
      change 1 - paperAlpha p q κ j.val ≤
        paperAlpha p q κ j.val *
          (κ * (12 * (2 : ℝ) ^ j.val) ^ paperSexp p q)
      exact paperAlpha_retention_le_weight p q κ hκ j.val
    exact band_lag_mass_sum_le P j (D j) (hD j) (W j)
      hα hαle hret
  have hpoint (t : ℕ) :
      ‖aggregateMeanLag P μsrc t‖ ≤
        ∑ j : Fin P.J,
          emaDriftMass (1 - P.alpha j) (D j) t := by
    calc
      ‖aggregateMeanLag P μsrc t‖ ≤
          ∑ u ∈ Finset.range t, ∑ j : Fin P.J,
            |1 - P.alpha j| ^ (t - u) * D j u := by
              simpa only [D] using aggregateMeanLag_norm_le P μsrc t
      _ = ∑ j : Fin P.J,
          emaDriftMass (1 - P.alpha j) (D j) t := by
            have hb (j : Fin P.J) : 0 ≤ 1 - P.alpha j := by
              change 0 ≤ 1 - paperAlpha p q κ j.val
              exact sub_nonneg.mpr (paperAlpha_le_one p q κ j.val)
            have habs (j : Fin P.J) : |1 - P.alpha j| =
                1 - P.alpha j := abs_of_nonneg (hb j)
            simp_rw [habs]
            rw [Finset.sum_comm]
            rfl
  calc
    (∑ t ∈ Finset.range P.T, ‖aggregateMeanLag P μsrc t‖) ≤
        ∑ t ∈ Finset.range P.T, ∑ j : Fin P.J,
          emaDriftMass (1 - P.alpha j) (D j) t :=
            Finset.sum_le_sum fun t _ => hpoint t
    _ = ∑ j : Fin P.J, ∑ t ∈ Finset.range P.T,
          emaDriftMass (1 - P.alpha j) (D j) t := by
            rw [Finset.sum_comm]
    _ ≤ ∑ j : Fin P.J, W j *
          (∑ u ∈ Finset.range P.T, D j u) :=
            Finset.sum_le_sum fun j _ => hband j
    _ = κ * (∑ u ∈ Finset.range P.T,
          ∑ j : Fin P.J,
            (12 * (2 : ℝ) ^ j.val) ^ s * D j u) := by
            simp only [W]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            congr 1
            funext u
            apply Finset.sum_congr rfl
            intro j hj
            ring

/-- The manuscript's `q=1` branch has no deterministic high-band EMA lag. -/
theorem paperSchedule_aggregateMeanLag_q_one
    (p Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    (hκ : 0 < κ) (hκle : κ ≤ 1)
    {d : ℕ}
    (μsrc : Fin (paperSchedule p 1 Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI).J →
      ℕ → Point d) (t : ℕ) :
    let P := paperSchedule p 1 Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
    aggregateMeanLag P μsrc t = 0 := by
  dsimp only
  let P := paperSchedule p 1 Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  apply aggregateMeanLag_of_alpha_one P μsrc
  intro j
  change paperAlpha p 1 κ j.val = 1
  exact paperAlpha_q_one p κ hκ hκle j.val

end

end HeavyTailedNoise.UpperK1
