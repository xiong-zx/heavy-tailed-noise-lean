import HeavyTailedNoise.Upper.K1.PhysicalParameters

/-!
Compare the frozen shared-batch upper rate shape with the complete
randomized lower rate shape. This file is scalar arithmetic only: the lower
minimax theorem and the upper algorithm keep their own proof obligations.
The comparison includes zero noise and every finite `q ≥ 1`.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

/-- The two max expressions differ by at most a factor of two whenever the
dimensionless optimization budget is at least one. Here `B` and `C` may be
any nonnegative scalars; their power relation is used only during the
physical substitution below. -/
private theorem abstract_rate_shapes_within_two
    {A B C D : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 1 ≤ D) :
    let lower := max (A + B + A * C) (A * D)
    let upper := max 1 B + A * max D (max 1 C)
    upper ≤ 2 * lower ∧ lower ≤ 2 * upper := by
  dsimp only
  let X : ℝ := A + B + A * C
  let lower : ℝ := max X (A * D)
  let M : ℝ := max D (max 1 C)
  let upper : ℝ := max 1 B + A * M
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1) hA
  have hAC0 : 0 ≤ A * C := mul_nonneg hA0 hC
  have hXlower : X ≤ lower := le_max_left _ _
  have hADlower : A * D ≤ lower := le_max_right _ _
  have hAlower : A ≤ lower := by dsimp [X] at hXlower; linarith
  have hBlower : B ≤ lower := by dsimp [X] at hXlower; linarith
  have hmaxBlower : max 1 B ≤ lower :=
    max_le (le_trans hA hAlower) hBlower
  have hAmaxClower : A * max 1 C ≤ lower := by
    rcases le_total C 1 with hC1 | h1C
    · rw [max_eq_left hC1]
      simpa only [mul_one] using hAlower
    · rw [max_eq_right h1C]
      dsimp [X] at hXlower
      linarith
  have hAMlower : A * M ≤ lower := by
    calc
      A * M = max (A * D) (A * max 1 C) :=
        mul_max_of_nonneg D (max 1 C) hA0
      _ ≤ lower := max_le hADlower hAmaxClower
  have hupperLower : upper ≤ 2 * lower := by
    dsimp [upper]
    linarith
  have hM1 : 1 ≤ M := hD.trans (le_max_left _ _)
  have hMc : C ≤ M :=
    (le_max_right 1 C).trans (le_max_right D (max 1 C))
  have hMD : D ≤ M := le_max_left _ _
  have hAleAM : A ≤ A * M := by
    have h := mul_le_mul_of_nonneg_left hM1 hA0
    simpa only [mul_one] using h
  have hACleAM : A * C ≤ A * M :=
    mul_le_mul_of_nonneg_left hMc hA0
  have hADleAM : A * D ≤ A * M :=
    mul_le_mul_of_nonneg_left hMD hA0
  have hBmax : B ≤ max 1 B := le_max_right _ _
  have hmaxB0 : 0 ≤ max 1 B :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hXupper : X ≤ 2 * upper := by
    dsimp [X, upper]
    linarith
  have hADupper : A * D ≤ 2 * upper := by
    dsimp [upper]
    linarith
  have hlowerUpper : lower ≤ 2 * upper :=
    max_le hXupper hADupper
  exact ⟨hupperLower, hlowerUpper⟩

private theorem physical_rate_shapes_within_two
    (p q Lbar Δ σ ε : ℝ) (hp : 1 < p) (hq : 1 ≤ q)
    (hσ : 0 ≤ σ) (hε : 0 < ε)
    (hA : 1 ≤ Lbar * Δ / ε ^ 2) :
    let A := Lbar * Δ / ε ^ 2
    let t := σ / ε
    let r := p / (p - 1)
    let B := t ^ r
    let S := paperS σ ε
    let lower := max (A + B + A * B ^ (1 / q)) (A * S ^ 2)
    let upper := S ^ r + A * max (S ^ 2) (S ^ (r / q))
    upper ≤ 2 * lower ∧ lower ≤ 2 * upper := by
  dsimp only
  let A : ℝ := Lbar * Δ / ε ^ 2
  let t : ℝ := σ / ε
  let r : ℝ := p / (p - 1)
  let B : ℝ := t ^ r
  let S : ℝ := paperS σ ε
  let C : ℝ := B ^ (1 / q)
  let D : ℝ := S ^ 2
  have ht : 0 ≤ t := div_nonneg hσ hε.le
  have hr : 0 < r := div_pos (by linarith : 0 < p) (sub_pos.mpr hp)
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hB : 0 ≤ B := Real.rpow_nonneg ht _
  have hC : 0 ≤ C := Real.rpow_nonneg hB _
  have hD : 1 ≤ D := by
    dsimp [D]
    simpa only [one_pow, S] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (one_le_paperS σ ε) 2)
  have hSrate : S ^ r = max 1 B := by
    change (max 1 t) ^ r = max 1 (t ^ r)
    rw [Real.rpow_max (by norm_num : (0 : ℝ) ≤ 1) ht hr.le]
    simp
  have hpower : t ^ (r / q) = C := by
    have he : r / q = r * (1 / q) := by ring
    rw [he, Real.rpow_mul ht]
  have hCscale : S ^ (r / q) = max 1 C := by
    change (max 1 t) ^ (r / q) = max 1 C
    rw [Real.rpow_max (by norm_num : (0 : ℝ) ≤ 1) ht
      (div_nonneg hr.le hq0.le)]
    rw [Real.one_rpow, hpower]
  have hscalar := abstract_rate_shapes_within_two hA hB hC hD
  change max 1 B + A * max D (max 1 C) ≤
      2 * max (A + B + A * C) (A * D) ∧
    max (A + B + A * C) (A * D) ≤
      2 * (max 1 B + A * max D (max 1 C)) at hscalar
  change S ^ r + A * max D (S ^ (r / q)) ≤
      2 * max (A + B + A * C) (A * D) ∧
    max (A + B + A * C) (A * D) ≤
      2 * (S ^ r + A * max D (S ^ (r / q)))
  rw [hSrate, hCscale]
  exact hscalar

/-- The exact shared-batch upper rate shape is at most twice the complete
randomized lower max shape in the lower theorem's accuracy regime. -/
theorem paper_upper_shape_le_two_full_lower_shape
    (p q Lbar Δ σ ε : ℝ) (hp : 1 < p) (hq : 1 ≤ q)
    (hσ : 0 ≤ σ) (hε : 0 < ε)
    (hA : 1 ≤ Lbar * Δ / ε ^ 2) :
    (paperS σ ε) ^ (p / (p - 1)) +
      paperAplus Lbar Δ ε *
        max ((paperS σ ε) ^ 2)
          ((paperS σ ε) ^ ((p / (p - 1)) / q)) ≤
      2 * max
        ((Lbar * Δ / ε ^ 2) + (σ / ε) ^ (p / (p - 1)) +
          (Lbar * Δ / ε ^ 2) *
            ((σ / ε) ^ (p / (p - 1))) ^ (1 / q))
        ((Lbar * Δ / ε ^ 2) * (paperS σ ε) ^ 2) := by
  have hplus : paperAplus Lbar Δ ε = Lbar * Δ / ε ^ 2 := by
    unfold paperAplus
    exact max_eq_right hA
  rw [hplus]
  exact (physical_rate_shapes_within_two p q Lbar Δ σ ε
    hp hq hσ hε hA).1

/-- Conversely, the complete randomized lower max shape is at most twice
the exact shared-batch upper rate shape. -/
theorem full_lower_shape_le_two_paper_upper_shape
    (p q Lbar Δ σ ε : ℝ) (hp : 1 < p) (hq : 1 ≤ q)
    (hσ : 0 ≤ σ) (hε : 0 < ε)
    (hA : 1 ≤ Lbar * Δ / ε ^ 2) :
    max
        ((Lbar * Δ / ε ^ 2) + (σ / ε) ^ (p / (p - 1)) +
          (Lbar * Δ / ε ^ 2) *
            ((σ / ε) ^ (p / (p - 1))) ^ (1 / q))
        ((Lbar * Δ / ε ^ 2) * (paperS σ ε) ^ 2) ≤
      2 * ((paperS σ ε) ^ (p / (p - 1)) +
        paperAplus Lbar Δ ε *
          max ((paperS σ ε) ^ 2)
            ((paperS σ ε) ^ ((p / (p - 1)) / q))) := by
  have hplus : paperAplus Lbar Δ ε = Lbar * Δ / ε ^ 2 := by
    unfold paperAplus
    exact max_eq_right hA
  rw [hplus]
  exact (physical_rate_shapes_within_two p q Lbar Δ σ ε
    hp hq hσ hε hA).2

end

end HeavyTailedNoise.UpperK1
