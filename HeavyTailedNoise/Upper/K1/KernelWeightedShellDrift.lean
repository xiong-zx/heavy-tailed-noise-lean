import HeavyTailedNoise.Upper.K1.KernelBandDriftSupport
import HeavyTailedNoise.Upper.K1.KernelActiveDyadic

/-!
Conservative q-WAS mean-drift geometry for the manuscript's dyadic high
bands. At q>1, only scales active for at least one of two residuals contribute.
The factor two uses the proved Lipschitz bound for a difference of radial
clips. The q=1 branch has no EMA lag and does not use this exponent.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- Same-seed weighted high-band increments obey an active-dyadic, no-log
bound, including zero residuals, no high bands, and threshold equality. -/
theorem paperSchedule_weighted_highBand_sub_sum_le
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} (u v : Point d) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    let ν := paperNu σ ε
    let s := paperSexp p q
    let R := max ‖u‖ ‖v‖
    (∑ j : Fin P.J,
      (12 * (2 : ℝ) ^ j.val) ^ s * ‖highBand P j u - highBand P j v‖) ≤
      2 * ‖u - v‖ *
        (((2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)) *
          (min (R / ν) (12 * (2 : ℝ) ^ P.J)) ^ s) := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  let ν := paperNu σ ε
  let s := paperSexp p q
  let R := max ‖u‖ ‖v‖
  have hν : 0 < ν := paperNu_pos (σ := σ) hε
  have hR : 0 ≤ R := le_trans (norm_nonneg u) (le_max_left _ _)
  have hRν : 0 ≤ R / ν := div_nonneg hR hν.le
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos (lt_trans zero_lt_one hp)
    apply sub_pos.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa using hq)
  have hterm (j : Fin P.J) :
      (12 * (2 : ℝ) ^ j.val) ^ s *
          ‖highBand P j u - highBand P j v‖ ≤
        2 * ‖u - v‖ *
          (if 12 * (2 : ℝ) ^ j.val < R / ν then
            (12 * (2 : ℝ) ^ j.val) ^ s else 0) := by
    have hw : 0 ≤ (12 * (2 : ℝ) ^ j.val) ^ s :=
      Real.rpow_nonneg (by positivity) _
    by_cases ha : 12 * (2 : ℝ) ^ j.val < R / ν
    · calc
        (12 * (2 : ℝ) ^ j.val) ^ s *
            ‖highBand P j u - highBand P j v‖ ≤
          (12 * (2 : ℝ) ^ j.val) ^ s *
            (2 * ‖u - v‖) :=
          mul_le_mul_of_nonneg_left (highBand_norm_sub_le_two P j u v) hw
        _ = 2 * ‖u - v‖ *
            (12 * (2 : ℝ) ^ j.val) ^ s := by ring
        _ = 2 * ‖u - v‖ *
            (if 12 * (2 : ℝ) ^ j.val < R / ν then
              (12 * (2 : ℝ) ^ j.val) ^ s else 0) := by simp [ha]
    · have hRle : R / ν ≤ 12 * (2 : ℝ) ^ j.val := le_of_not_gt ha
      have hRτ : R ≤ paperTau σ ε j.val := by
        calc
          R ≤ (12 * (2 : ℝ) ^ j.val) * ν :=
            (div_le_iff₀ hν).mp hRle
          _ = paperTau σ ε j.val := by
            dsimp [ν, paperTau]
            ring
      have hzero : highBand P j u - highBand P j v = 0 := by
        exact paperSchedule_highBand_sub_zero_of_max_norm_le
          p q Δ σ Lbar ε Ctail ch κ Cb CI
          hε hch hCb hCI j u v hRτ
      simp [ha, hzero]
  have hactive :
      (∑ j : Fin P.J,
        if 12 * (2 : ℝ) ^ j.val < R / ν then
          (12 * (2 : ℝ) ^ j.val) ^ s else 0) =
      ∑ j ∈ activeDyadic P.J (R / ν),
        (12 * (2 : ℝ) ^ j) ^ s := by
    let F : ℕ → ℝ := fun j =>
      if 12 * (2 : ℝ) ^ j < R / ν then
        (12 * (2 : ℝ) ^ j) ^ s else 0
    change (∑ j : Fin P.J, F j.val) = _
    rw [Fin.sum_univ_eq_sum_range F]
    simp [F, activeDyadic, Finset.sum_filter]
  calc
    (∑ j : Fin P.J,
      (12 * (2 : ℝ) ^ j.val) ^ s *
        ‖highBand P j u - highBand P j v‖) ≤
      ∑ j : Fin P.J,
        2 * ‖u - v‖ *
          (if 12 * (2 : ℝ) ^ j.val < R / ν then
            (12 * (2 : ℝ) ^ j.val) ^ s else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hterm j
    _ = 2 * ‖u - v‖ *
        (∑ j : Fin P.J,
          if 12 * (2 : ℝ) ^ j.val < R / ν then
            (12 * (2 : ℝ) ^ j.val) ^ s else 0) := by
      rw [Finset.mul_sum]
    _ = 2 * ‖u - v‖ *
        (∑ j ∈ activeDyadic P.J (R / ν),
          (12 * (2 : ℝ) ^ j) ^ s) := by rw [hactive]
    _ ≤ 2 * ‖u - v‖ *
        (((2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)) *
          (min (R / ν) (12 * (2 : ℝ) ^ P.J)) ^ s) :=
      mul_le_mul_of_nonneg_left (activeDyadic_sum_le_min P.J hRν hs)
        (mul_nonneg (by norm_num) (norm_nonneg _))

end

end HeavyTailedNoise.UpperK1
