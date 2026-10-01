import HeavyTailedNoise.Upper.K1.KernelPhysicalBandWeight

/-!
The remaining per-band weight estimate for the literal manuscript schedule.
It turns the inverse EMA rate and the conservative shell norm into a dyadic
power with exponent `1 - s/2`. This removes the weight premise of the
conditional high-band kernel bridge without introducing any probability
assumption.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem paperSchedule_sqrtAlpha_mul_highBand_norm_le
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} (z : Point d) (j : Fin (paperJ p σ ε Ctail)) :
    Real.sqrt ((paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI).alpha j) *
        ‖highBand (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
          hε hch hCb hCI) j z‖ ≤
      (3 * paperNu σ ε / Real.sqrt κ) *
        (12 * (2 : ℝ) ^ (j : ℕ)) ^ (1 - paperSexp p q / 2) := by
  let ν : ℝ := paperNu σ ε
  let t : ℝ := 12 * (2 : ℝ) ^ (j : ℕ)
  let s : ℝ := paperSexp p q
  let a : ℝ := 1 - s / 2
  let α : ℝ := paperAlpha p q κ j.val
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  have hν : 0 < ν := paperNu_pos hε
  have ht : 0 < t := by dsimp [t]; positivity
  have hα : 0 < α := paperAlpha_pos hκ j.val
  have hαinv : α ≤ (κ * t ^ s)⁻¹ := by
    simpa only [α, t, s] using paperAlpha_le_inverse_branch p q κ j.val
  have hβ : 0 < κ * t ^ s :=
    mul_pos hκ (Real.rpow_pos_of_pos ht _)
  have hd : ‖highBand P j z‖ ≤ 3 * ν * t := by
    simpa only [P, ν, t] using
      paperSchedule_highBand_norm_le_three_nu_dyadic
        p q Δ σ Lbar ε Ctail ch κ Cb CI hε hch hCb hCI z j
  have hdSq : ‖highBand P j z‖ ^ 2 ≤ (3 * ν * t) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hd
  have hLsq : (Real.sqrt α * ‖highBand P j z‖) ^ 2 ≤
      (κ * t ^ s)⁻¹ * (3 * ν * t) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hα.le]
    calc
      α * ‖highBand P j z‖ ^ 2 ≤ α * (3 * ν * t) ^ 2 :=
        mul_le_mul_of_nonneg_left hdSq hα.le
      _ ≤ (κ * t ^ s)⁻¹ * (3 * ν * t) ^ 2 :=
        mul_le_mul_of_nonneg_right hαinv (sq_nonneg _)
  have hta : (t ^ a) ^ 2 = t ^ 2 / t ^ s := by
    have hexp : a * (2 : ℝ) = 2 - s := by dsimp [a]; ring
    have hta1 : (t ^ a) ^ 2 = t ^ (a * (2 : ℝ)) := by
      simpa using (Real.rpow_mul_natCast ht.le a 2).symm
    have hta2 : t ^ (a * (2 : ℝ)) = t ^ (2 - s) :=
      congrArg (fun r : ℝ => t ^ r) hexp
    have hta3 : t ^ (2 - s) = t ^ 2 / t ^ s := by
      simpa using (Real.rpow_sub ht 2 s)
    exact hta1.trans (hta2.trans hta3)
  have hκsqrt : (Real.sqrt κ) ^ 2 = κ := Real.sq_sqrt hκ.le
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have htspow_ne : t ^ s ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  have hκsqrt_ne : Real.sqrt κ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hκ)
  have hRsq : ((3 * ν / Real.sqrt κ) * t ^ a) ^ 2 =
      (κ * t ^ s)⁻¹ * (3 * ν * t) ^ 2 := by
    rw [mul_pow, div_pow, hκsqrt, hta]
    field_simp [hκne, htspow_ne, hκsqrt_ne] <;> ring
  have hLnonneg : 0 ≤ Real.sqrt α * ‖highBand P j z‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hRnonneg : 0 ≤ (3 * ν / Real.sqrt κ) * t ^ a := by
    positivity
  have hsqtarget : (Real.sqrt α * ‖highBand P j z‖) ^ 2 ≤
      ((3 * ν / Real.sqrt κ) * t ^ a) ^ 2 := by
    rw [hRsq]
    exact hLsq
  have hbound := (sq_le_sq₀ hLnonneg hRnonneg).mp hsqtarget
  change Real.sqrt α * ‖highBand P j z‖ ≤ (3 * ν / Real.sqrt κ) * t ^ a
  exact hbound

end

end HeavyTailedNoise.UpperK1
