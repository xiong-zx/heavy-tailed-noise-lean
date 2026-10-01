import Mathlib.Analysis.MeanInequalitiesPow

/-!
Scalar conversion from the shifted tracker moment with explicit `lam` to a
dimension-free `ν^p` bound.  The algorithmic and oracle facts enter only when
this lemma is instantiated with the paper schedule.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem tracker_p_moment_le_nu_rpow
    {p σ ν τ a lam E : ℝ}
    (hp : 0 < p) (hσ : 0 ≤ σ) (hν : 0 ≤ ν)
    (ha : 0 ≤ a) (hlam : 0 < lam)
    (hσν : σ ≤ ν) (hτ : τ = 12 * ν)
    (haτ : a ≤ 3 * τ)
    (hlamInv : lam⁻¹ ≤ (81 / 32 : ℝ) * τ)
    (hbound : lam ^ p * E ≤
      4 * (lam ^ p * σ ^ p + lam ^ p * a ^ p + 815)) :
    E ≤ 4 * (1 + (36 : ℝ) ^ p +
      815 * (243 / 8 : ℝ) ^ p) * ν ^ p := by
  have hlamP : 0 < lam ^ p := Real.rpow_pos_of_pos hlam p
  have hE : E ≤ 4 * (σ ^ p + a ^ p + 815 * (lam ^ p)⁻¹) := by
    have hscaled := mul_le_mul_of_nonneg_left hbound
      (inv_nonneg.mpr hlamP.le)
    calc
      E = (lam ^ p)⁻¹ * (lam ^ p * E) := by
        field_simp [ne_of_gt hlamP]
      _ ≤ (lam ^ p)⁻¹ *
          (4 * (lam ^ p * σ ^ p + lam ^ p * a ^ p + 815)) := hscaled
      _ = 4 * (σ ^ p + a ^ p + 815 * (lam ^ p)⁻¹) := by
        field_simp [ne_of_gt hlamP]
  have hσpow : σ ^ p ≤ ν ^ p :=
    Real.rpow_le_rpow hσ hσν hp.le
  have haν : a ≤ 36 * ν := by
    rw [hτ] at haτ
    nlinarith
  have hapow : a ^ p ≤ (36 * ν) ^ p :=
    Real.rpow_le_rpow ha haν hp.le
  have hInvν : lam⁻¹ ≤ (243 / 8 : ℝ) * ν := by
    rw [hτ] at hlamInv
    nlinarith
  have hInvPow : (lam ^ p)⁻¹ ≤ ((243 / 8 : ℝ) * ν) ^ p := by
    rw [← Real.inv_rpow hlam.le]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hlam.le) hInvν hp.le
  have hsum :
      σ ^ p + a ^ p + 815 * (lam ^ p)⁻¹ ≤
        ν ^ p + (36 * ν) ^ p +
          815 * ((243 / 8 : ℝ) * ν) ^ p := by
    have h815 := mul_le_mul_of_nonneg_left hInvPow (by norm_num : (0 : ℝ) ≤ 815)
    linarith
  calc
    E ≤ 4 * (σ ^ p + a ^ p + 815 * (lam ^ p)⁻¹) := hE
    _ ≤ 4 * (ν ^ p + (36 * ν) ^ p +
          815 * ((243 / 8 : ℝ) * ν) ^ p) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 4 * (1 + (36 : ℝ) ^ p +
          815 * (243 / 8 : ℝ) ^ p) * ν ^ p := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 36) hν,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 243 / 8) hν]
      ring

end

end HeavyTailedNoise.UpperK1
