import HeavyTailedNoise.Upper.K1.ResidualPhysicalMoment
import HeavyTailedNoise.Upper.K1.RuntimeNoisePhysicalCoefficient
import HeavyTailedNoise.Upper.K1.MeanDriftScale

/-!
Explicit admissible constants for the manuscript's existing schedule.
The four analytical errors receive separate `ε / 32` budgets. The choices
depend only on the moment and smoothness exponents, never on dimension,
accuracy or physical oracle parameters.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

def upperCtail (p : ℝ) : ℝ :=
  (128 * (1 + physicalResidualTrackerConstant p)) ^ (1 / (p - 1))

def upperKappa (p q : ℝ) : ℝ :=
  (32 * max 1 (paperMeanDriftConstant p q))⁻¹

def upperCb (p q : ℝ) : ℝ :=
  2048 * (1 + physicalResidualTrackerConstant p) *
    max 1 (physicalKernelNoiseConstant p q (upperKappa p q))

def upperCI : ℝ := 4096

theorem physicalResidualTrackerConstant_nonneg (p : ℝ) :
    0 ≤ physicalResidualTrackerConstant p := by
  unfold physicalResidualTrackerConstant
  have h36 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 36) p
  have h243 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 243 / 8) p
  nlinarith

theorem upperCtail_pos (p : ℝ) : 0 < upperCtail p := by
  unfold upperCtail
  apply Real.rpow_pos_of_pos
  have := physicalResidualTrackerConstant_nonneg p
  positivity

theorem upperCtail_pow (p : ℝ) (hp : 1 < p) :
    (upperCtail p) ^ (p - 1) =
      128 * (1 + physicalResidualTrackerConstant p) := by
  have hbase : 0 ≤ 128 * (1 + physicalResidualTrackerConstant p) := by
    have := physicalResidualTrackerConstant_nonneg p
    positivity
  have hpm : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  unfold upperCtail
  rw [← Real.rpow_mul hbase]
  have hcancel : 1 / (p - 1) * (p - 1) = 1 := by field_simp [hpm]
  rw [hcancel, Real.rpow_one]

theorem upperCtail_ge_twelve (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    12 ≤ upperCtail p := by
  have hC := physicalResidualTrackerConstant_nonneg p
  have hbase : 1 ≤ 128 * (1 + physicalResidualTrackerConstant p) := by
    nlinarith
  have hexp : 1 ≤ 1 / (p - 1) :=
    (le_div_iff₀ (sub_pos.mpr hp)).2 (by linarith)
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase hexp
  rw [Real.rpow_one] at hpow
  exact (by nlinarith : 12 ≤ 128 * (1 + physicalResidualTrackerConstant p)).trans hpow

theorem upperKappa_pos (p q : ℝ) : 0 < upperKappa p q := by
  unfold upperKappa
  have hm : 0 < max 1 (paperMeanDriftConstant p q) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

theorem upperKappa_le_one (p q : ℝ) : upperKappa p q ≤ 1 := by
  have hm : 1 ≤ max 1 (paperMeanDriftConstant p q) := le_max_left _ _
  unfold upperKappa
  apply (inv_le_one₀ (by positivity)).2
  nlinarith

theorem upperKappa_drift_le (p q : ℝ) :
    paperMeanDriftConstant p q * upperKappa p q ≤ 1 / 32 := by
  let M := max 1 (paperMeanDriftConstant p q)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hD : paperMeanDriftConstant p q ≤ M := le_max_right _ _
  change paperMeanDriftConstant p q * (32 * M)⁻¹ ≤ 1 / 32
  calc
    _ ≤ M * (32 * M)⁻¹ :=
      mul_le_mul_of_nonneg_right hD (by positivity)
    _ = 1 / 32 := by field_simp [hM.ne']

theorem upperCb_pos (p q : ℝ) : 0 < upperCb p q := by
  unfold upperCb
  have hC := physicalResidualTrackerConstant_nonneg p
  have hK : 0 < max 1 (physicalKernelNoiseConstant p q (upperKappa p q)) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

theorem upperCI_pos : 0 < upperCI := by norm_num [upperCI]

theorem upper_bias_coefficient (p : ℝ) (hp : 1 < p) :
    4 * (1 + physicalResidualTrackerConstant p) /
      (upperCtail p) ^ (p - 1) = 1 / 32 := by
  rw [upperCtail_pow p hp]
  have hC : 1 + physicalResidualTrackerConstant p ≠ 0 := by
    have := physicalResidualTrackerConstant_nonneg p
    positivity
  field_simp [hC]
  <;> ring

theorem upper_runtime_variance_coefficient_le (p q : ℝ) :
    2 * (1 + physicalResidualTrackerConstant p) *
        physicalKernelNoiseConstant p q (upperKappa p q) / upperCb p q ≤
      (1 / 32 : ℝ) ^ 2 := by
  let C := 1 + physicalResidualTrackerConstant p
  let K := physicalKernelNoiseConstant p q (upperKappa p q)
  let M := max 1 K
  have hC : 0 < C := by
    dsimp [C]
    have := physicalResidualTrackerConstant_nonneg p
    positivity
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKM : K ≤ M := le_max_right _ _
  change 2 * C * K / (2048 * C * M) ≤ (1 / 32 : ℝ) ^ 2
  apply (div_le_iff₀ (by positivity : 0 < 2048 * C * M)).2
  have h := mul_le_mul_of_nonneg_left hKM (by positivity : 0 ≤ 2 * C)
  nlinarith [h]

theorem upper_initial_variance_coefficient :
    4 / upperCI = (1 / 32 : ℝ) ^ 2 := by norm_num [upperCI]

end

end HeavyTailedNoise.UpperK1
