import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Finite-time `L²` to expected `L¹` conversion on one probability space.
Every time uses the same random source; no temporal independence is assumed.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- A bound on the average second moment controls the expected average
norm, with the exact same constant. The extended-nonnegative conclusion is
usable even when the estimator-error assembly is stated using `lintegral`. -/
theorem finite_average_l2_to_l1
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : ℕ} {V : Type*} [NormedAddCommGroup V]
    (hT : 0 < T)
    (E : Fin T → Ω → V)
    (hE : ∀ t : Fin T, MemLp (E t) 2 μ)
    {a : ℝ} (ha : 0 ≤ a)
    (hsecond :
      (∑ t : Fin T, ∫ ω, ‖E t ω‖ ^ 2 ∂μ) / (T : ℝ) ≤ a ^ 2) :
    (T : ENNReal)⁻¹ *
      (∫⁻ ω, ENNReal.ofReal (∑ t : Fin T, ‖E t ω‖) ∂μ) ≤
      ENNReal.ofReal a := by
  let F : Ω → ℝ := fun ω => ∑ t : Fin T, ‖E t ω‖
  let Q : Ω → ℝ := fun ω => ∑ t : Fin T, ‖E t ω‖ ^ 2
  have hF0 (ω : Ω) : 0 ≤ F ω :=
    Finset.sum_nonneg fun t _ => norm_nonneg (E t ω)
  have hFMem : MemLp F 2 μ := by
    change MemLp (fun ω => ∑ t : Fin T, ‖E t ω‖) 2 μ
    apply memLp_finsetSum Finset.univ
    intro t ht
    exact (hE t).norm
  have hFInt : Integrable F μ := hFMem.integrable (by norm_num)
  have hF2Int : Integrable (fun ω => F ω ^ 2) μ := hFMem.integrable_sq
  have hE2Int (t : Fin T) : Integrable (fun ω => ‖E t ω‖ ^ 2) μ :=
    ((hE t).norm).integrable_sq
  have hQInt : Integrable Q μ := by
    change Integrable (fun ω => ∑ t : Fin T, ‖E t ω‖ ^ 2) μ
    apply integrable_finset_sum
    intro t ht
    exact hE2Int t
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hpoint (ω : Ω) : F ω ^ 2 ≤ (T : ℝ) * Q ω := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin T))
      (fun t => ‖E t ω‖) (fun _ => (1 : ℝ))
    simpa [F, Q, mul_comm] using h
  have hQeq : (∫ ω, Q ω ∂μ) =
      ∑ t : Fin T, ∫ ω, ‖E t ω‖ ^ 2 ∂μ := by
    dsimp [Q]
    exact integral_finsetSum _ (fun t _ => hE2Int t)
  have hF2Bound : (∫ ω, F ω ^ 2 ∂μ) ≤
      (T : ℝ) * (∑ t : Fin T, ∫ ω, ‖E t ω‖ ^ 2 ∂μ) := by
    calc
      (∫ ω, F ω ^ 2 ∂μ) ≤ ∫ ω, (T : ℝ) * Q ω ∂μ :=
        integral_mono hF2Int (hQInt.const_mul _) hpoint
      _ = (T : ℝ) * (∫ ω, Q ω ∂μ) := by rw [integral_const_mul]
      _ = (T : ℝ) *
          (∑ t : Fin T, ∫ ω, ‖E t ω‖ ^ 2 ∂μ) := by rw [hQeq]
  have hMass : (∑ t : Fin T, ∫ ω, ‖E t ω‖ ^ 2 ∂μ) ≤
      (T : ℝ) * a ^ 2 := by
    simpa only [mul_comm] using (div_le_iff₀ hTreal).mp hsecond
  have hF2Target : (∫ ω, F ω ^ 2 ∂μ) ≤
      ((T : ℝ) * a) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hMass hTreal.le
    nlinarith [hF2Bound]
  have hLp : lpNorm F 1 μ ≤ lpNorm F 2 μ := by
    have hENN : eLpNorm F 1 μ ≤ eLpNorm F 2 μ := by
      have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (f := F) (μ := μ)
        (ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 2))
        hFMem.aestronglyMeasurable
      simpa using h
    simpa only [toReal_eLpNorm] using
      (ENNReal.toReal_mono hFMem.eLpNorm_ne_top hENN)
  have hFIntegral0 : 0 ≤ ∫ ω, F ω ∂μ :=
    integral_nonneg hF0
  have hF2Integral0 : 0 ≤ ∫ ω, F ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg (F ω)
  have hLpOne : lpNorm F 1 μ = ∫ ω, F ω ∂μ := by
    rw [lpNorm_one_eq_integral_norm hFMem.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      change ‖F ω‖ = F ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
  have hLpTwo : (lpNorm F 2 μ) ^ 2 = ∫ ω, F ω ^ 2 ∂μ := by
    have hformula : lpNorm F (ENNReal.ofReal (2 : ℝ)) μ =
        (∫ ω, F ω ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ := by
      rw [lpNorm_eq_integral_norm_rpow_toReal
        (by norm_num : ENNReal.ofReal (2 : ℝ) ≠ 0)
        ENNReal.ofReal_ne_top hFMem.aestronglyMeasurable]
      simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change ‖F ω‖ ^ (2 : ℝ) = F ω ^ (2 : ℕ)
        calc
          ‖F ω‖ ^ (2 : ℝ) = F ω ^ (2 : ℝ) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
          _ = F ω ^ (2 : ℕ) := Real.rpow_natCast (F ω) 2
    have hformula' : lpNorm F 2 μ =
        (∫ ω, F ω ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ := by
      simpa only [ENNReal.ofReal_ofNat] using hformula
    rw [hformula', show (2 : ℝ)⁻¹ = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hF2Integral0
  have hLsq : (∫ ω, F ω ∂μ) ^ 2 ≤ ∫ ω, F ω ^ 2 ∂μ := by
    rw [← hLpOne, ← hLpTwo]
    have hleft : 0 ≤ lpNorm F 1 μ := lpNorm_nonneg
    have hright : 0 ≤ lpNorm F 2 μ := lpNorm_nonneg
    nlinarith [hLp, mul_nonneg (sub_nonneg.mpr hLp)
      (add_nonneg hleft hright)]
  have hL : (∫ ω, F ω ∂μ) ≤ (T : ℝ) * a := by
    have hright : 0 ≤ (T : ℝ) * a := mul_nonneg hTreal.le ha
    nlinarith [hLsq, hF2Target]
  have hlintegral :
      (∫⁻ ω, ENNReal.ofReal (F ω) ∂μ) =
        ENNReal.ofReal (∫ ω, F ω ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFInt
      (Filter.Eventually.of_forall hF0)).symm
  have hT0 : (T : ENNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hTtop : (T : ENNReal) ≠ ⊤ := by simp
  change (T : ENNReal)⁻¹ *
    (∫⁻ ω, ENNReal.ofReal (F ω) ∂μ) ≤ ENNReal.ofReal a
  calc
    (T : ENNReal)⁻¹ *
        (∫⁻ ω, ENNReal.ofReal (F ω) ∂μ) =
        (T : ENNReal)⁻¹ *
          ENNReal.ofReal (∫ ω, F ω ∂μ) := by rw [hlintegral]
    _ ≤ (T : ENNReal)⁻¹ *
        ENNReal.ofReal ((T : ℝ) * a) :=
          by simpa only [mul_comm] using
            (mul_le_mul_right (ENNReal.ofReal_le_ofReal hL)
              ((T : ENNReal)⁻¹))
    _ = ENNReal.ofReal a := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg T), ENNReal.ofReal_natCast]
      exact ENNReal.inv_mul_cancel_left hT0 hTtop

end

end HeavyTailedNoise.UpperK1
