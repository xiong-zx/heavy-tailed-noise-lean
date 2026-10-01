import HeavyTailedNoise.Upper.K1.KernelSourceMeanHolderBound
import HeavyTailedNoise.Upper.K1.SameSeedMaxResidualLpNorm

/-!
The fixed-endpoint same-seed mixed source drift is expressed in physical
quantities: centered noise scale, two tracker errors, q-WAS displacement,
and the deterministic center displacement.  The outer expectation over an
adaptive runtime path is a separate downstream step.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem paperSchedule_kernel_mix_integral_le_physical
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar)
    (x x' w w' : Point d) :
    let s := paperSexp p q
    let ν := paperNu σ ε
    let U : ℝ := 12 * (2 : ℝ) ^ paperJ p σ ε Ctail
    let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
    let X : Seed → Point d := fun ξ => I.oracle.response x ξ - w
    let Y : Seed → Point d := fun ξ => I.oracle.response x' ξ - w'
    let R : Seed → ℝ := fun ξ => max ‖Y ξ‖ ‖X ξ‖
    let V : Seed → Point d := fun ξ => Y ξ - X ξ
    let D : Seed → ℝ := fun ξ => ‖V ξ‖
    (∫ ξ, 2 * D ξ * (C * (min (R ξ / ν) U) ^ s) ∂I.oracle.law) ≤
      (2 * C / ν ^ s) *
        (((σ + ‖I.objective.grad x' - w'‖) +
            (σ + ‖I.objective.grad x - w‖)) ^ s *
          (Lbar * ‖x' - x‖ + ‖w' - w‖)) := by
  dsimp only
  let s := paperSexp p q
  let ν := paperNu σ ε
  let U : ℝ := 12 * (2 : ℝ) ^ paperJ p σ ε Ctail
  let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
  let X : Seed → Point d := fun ξ => I.oracle.response x ξ - w
  let Y : Seed → Point d := fun ξ => I.oracle.response x' ξ - w'
  let R : Seed → ℝ := fun ξ => max ‖Y ξ‖ ‖X ξ‖
  let V : Seed → Point d := fun ξ => Y ξ - X ξ
  let D : Seed → ℝ := fun ξ => ‖V ξ‖
  let K : ℝ := 2 * C / ν ^ s
  let A : ℝ := (σ + ‖I.objective.grad x' - w'‖) +
    (σ + ‖I.objective.grad x - w‖)
  let B : ℝ := Lbar * ‖x' - x‖ + ‖w' - w‖
  let r : ℝ := q / (q - 1)
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hr : 0 < r := div_pos hqpos (sub_pos.mpr hq)
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos (lt_trans zero_lt_one hp)
    apply sub_pos.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa using hq)
  have hq0 : q ≠ 0 := ne_of_gt hqpos
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq.ne'
  have hsr : r * s = p := by
    dsimp [r, s, paperSexp]
    field_simp [hq0, hq1] <;> ring
  have hexp : ENNReal.ofReal r * ENNReal.ofReal s =
      ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul hr.le, hsr]
  have hν : 0 < ν := paperNu_pos (σ := σ) hε
  have htwo : 1 < (2 : ℝ) ^ s :=
    Real.one_lt_rpow (by norm_num) hs
  have hC : 0 ≤ C := by
    dsimp [C]
    exact (div_pos (Real.rpow_pos_of_pos (by norm_num) s)
      (sub_pos.mpr htwo)).le
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hresponse (a : Point d) : Measurable (I.oracle.response a) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hYm : Measurable Y := (hresponse x').sub measurable_const
  have hXm : Measurable X := (hresponse x).sub measurable_const
  have hRm : Measurable R := hYm.norm.max hXm.norm
  have hR0 (ξ : Seed) : 0 ≤ R ξ :=
    (norm_nonneg (Y ξ)).trans (le_max_left _ _)
  have hRfun : (fun ξ => ‖R ξ‖ ^ s) = (fun ξ => (R ξ) ^ s) := by
    funext ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hR0 ξ)]
  have hRpowMem : MemLp (fun ξ => (R ξ) ^ s)
      (ENNReal.ofReal r) I.oracle.law := by
    simpa only [r, R, X, Y, s] using
      (Admissible.same_seed_max_residual_rpow_memLp I hq x x' w w')
  have hVmem : MemLp V (ENNReal.ofReal q) I.oracle.law := by
    simpa only [V, X, Y] using
      (Admissible.same_seed_residual_increment_memLp I x x' w w')
  have hRpowerLp :
      lpNorm (fun ξ => (R ξ) ^ s) (ENNReal.ofReal r) I.oracle.law =
        (lpNorm R (ENNReal.ofReal p) I.oracle.law) ^ s := by
    have h := eLpNorm_norm_rpow R hRm.aestronglyMeasurable hs
      (p := ENNReal.ofReal r) (μ := I.oracle.law)
    rw [hRfun, hexp] at h
    have hreal := congrArg ENNReal.toReal h
    rw [← ENNReal.toReal_rpow] at hreal
    simpa only [toReal_eLpNorm] using hreal
  have hRroot :
      (∫ ξ, ((R ξ) ^ s) ^ r ∂I.oracle.law) ^ (1 / r) =
        lpNorm (fun ξ => (R ξ) ^ s) (ENNReal.ofReal r)
          I.oracle.law := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hr)
      ENNReal.ofReal_ne_top hRpowMem.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hr.le, one_div]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (hR0 ξ) _)]
  have hVroot :
      (∫ ξ, (D ξ) ^ q ∂I.oracle.law) ^ (1 / q) =
        lpNorm V (ENNReal.ofReal q) I.oracle.law := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hqpos)
      ENNReal.ofReal_ne_top hVmem.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hqpos.le, one_div, D]
  have hbase :
      (∫ ξ, 2 * D ξ * (C * (min (R ξ / ν) U) ^ s)
        ∂I.oracle.law) ≤
        K * ((∫ ξ, ((R ξ) ^ s) ^ r ∂I.oracle.law) ^ (1 / r) *
          (∫ ξ, (D ξ) ^ q ∂I.oracle.law) ^ (1 / q)) := by
    simpa only [K, r, D, V, R, X, Y, C, U, ν, s] using
      (paperSchedule_kernel_mix_integral_le_holder
        p q Δ σ Lbar ε Ctail ch κ Cb CI
        hp hq hε hch hCb hCI I x x' w w')
  have hLpR : lpNorm R (ENNReal.ofReal p) I.oracle.law ≤ A := by
    simpa only [A, R, X, Y] using
      (Admissible.same_seed_max_residual_lpNorm_le I x x' w w')
  have hLpV : lpNorm V (ENNReal.ofReal q) I.oracle.law ≤ B := by
    simpa only [B, V, X, Y] using
      (Admissible.same_seed_residual_increment_lpNorm_le I x x' w w')
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (add_nonneg I.sigma_nonneg (norm_nonneg _))
      (add_nonneg I.sigma_nonneg (norm_nonneg _))
  have hpower :
      (lpNorm R (ENNReal.ofReal p) I.oracle.law) ^ s ≤ A ^ s :=
    Real.rpow_le_rpow lpNorm_nonneg hLpR hs.le
  have hprod :
      (lpNorm R (ENNReal.ofReal p) I.oracle.law) ^ s *
          lpNorm V (ENNReal.ofReal q) I.oracle.law ≤ A ^ s * B := by
    calc
      _ ≤ A ^ s * lpNorm V (ENNReal.ofReal q) I.oracle.law :=
        mul_le_mul_of_nonneg_right hpower lpNorm_nonneg
      _ ≤ A ^ s * B :=
        mul_le_mul_of_nonneg_left hLpV
          (Real.rpow_nonneg hA _)
  calc
    (∫ ξ, 2 * D ξ * (C * (min (R ξ / ν) U) ^ s)
      ∂I.oracle.law) ≤
        K * ((∫ ξ, ((R ξ) ^ s) ^ r ∂I.oracle.law) ^ (1 / r) *
          (∫ ξ, (D ξ) ^ q ∂I.oracle.law) ^ (1 / q)) := hbase
    _ = K * ((lpNorm R (ENNReal.ofReal p) I.oracle.law) ^ s *
        lpNorm V (ENNReal.ofReal q) I.oracle.law) := by
      rw [hRroot, hRpowerLp, hVroot]
    _ ≤ K * (A ^ s * B) :=
      mul_le_mul_of_nonneg_left hprod hK

end

end HeavyTailedNoise.UpperK1
