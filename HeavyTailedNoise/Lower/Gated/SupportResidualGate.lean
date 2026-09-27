import HeavyTailedNoise.Lower.Gated.SupportInstantiation
import HeavyTailedNoise.Analysis.FrameCoordinates

/-!
The actual residual gate in frozen Sections 2.3 and 3. Indices are zero-based,
so the prefix `i ≤ k` here is the manuscript's first `k+1` frame vectors.
`gatedResidual` is the sole definition of σ. Its explicit finite-frame
projector is proved equal to orthogonal projection onto the prefix complement.
No quantitative gradient or Hessian bound is asserted in this module.
-/

namespace HeavyTailedNoise

open Set Filter
open scoped BigOperators Topology

noncomputable section

def carmonOmegaSix : ℝ → ℝ := stepWindow (1 / 16) (1 / 16)

theorem carmonOmegaSix_nonneg (z : ℝ) : 0 ≤ carmonOmegaSix z := smoothstep_nonneg _

theorem carmonOmegaSix_le_one (z : ℝ) : carmonOmegaSix z ≤ 1 := smoothstep_le_one _

theorem carmonOmegaSix_zero {z : ℝ} (hz : |z| ≤ 1 / 16) : carmonOmegaSix z = 0 :=
  stepWindow_zero_of_abs_le (by norm_num) hz

theorem carmonOmegaSix_one {z : ℝ} (hz : 1 / 8 ≤ |z|) : carmonOmegaSix z = 1 :=
  stepWindow_one_of_abs_ge (by norm_num) (by linarith)

theorem contDiff_carmonOmegaSix_two : ContDiff ℝ 2 carmonOmegaSix :=
  contDiff_stepWindow_two (by norm_num) (by norm_num)

/-- Coordinates `Uᵀ y` for a finite real frame. -/
def gatedResidual {d T : ℕ} (U : Fin T → Point d) (k : Fin T) (y : Point d) : ℝ :=
  ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ k)) y‖ ^ 2 -
    ∑ i ∈ Finset.univ.filter (k < ·),
      carmonOmegaSix (frameCoordinates U y i) * (frameCoordinates U y i) ^ 2

theorem gatedResidual_eq_projection {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) :
    gatedResidual U k y =
      ‖((selectedFrameSpan U (Finset.univ.filter (· ≤ k)))ᗮ).starProjection y‖ ^ 2 -
        ∑ i ∈ Finset.univ.filter (k < ·),
          carmonOmegaSix (frameCoordinates U y i) * (frameCoordinates U y i) ^ 2 := by
  unfold gatedResidual
  rw [frameOrthogonalResidual_eq_starProjection hU]

/-- Bessel's inequality controls the complete coordinate mass. The tail weights
are at most one, so subtracting their mass cannot exhaust the prefix residual. -/
theorem gatedResidual_nonneg {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) (y : Point d) : 0 ≤ gatedResidual U k y := by
  have hB : (∑ i : Fin T, (frameCoordinates U y i) ^ 2) ≤ ‖y‖ ^ 2 := by
    simpa [frameCoordinates, Real.norm_eq_abs, sq_abs] using
      (hU.sum_inner_products_le (s := Finset.univ) y)
  have hpart :
      (∑ i ∈ Finset.univ.filter (· ≤ k), (frameCoordinates U y i) ^ 2) +
      (∑ i ∈ Finset.univ.filter (k < ·), (frameCoordinates U y i) ^ 2) =
        ∑ i : Fin T, (frameCoordinates U y i) ^ 2 := by
    simpa only [not_le] using Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun i : Fin T => i ≤ k) (fun i => (frameCoordinates U y i) ^ 2)
  have hw :
      (∑ i ∈ Finset.univ.filter (k < ·),
        carmonOmegaSix (frameCoordinates U y i) * (frameCoordinates U y i) ^ 2) ≤
      ∑ i ∈ Finset.univ.filter (k < ·), (frameCoordinates U y i) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    simpa using mul_le_mul_of_nonneg_right (carmonOmegaSix_le_one (frameCoordinates U y i))
      (sq_nonneg (frameCoordinates U y i))
  unfold gatedResidual
  rw [frameOrthogonalResidual_norm_sq hU]
  linarith

theorem contDiff_gatedResidual_two {d T : ℕ} (U : Fin T → Point d) (k : Fin T) :
    ContDiff ℝ 2 (gatedResidual U k) := by
  unfold gatedResidual
  apply ((contDiff_frameOrthogonalResidual_two U
    (Finset.univ.filter (· ≤ k))).norm_sq ℝ).sub
  apply ContDiff.sum
  intro i hi
  have hc := (contDiff_pi.mp (contDiff_frameCoordinates_two U)) i
  exact (contDiff_carmonOmegaSix_two.comp hc).mul (hc.pow 2)

/-- Exact residual cutoff, with `a₁ = 1/16` and `W = 1000`. -/
def carmonChi (s : ℝ) : ℝ := 1 - smoothstep ((s - 1 / 16) / 1000)

theorem carmonChi_nonneg (s : ℝ) : 0 ≤ carmonChi s :=
  sub_nonneg.mpr (smoothstep_le_one _)

theorem carmonChi_le_one (s : ℝ) : carmonChi s ≤ 1 := by
  unfold carmonChi
  linarith [smoothstep_nonneg ((s - 1 / 16) / 1000)]

theorem contDiff_carmonChi_two : ContDiff ℝ 2 carmonChi := by
  have hh := contDiff_smoothstep_two
  unfold carmonChi
  fun_prop

theorem actual_chainGateTerm_nonneg {T : ℕ} (z : Fin T → ℝ) (k : Fin T) :
    0 ≤ chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z k := by
  by_cases hz : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z k = 0
  · simp [hz]
  obtain ⟨hprev, hcurrent, hlater⟩ := chainGateTerm_support
    (fun _ ht => carmonPsi_zero_of_le ht) (fun _ ht => carmonOmega_one ht)
    (fun _ ht => carmonOmegaThree_one ht) hz
  have hq : 0 < chainCorrection carmonPsi carmonPhi carmonOmega 1 z k :=
    frontierCorrection_pos (fun _ ht => carmonPsi_zero_of_le ht)
      (fun _ ht => carmonPsi_pos_of_gt ht) (fun _ ht => carmonOmega_lt_one ht)
      (fun _ ht => carmonPhi_correction_brackets_pos ht) hprev hcurrent
  have hsel : 0 < chainSelector carmonOmegaThree z k := by
    apply Finset.prod_pos
    intro i hi
    exact sub_pos.mpr (carmonOmegaThree_lt_one (hlater i (Finset.mem_filter.mp hi).2))
  exact (mul_pos hq hsel).le

/-- The full finite correction sum Q, using the one authoritative residual. -/
def gatedCorrection {d T : ℕ} (U : Fin T → Point d) (y : Point d) : ℝ :=
  ∑ k : Fin T, (1 - carmonChi (gatedResidual U k y)) *
    chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 (frameCoordinates U y) k

theorem gatedCorrection_nonneg {d T : ℕ} (U : Fin T → Point d) (y : Point d) :
    0 ≤ gatedCorrection U y := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (sub_nonneg.mpr (carmonChi_le_one _))
    (actual_chainGateTerm_nonneg _ _)

theorem contDiff_gatedCorrection_two {d T : ℕ} (U : Fin T → Point d) :
    ContDiff ℝ 2 (gatedCorrection U) := by
  apply ContDiff.sum
  intro k hk
  exact (contDiff_const.sub (contDiff_carmonChi_two.comp (contDiff_gatedResidual_two U k))).mul
    ((contDiff_actual_chainGateTerm_two k).comp (contDiff_frameCoordinates_two U))

end

end HeavyTailedNoise
