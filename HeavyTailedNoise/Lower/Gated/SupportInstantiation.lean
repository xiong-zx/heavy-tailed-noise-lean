import HeavyTailedNoise.Lower.Gated.GateSupport
import HeavyTailedNoise.Analysis.CarmonPhi
import HeavyTailedNoise.Analysis.CarmonScalar
import HeavyTailedNoise.Analysis.GateAlgebra

/-!
Concrete scalar certificates and finite-chain support for the frozen gated
construction. The exact windows reuse `stepWindow`, and every scalar premise
of the conditional `GateSupport` lemmas is discharged here.
-/

namespace HeavyTailedNoise

open Filter Set
open scoped Topology

noncomputable section

theorem ZeroTwoJet.of_contDiff_scalar {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiff ℝ 2 f) (hv : f x = 0)
    (hfirst : deriv f x = 0) (hsecond : deriv (deriv f) x = 0) :
    ZeroTwoJet f x := by
  apply ZeroTwoJet.of_hasDerivAt hv
  · rw [← hfirst]
    exact (hf.differentiable (by norm_num) x).hasDerivAt
  · rw [← hsecond]
    exact (hf.differentiable_deriv_two x).hasDerivAt

theorem ZeroTwoJet.congr_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ZeroTwoJet f x) (h : g =ᶠ[𝓝 x] f) :
    ZeroTwoJet g x := by
  refine ⟨h.self_of_nhds.trans hf.value, hf.first.congr_of_eventuallyEq h, ?_⟩
  have hd : fderiv ℝ g =ᶠ[𝓝 x] fderiv ℝ f := h.fderiv
  exact hf.second.congr_of_eventuallyEq hd

theorem smoothstep_complement_zeroTwoJet {t : ℝ} (ht : 1 ≤ t) :
    ZeroTwoJet (fun u => 1 - smoothstep u) t := by
  have ht0 : ¬t ≤ 0 := by linarith
  apply ZeroTwoJet.of_contDiff_scalar (contDiff_const.sub contDiff_smoothstep_two)
  · simp [smoothstep_one_of_one_le ht]
  · rw [deriv_const_sub, deriv_smoothstep_formula]
    simp [ht0, ht]
  · rw [deriv_const_sub', deriv.fun_neg, second_deriv_smoothstep_formula]
    simp [ht0, ht]

theorem stepWindow_zero_of_abs_le {a w z : ℝ} (hw : 0 < w) (hz : |z| ≤ a) :
    stepWindow a w z = 0 := by
  apply smoothstep_zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) hw.le

theorem stepWindow_one_of_abs_ge {a w z : ℝ} (hw : 0 < w) (hz : a + w ≤ |z|) :
    stepWindow a w z = 1 := by
  apply smoothstep_one_of_one_le
  apply (le_div_iff₀ hw).mpr
  linarith

theorem stepWindow_lt_one_of_abs_lt {a w z : ℝ} (hw : 0 < w) (hz : |z| < a + w) :
    stepWindow a w z < 1 := by
  apply smoothstep_lt_one_of_lt
  apply (div_lt_iff₀ hw).mpr
  linarith

/-- The nonsmooth point of absolute value lies inside the constant-zero region. -/
theorem contDiff_stepWindow_two {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    ContDiff ℝ 2 (stepWindow a w) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    exact contDiffAt_const.congr_of_eventuallyEq
      (stepWindow_eventually_zero hw (by simpa using ha))
  · have habs : ContDiffAt ℝ 2 (fun u : ℝ => |u|) z := contDiffAt_abs hz
    have hinner : ContDiffAt ℝ 2 (fun u : ℝ => (|u| - a) / w) z := by fun_prop
    exact contDiff_smoothstep_two.contDiffAt.comp z hinner

/-- A closed outer-window point is flat through order two, including both
endpoints. Locally, absolute value is replaced by its correct affine branch. -/
theorem stepWindow_complement_zeroTwoJet {a w z : ℝ}
    (ha : 0 < a) (hw : 0 < w) (hz : a + w ≤ |z|) :
    ZeroTwoJet (fun u => 1 - stepWindow a w u) z := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp only [abs_zero] at hz
    linarith
  have harg : 1 ≤ (|z| - a) / w := by
    apply (le_div_iff₀ hw).mpr
    linarith
  have houter : ContDiff ℝ 2 (fun u => 1 - smoothstep u) :=
    contDiff_const.sub contDiff_smoothstep_two
  rcases lt_or_gt_of_ne hz0 with hneg | hpos
  · rw [abs_of_neg hneg] at harg
    have hflat := (smoothstep_complement_zeroTwoJet harg).comp
      (b := fun u : ℝ => (-u - a) / w) (x := z) houter (by fun_prop)
    apply hflat.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hneg] with u hu
    change u < 0 at hu
    simp [stepWindow, abs_of_neg hu]
  · rw [abs_of_pos hpos] at harg
    have hflat := (smoothstep_complement_zeroTwoJet harg).comp
      (b := fun u : ℝ => (u - a) / w) (x := z) houter (by fun_prop)
    apply hflat.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hpos] with u hu
    change 0 < u at hu
    simp [stepWindow, abs_of_pos hu]

/-- The exact manuscript window `ω`. -/
def carmonOmega : ℝ → ℝ := stepWindow (1 / 8) (3 / 8)

/-- The exact manuscript suffix window `ω₃`. -/
def carmonOmegaThree : ℝ → ℝ := stepWindow (1 / 4) (1 / 4)

theorem carmonOmega_zero {z : ℝ} (hz : |z| ≤ 1 / 8) : carmonOmega z = 0 :=
  stepWindow_zero_of_abs_le (by norm_num) hz

theorem carmonOmegaThree_zero {z : ℝ} (hz : |z| ≤ 1 / 4) : carmonOmegaThree z = 0 :=
  stepWindow_zero_of_abs_le (by norm_num) hz

theorem carmonOmega_one {z : ℝ} (hz : 1 / 2 ≤ |z|) : carmonOmega z = 1 :=
  stepWindow_one_of_abs_ge (by norm_num) (by linarith)

theorem carmonOmegaThree_one {z : ℝ} (hz : 1 / 2 ≤ |z|) : carmonOmegaThree z = 1 :=
  stepWindow_one_of_abs_ge (by norm_num) (by linarith)

theorem carmonOmega_lt_one {z : ℝ} (hz : |z| < 1 / 2) : carmonOmega z < 1 :=
  stepWindow_lt_one_of_abs_lt (by norm_num) (by linarith)

theorem carmonOmegaThree_lt_one {z : ℝ} (hz : |z| < 1 / 2) : carmonOmegaThree z < 1 :=
  stepWindow_lt_one_of_abs_lt (by norm_num) (by linarith)

theorem contDiff_carmonOmega_two : ContDiff ℝ 2 carmonOmega :=
  contDiff_stepWindow_two (by norm_num) (by norm_num)

theorem contDiff_carmonOmegaThree_two : ContDiff ℝ 2 carmonOmegaThree :=
  contDiff_stepWindow_two (by norm_num) (by norm_num)

theorem carmonOmega_complement_zeroTwoJet {z : ℝ} (hz : 1 / 2 ≤ |z|) :
    ZeroTwoJet (fun u => 1 - carmonOmega u) z :=
  stepWindow_complement_zeroTwoJet (by norm_num) (by norm_num) (by linarith)

theorem carmonOmegaThree_complement_zeroTwoJet {z : ℝ} (hz : 1 / 2 ≤ |z|) :
    ZeroTwoJet (fun u => 1 - carmonOmegaThree u) z :=
  stepWindow_complement_zeroTwoJet (by norm_num) (by norm_num) (by linarith)

theorem carmonPsi_zeroTwoJet {t : ℝ} (ht : t ≤ 1 / 2) : ZeroTwoJet carmonPsi t := by
  apply ZeroTwoJet.of_contDiff_scalar contDiff_carmonPsi_two (carmonPsi_zero_of_le ht)
  · rw [deriv_carmonPsi, carmonPsiBaseFirst_zero_of_nonpos (by linarith)]
    simp
  · rw [second_deriv_carmonPsi, carmonPsiBaseSecond_zero_of_nonpos (by linarith)]
    simp

theorem actual_chainGateTerm_unique_active {T : ℕ} {z : Fin T → ℝ} {k l : Fin T}
    (hk : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z k ≠ 0)
    (hl : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z l ≠ 0) :
    k = l :=
  chainGateTerm_unique_active (fun _ ht => carmonPsi_zero_of_le ht)
    (fun _ ht => carmonOmega_one ht) (fun _ ht => carmonOmegaThree_one ht) hk hl

theorem actual_chainGateTerm_active_card_le_one {T : ℕ} (z : Fin T → ℝ) :
    (Finset.univ.filter (fun k =>
      chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z k ≠ 0)).card ≤ 1 :=
  chainGateTerm_active_card_le_one (fun _ ht => carmonPsi_zero_of_le ht)
    (fun _ ht => carmonOmega_one ht) (fun _ ht => carmonOmegaThree_one ht)

theorem actual_chainGateTerm_zero_iff {T : ℕ} (z : Fin T → ℝ) (k : Fin T) :
    chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z k = 0 ↔
      |chainPredecessor z k| ≤ 1 / 2 ∨ 1 / 2 ≤ |z k| ∨
        ∃ i, k < i ∧ 1 / 2 ≤ |z i| :=
  chainGateTerm_zero_iff (fun _ ht => carmonPsi_zero_of_le ht)
    (fun _ ht => carmonPsi_pos_of_gt ht)
    (fun _ ht => carmonOmega_one ht) (fun _ ht => carmonOmega_lt_one ht)
    (fun _ ht => carmonOmegaThree_one ht) (fun _ ht => carmonOmegaThree_lt_one ht)
    (fun _ ht => carmonPhi_correction_brackets_pos ht)

/-- Frozen Lemma 1(ii) for the actual scalar functions, with no remaining
scalar regularity, support, positivity, or endpoint-flatness premises. -/
theorem actual_chainGateTerm_zeroTwoJet_of_inactive {T : ℕ} {z : Fin T → ℝ} {k : Fin T}
    (hzero : chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z k = 0) :
    ZeroTwoJet (fun w =>
      chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 w k) z :=
  chainGateTerm_zeroTwoJet_of_inactive
    contDiff_carmonPsi_two contDiff_carmonPhi_two
    contDiff_carmonOmega_two contDiff_carmonOmegaThree_two
    (fun _ ht => carmonPsi_zeroTwoJet ht)
    (fun _ ht => carmonOmega_complement_zeroTwoJet ht)
    (fun _ ht => carmonOmegaThree_complement_zeroTwoJet ht)
    (fun _ ht => carmonPsi_pos_of_gt ht)
    (fun _ ht => carmonOmega_lt_one ht) (fun _ ht => carmonOmegaThree_lt_one ht)
    (fun _ ht => carmonPhi_correction_brackets_pos ht) hzero

theorem contDiff_actual_chainGateTerm_two {T : ℕ} (k : Fin T) :
    ContDiff ℝ 2 (fun z : Fin T → ℝ =>
      chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 z k) :=
  contDiff_chainGateTerm 1 k contDiff_carmonPsi_two contDiff_carmonPhi_two
    contDiff_carmonOmega_two contDiff_carmonOmegaThree_two

end

end HeavyTailedNoise
