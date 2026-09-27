import HeavyTailedNoise.Analysis.GateAlgebra
import HeavyTailedNoise.Analysis.CarmonCoordinates

/-!
Finite-chain support for the exact correction in the frozen gated Haar
construction, Sections 2.3 and 3, Lemma 1. Indices here start at zero;
`chainPredecessor z 0 = 1` implements the manuscript's virtual coordinate.
The link formula is reused from `GateAlgebra.frontierCorrection`.

All scalar support and regularity premises are explicit. No assertion about
Haar measures, oracle access, or the lower-bound theorem is made here.
-/

namespace HeavyTailedNoise

open scoped BigOperators Topology
open Filter

noncomputable section

/-- The virtual predecessor of the first coordinate is one. -/
def chainCorrection {T : ℕ} (ψ φ ω : ℝ → ℝ) (κ : ℝ)
    (z : Fin T → ℝ) (k : Fin T) : ℝ :=
  frontierCorrection ψ φ ω κ (chainPredecessor z k) (z k)

/-- The manuscript's suffix product `Π_k`; an empty suffix has product one. -/
def chainSelector {T : ℕ} (ω₃ : ℝ → ℝ) (z : Fin T → ℝ)
    (k : Fin T) : ℝ :=
  ∏ i ∈ Finset.univ.filter (k < ·), (1 - ω₃ (z i))

/-- The support-bearing factor `q_k Π_k`, before multiplication by the residual gate. -/
def chainGateTerm {T : ℕ} (ψ φ ω ω₃ : ℝ → ℝ) (κ : ℝ)
    (z : Fin T → ℝ) (k : Fin T) : ℝ :=
  chainCorrection ψ φ ω κ z k * chainSelector ω₃ z k

theorem frontierCorrection_eq_zero_of_predecessor_small
    {ψ φ ω : ℝ → ℝ} {κ a b : ℝ}
    (hψ : ∀ t ≤ (1 / 2 : ℝ), ψ t = 0) (ha : |a| ≤ 1 / 2) :
    frontierCorrection ψ φ ω κ a b = 0 := by
  have ha' := (abs_le.mp ha)
  simp [frontierCorrection, hψ a ha'.2, hψ (-a) (by linarith : -a ≤ 1 / 2)]

theorem frontierCorrection_eq_zero_of_current_large
    {ψ φ ω : ℝ → ℝ} {κ a b : ℝ}
    (hω : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω t = 1) (hb : 1 / 2 ≤ |b|) :
    frontierCorrection ψ φ ω κ a b = 0 := by
  simp [frontierCorrection, hω b hb]

theorem chainSelector_eq_zero_of_later_large
    {T : ℕ} {ω₃ : ℝ → ℝ} {z : Fin T → ℝ} {k i : Fin T}
    (hω₃ : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω₃ t = 1)
    (hki : k < i) (hi : 1 / 2 ≤ |z i|) : chainSelector ω₃ z k = 0 := by
  unfold chainSelector
  apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hki⟩)
  simp [hω₃ (z i) hi]

/-- Exact support implications in Lemma 1(i). No positivity or differentiability
is needed in this direction. -/
theorem chainGateTerm_support
    {T : ℕ} {ψ φ ω ω₃ : ℝ → ℝ} {κ : ℝ} {z : Fin T → ℝ} {k : Fin T}
    (hψ : ∀ t ≤ (1 / 2 : ℝ), ψ t = 0)
    (hω : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω t = 1)
    (hω₃ : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω₃ t = 1)
    (hk : chainGateTerm ψ φ ω ω₃ κ z k ≠ 0) :
    (1 / 2 : ℝ) < |chainPredecessor z k| ∧ |z k| < 1 / 2 ∧
      ∀ i, k < i → |z i| < 1 / 2 := by
  have hq : chainCorrection ψ φ ω κ z k ≠ 0 := (mul_ne_zero_iff.mp hk).1
  have hSel : chainSelector ω₃ z k ≠ 0 := (mul_ne_zero_iff.mp hk).2
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    exact hq (frontierCorrection_eq_zero_of_predecessor_small hψ (le_of_not_gt h))
  · by_contra h
    exact hq (frontierCorrection_eq_zero_of_current_large hω (le_of_not_gt h))
  · intro i hki
    by_contra h
    exact hSel (chainSelector_eq_zero_of_later_large hω₃ hki (le_of_not_gt h))

/-- Two distinct finite-chain corrections cannot both be active. This is the
dimension-independent support property in frozen Lemma 1(i). -/
theorem chainGateTerm_unique_active
    {T : ℕ} {ψ φ ω ω₃ : ℝ → ℝ} {κ : ℝ} {z : Fin T → ℝ}
    (hψ : ∀ t ≤ (1 / 2 : ℝ), ψ t = 0)
    (hω : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω t = 1)
    (hω₃ : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω₃ t = 1)
    {k l : Fin T} (hk : chainGateTerm ψ φ ω ω₃ κ z k ≠ 0)
    (hl : chainGateTerm ψ φ ω ω₃ κ z l ≠ 0) : k = l := by
  have hno : ∀ k l : Fin T, k < l →
      chainGateTerm ψ φ ω ω₃ κ z k ≠ 0 →
      chainGateTerm ψ φ ω ω₃ κ z l ≠ 0 → False := by
    intro k l hkl hk hl
    obtain ⟨_, hcurrent, hlater⟩ := chainGateTerm_support hψ hω hω₃ hk
    obtain ⟨hprev, _, _⟩ := chainGateTerm_support hψ hω hω₃ hl
    have hl0 : l.val ≠ 0 := by have := hkl; simp only [Fin.lt_def] at this; omega
    let i : Fin T := ⟨l.val - 1, by omega⟩
    have hki : k ≤ i := by simp only [Fin.le_def]; dsimp [i]; have := hkl; simp only [Fin.lt_def] at this; omega
    have hi : |z i| < 1 / 2 := by
      rcases eq_or_lt_of_le hki with heq | hlt
      · simpa [← heq] using hcurrent
      · exact hlater i hlt
    have hpred : chainPredecessor z l = z i := by simp [chainPredecessor, hl0, i]
    rw [hpred] at hprev
    exact (lt_asymm hprev hi)
  rcases lt_trichotomy k l with hkl | heq | hlk
  · exact (hno k l hkl hk hl).elim
  · exact heq
  · exact (hno l k hlk hl hk).elim

/-- An equivalent finite-set statement of the unique active term property. -/
theorem chainGateTerm_active_card_le_one
    {T : ℕ} {ψ φ ω ω₃ : ℝ → ℝ} {κ : ℝ} {z : Fin T → ℝ}
    (hψ : ∀ t ≤ (1 / 2 : ℝ), ψ t = 0)
    (hω : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω t = 1)
    (hω₃ : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω₃ t = 1) :
    (Finset.univ.filter (fun k => chainGateTerm ψ φ ω ω₃ κ z k ≠ 0)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro k hk l hl
  exact chainGateTerm_unique_active hψ hω hω₃
    (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2

theorem frontierCorrection_pos
    {ψ φ ω : ℝ → ℝ} {κ a b : ℝ}
    (hψ : ∀ t ≤ (1 / 2 : ℝ), ψ t = 0)
    (hψpos : ∀ t, (1 / 2 : ℝ) < t → 0 < ψ t)
    (hω : ∀ t, |t| < (1 / 2 : ℝ) → ω t < 1)
    (hφ : ∀ t, |t| < (1 / 2 : ℝ) →
      0 < φ t - φ 0 + κ ∧ 0 < φ 0 - φ (-t) + κ)
    (ha : (1 / 2 : ℝ) < |a|) (hb : |b| < 1 / 2) :
    0 < frontierCorrection ψ φ ω κ a b := by
  have hb' := hφ b hb
  unfold frontierCorrection
  apply mul_pos _ (sub_pos.mpr (hω b hb))
  rcases lt_abs.mp ha with ha | ha
  · have hneg : ψ (-a) = 0 := hψ (-a) (by linarith)
    simpa [hneg] using mul_pos (hψpos a ha) hb'.1
  · have hpos : ψ a = 0 := hψ a (by linarith)
    simpa [hpos] using mul_pos (hψpos (-a) (by linarith)) hb'.2

/-- The converse support implication explicitly uses strict scalar positivity.
It rules out a zero correction caused by cancellation inside the active region. -/
theorem chainGateTerm_zero_iff
    {T : ℕ} {ψ φ ω ω₃ : ℝ → ℝ} {κ : ℝ} {z : Fin T → ℝ} {k : Fin T}
    (hψ : ∀ t ≤ (1 / 2 : ℝ), ψ t = 0)
    (hψpos : ∀ t, (1 / 2 : ℝ) < t → 0 < ψ t)
    (hωout : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω t = 1)
    (hωin : ∀ t, |t| < (1 / 2 : ℝ) → ω t < 1)
    (hω₃out : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω₃ t = 1)
    (hω₃in : ∀ t, |t| < (1 / 2 : ℝ) → ω₃ t < 1)
    (hφ : ∀ t, |t| < (1 / 2 : ℝ) →
      0 < φ t - φ 0 + κ ∧ 0 < φ 0 - φ (-t) + κ) :
    chainGateTerm ψ φ ω ω₃ κ z k = 0 ↔
      |chainPredecessor z k| ≤ 1 / 2 ∨ 1 / 2 ≤ |z k| ∨
        ∃ i, k < i ∧ 1 / 2 ≤ |z i| := by
  constructor
  · intro hzero
    by_contra h
    push Not at h
    have hq : 0 < chainCorrection ψ φ ω κ z k :=
      frontierCorrection_pos hψ hψpos hωin hφ h.1 h.2.1
    have hSel : 0 < chainSelector ω₃ z k := by
      apply Finset.prod_pos
      intro i hi
      exact sub_pos.mpr (hω₃in (z i) (h.2.2 i (Finset.mem_filter.mp hi).2))
    exact (ne_of_gt (mul_pos hq hSel)) hzero
  · rintro (hprev | hcurrent | ⟨i, hki, hi⟩)
    · simp [chainGateTerm, chainCorrection,
        frontierCorrection_eq_zero_of_predecessor_small hψ hprev]
    · simp [chainGateTerm, chainCorrection,
        frontierCorrection_eq_zero_of_current_large hωout hcurrent]
    · simp [chainGateTerm, chainSelector_eq_zero_of_later_large hω₃out hki hi]

/-- Value, first Frechet derivative, and the derivative of the Frechet derivative
all vanish. `HasFDerivAt` prevents totalized derivative values from hiding
nondifferentiability. -/
structure ZeroTwoJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : Prop where
  value : f x = 0
  first : HasFDerivAt f (0 : E →L[ℝ] ℝ) x
  second : HasFDerivAt (fderiv ℝ f) (0 : E →L[ℝ] E →L[ℝ] ℝ) x

/-- Adapter for scalar endpoint lemmas stated with ordinary derivatives. -/
theorem ZeroTwoJet.of_hasDerivAt {f : ℝ → ℝ} {x : ℝ}
    (hvalue : f x = 0) (hfirst : HasDerivAt f 0 x)
    (hsecond : HasDerivAt (deriv f) 0 x) : ZeroTwoJet f x := by
  refine ⟨hvalue, ?_, ?_⟩
  · simpa using hfirst.hasFDerivAt
  · have heq : fderiv ℝ f =
        (fun y => deriv f y • (1 : ℝ →L[ℝ] ℝ)) := by
      ext y
      simp
    rw [heq]
    simpa using (hsecond.smul_const (1 : ℝ →L[ℝ] ℝ)).hasFDerivAt

section Jets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {x : E}

theorem ZeroTwoJet.derivatives (h : ZeroTwoJet f x) :
    f x = 0 ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0 :=
  ⟨h.value, h.first.fderiv, h.second.fderiv⟩

theorem ZeroTwoJet.add (h : ZeroTwoJet f x) (h' : ZeroTwoJet g x)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    ZeroTwoJet (fun y => f y + g y) x := by
  refine ⟨by simp [h.value, h'.value], ?_, ?_⟩
  · convert! h.first.fun_add h'.first using 1 <;> simp
  · have heq : fderiv ℝ (fun y => f y + g y) =
        (fun y => fderiv ℝ f y + fderiv ℝ g y) :=
      funext fun y => fderiv_fun_add (hf y) (hg y)
    rw [heq]
    convert! h.second.fun_add h'.second using 1 <;> simp

theorem ZeroTwoJet.mul (h : ZeroTwoJet f x)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ZeroTwoJet (fun y => f y * g y) x := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hgdd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  refine ⟨by simp [h.value], ?_, ?_⟩
  · convert! h.first.fun_mul (hgd x).hasFDerivAt using 1 <;> simp [h.value]
  · have heq : fderiv ℝ (fun y => f y * g y) =
        (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) :=
      funext fun y => fderiv_fun_mul (hfd y) (hgd y)
    rw [heq]
    have hleft := h.first.smul (hgdd x).hasFDerivAt
    have hright := (hgd x).hasFDerivAt.smul h.second
    convert! hleft.fun_add hright using 1 <;> simp [h.value, h.first.fderiv]

theorem ZeroTwoJet.mul_left (h : ZeroTwoJet f x)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ZeroTwoJet (fun y => g y * f y) x := by
  simpa only [mul_comm] using h.mul hf hg

/-- A flat factor stays flat after any `C²` coordinate map. -/
theorem ZeroTwoJet.comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : F → ℝ} {b : E → F}
    (h : ZeroTwoJet a (b x)) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) :
    ZeroTwoJet (fun y => a (b y)) x := by
  have had := ha.differentiable (by norm_num)
  have hbd := hb.differentiable (by norm_num)
  have hbdd : Differentiable ℝ (fderiv ℝ b) :=
    (hb.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  refine ⟨h.value, ?_, ?_⟩
  · convert! h.first.comp x (hbd x).hasFDerivAt using 1 <;> simp
  · have heq : fderiv ℝ (fun y => a (b y)) =
        (fun y => (fderiv ℝ a (b y)).comp (fderiv ℝ b y)) :=
      funext fun y => fderiv_comp y (had (b y)) (hbd y)
    rw [heq]
    have houter := h.second.comp x (hbd x).hasFDerivAt
    have hcomp := houter.clm_comp (hbdd x).hasFDerivAt
    simpa [h.first.fderiv] using hcomp

end Jets

theorem contDiff_chainCorrection {T : ℕ} {ψ φ ω : ℝ → ℝ} (κ : ℝ) (k : Fin T)
    (hψ : ContDiff ℝ 2 ψ) (hφ : ContDiff ℝ 2 φ) (hω : ContDiff ℝ 2 ω) :
    ContDiff ℝ 2 (fun z : Fin T → ℝ => chainCorrection ψ φ ω κ z k) := by
  have hp := contDiff_chainPredecessor k
  unfold chainCorrection frontierCorrection
  fun_prop

theorem contDiff_chainSelector {T : ℕ} {ω₃ : ℝ → ℝ} (k : Fin T)
    (hω₃ : ContDiff ℝ 2 ω₃) :
    ContDiff ℝ 2 (fun z : Fin T → ℝ => chainSelector ω₃ z k) := by
  unfold chainSelector
  apply contDiff_prod
  intro i hi
  fun_prop

theorem contDiff_chainGateTerm {T : ℕ} {ψ φ ω ω₃ : ℝ → ℝ} (κ : ℝ) (k : Fin T)
    (hψ : ContDiff ℝ 2 ψ) (hφ : ContDiff ℝ 2 φ) (hω : ContDiff ℝ 2 ω)
    (hω₃ : ContDiff ℝ 2 ω₃) :
    ContDiff ℝ 2 (fun z : Fin T → ℝ => chainGateTerm ψ φ ω ω₃ κ z k) :=
  (contDiff_chainCorrection κ k hψ hφ hω).mul (contDiff_chainSelector k hω₃)

theorem ZeroTwoJet.finsetProd_of_mem
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι]
    {s : Finset ι} {f : ι → E → ℝ} {x : E} {i : ι}
    (hi : i ∈ s) (h : ZeroTwoJet (f i) x)
    (hf : ∀ j ∈ s, ContDiff ℝ 2 (f j)) :
    ZeroTwoJet (fun y => ∏ j ∈ s, f j y) x := by
  have heq : (fun y => ∏ j ∈ s, f j y) =
      (fun y => f i y * ∏ j ∈ s.erase i, f j y) := by
    funext y
    exact (Finset.mul_prod_erase s (fun j => f j y) hi).symm
  rw [heq]
  apply h.mul (hf i hi)
  apply contDiff_prod
  intro j hj
  exact hf j (Finset.mem_of_mem_erase hj)

/-- Flatness of either the predecessor cutoff or the current-coordinate
selector kills the full link correction through second order. -/
theorem chainCorrection_zeroTwoJet
    {T : ℕ} {ψ φ ω : ℝ → ℝ} {κ : ℝ} {z : Fin T → ℝ} {k : Fin T}
    (hψ : ContDiff ℝ 2 ψ) (hφ : ContDiff ℝ 2 φ) (hω : ContDiff ℝ 2 ω)
    (hψflat : ∀ t ≤ (1 / 2 : ℝ), ZeroTwoJet ψ t)
    (hωflat : ∀ t, (1 / 2 : ℝ) ≤ |t| → ZeroTwoJet (fun u => 1 - ω u) t)
    (hz : |chainPredecessor z k| ≤ 1 / 2 ∨ 1 / 2 ≤ |z k|) :
    ZeroTwoJet (fun w => chainCorrection ψ φ ω κ w k) z := by
  have hp := contDiff_chainPredecessor k
  have hc : ContDiff ℝ 2 (fun w : Fin T → ℝ => w k) := by fun_prop
  have hA : ContDiff ℝ 2 (fun w : Fin T → ℝ => φ (w k) - φ 0 + κ) := by fun_prop
  have hB : ContDiff ℝ 2 (fun w : Fin T → ℝ => φ 0 - φ (-w k) + κ) := by fun_prop
  have hC : ContDiff ℝ 2 (fun w : Fin T → ℝ => 1 - ω (w k)) := by fun_prop
  have hP : ContDiff ℝ 2 (fun w : Fin T → ℝ => ψ (chainPredecessor w k)) :=
    hψ.comp hp
  have hN : ContDiff ℝ 2 (fun w : Fin T → ℝ => ψ (-chainPredecessor w k)) :=
    hψ.comp hp.neg
  unfold chainCorrection frontierCorrection
  rcases hz with hz | hz
  · have hpa := (abs_le.mp hz)
    have hPflat := (hψflat (chainPredecessor z k) hpa.2).comp
      (b := fun w : Fin T → ℝ => chainPredecessor w k) (x := z) hψ hp
    have hNflat := (hψflat (-chainPredecessor z k) (by linarith)).comp
      (b := fun w : Fin T → ℝ => -chainPredecessor w k) (x := z) hψ hp.neg
    exact ((hPflat.mul hP hA).add (hNflat.mul hN hB)
      ((hP.mul hA).differentiable (by norm_num))
      ((hN.mul hB).differentiable (by norm_num))).mul
        ((hP.mul hA).add (hN.mul hB)) hC
  · have hflat := (hωflat (z k) hz).comp
      (b := fun w : Fin T → ℝ => w k) (x := z) (contDiff_const.sub hω) hc
    exact hflat.mul_left hC ((hP.mul hA).add (hN.mul hB))

/-- A flat suffix-selector factor kills the entire finite suffix product. -/
theorem chainSelector_zeroTwoJet
    {T : ℕ} {ω₃ : ℝ → ℝ} {z : Fin T → ℝ} {k i : Fin T}
    (hω₃ : ContDiff ℝ 2 ω₃)
    (hω₃flat : ∀ t, (1 / 2 : ℝ) ≤ |t| → ZeroTwoJet (fun u => 1 - ω₃ u) t)
    (hki : k < i) (hi : 1 / 2 ≤ |z i|) :
    ZeroTwoJet (fun w => chainSelector ω₃ w k) z := by
  have hc : ContDiff ℝ 2 (fun w : Fin T → ℝ => w i) := by fun_prop
  have hflat := (hω₃flat (z i) hi).comp
    (b := fun w : Fin T → ℝ => w i) (x := z) (contDiff_const.sub hω₃) hc
  unfold chainSelector
  apply ZeroTwoJet.finsetProd_of_mem (i := i)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hki⟩) hflat
  intro j hj
  fun_prop

/-- Frozen Lemma 1(ii), for `q_k Π_k`, including threshold endpoints.
Global scalar `C²`, endpoint flatness, and strict positivity in the active
windows are separate obligations, rather than project axioms. -/
theorem chainGateTerm_zeroTwoJet_of_inactive
    {T : ℕ} {ψ φ ω ω₃ : ℝ → ℝ} {κ : ℝ} {z : Fin T → ℝ} {k : Fin T}
    (hψ : ContDiff ℝ 2 ψ) (hφ : ContDiff ℝ 2 φ)
    (hω : ContDiff ℝ 2 ω) (hω₃ : ContDiff ℝ 2 ω₃)
    (hψflat : ∀ t ≤ (1 / 2 : ℝ), ZeroTwoJet ψ t)
    (hωflat : ∀ t, (1 / 2 : ℝ) ≤ |t| → ZeroTwoJet (fun u => 1 - ω u) t)
    (hω₃flat : ∀ t, (1 / 2 : ℝ) ≤ |t| → ZeroTwoJet (fun u => 1 - ω₃ u) t)
    (hψpos : ∀ t, (1 / 2 : ℝ) < t → 0 < ψ t)
    (hωin : ∀ t, |t| < (1 / 2 : ℝ) → ω t < 1)
    (hω₃in : ∀ t, |t| < (1 / 2 : ℝ) → ω₃ t < 1)
    (hφpos : ∀ t, |t| < (1 / 2 : ℝ) →
      0 < φ t - φ 0 + κ ∧ 0 < φ 0 - φ (-t) + κ)
    (hzero : chainGateTerm ψ φ ω ω₃ κ z k = 0) :
    ZeroTwoJet (fun w => chainGateTerm ψ φ ω ω₃ κ w k) z := by
  have hψzero : ∀ t ≤ (1 / 2 : ℝ), ψ t = 0 := fun t ht => (hψflat t ht).value
  have hωout : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω t = 1 := by
    intro t ht
    have := (hωflat t ht).value
    linarith
  have hω₃out : ∀ t, (1 / 2 : ℝ) ≤ |t| → ω₃ t = 1 := by
    intro t ht
    have := (hω₃flat t ht).value
    linarith
  have hz := (chainGateTerm_zero_iff hψzero hψpos hωout hωin hω₃out hω₃in hφpos).mp hzero
  unfold chainGateTerm
  rcases hz with hprev | hcurrent | ⟨i, hki, hi⟩
  · exact (chainCorrection_zeroTwoJet hψ hφ hω hψflat hωflat (Or.inl hprev)).mul
      (contDiff_chainCorrection κ k hψ hφ hω) (contDiff_chainSelector k hω₃)
  · exact (chainCorrection_zeroTwoJet hψ hφ hω hψflat hωflat (Or.inr hcurrent)).mul
      (contDiff_chainCorrection κ k hψ hφ hω) (contDiff_chainSelector k hω₃)
  · exact (chainSelector_zeroTwoJet hω₃ hω₃flat hki hi).mul_left
      (contDiff_chainSelector k hω₃) (contDiff_chainCorrection κ k hψ hφ hω)

/-- The ambient residual weight may be any `C²` function: the inactive
correction is still zero through order two after the chain-coordinate map.
Taking `G(y) = 1 - χ(σ_k(y))` gives exactly the remaining product in Lemma 1(ii). -/
theorem inactive_chainGateTerm_weighted_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℕ} {ψ φ ω ω₃ : ℝ → ℝ} {κ : ℝ} {k : Fin T}
    {Z : E → Fin T → ℝ} {G : E → ℝ} {x : E}
    (hψ : ContDiff ℝ 2 ψ) (hφ : ContDiff ℝ 2 φ)
    (hω : ContDiff ℝ 2 ω) (hω₃ : ContDiff ℝ 2 ω₃)
    (hZ : ContDiff ℝ 2 Z) (hG : ContDiff ℝ 2 G)
    (hflat : ZeroTwoJet (fun z => chainGateTerm ψ φ ω ω₃ κ z k) (Z x)) :
    ZeroTwoJet (fun y => G y * chainGateTerm ψ φ ω ω₃ κ (Z y) k) x := by
  have hc := contDiff_chainGateTerm κ k hψ hφ hω hω₃
  exact (hflat.comp hc hZ).mul_left (hc.comp hZ) hG

end

end HeavyTailedNoise
