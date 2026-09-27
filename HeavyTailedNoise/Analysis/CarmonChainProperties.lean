import HeavyTailedNoise.Analysis.CarmonChainStationarity

/-!
Properties of the unscaled Carmon chain on its actual Euclidean domain.
The raw scalar chain remains `carmonChain`; this file only transports that
single definition through the standard orthonormal frame.
-/

namespace HeavyTailedNoise

open scoped BigOperators
noncomputable section

/-- Standard orthonormal frame, including the empty zero-dimensional frame. -/
def carmonStandardFrame (T : ℕ) (i : Fin T) : Point T :=
  EuclideanSpace.single i 1

theorem orthonormal_carmonStandardFrame (T : ℕ) :
    Orthonormal ℝ (carmonStandardFrame T) :=
  EuclideanSpace.orthonormal_single

@[simp] theorem frameCoordinates_carmonStandardFrame {T : ℕ} (x : Point T) :
    frameCoordinates (carmonStandardFrame T) x = (fun i => x i) := by
  funext i
  simp [frameCoordinates, carmonStandardFrame, EuclideanSpace.inner_single_left]

/-- The exact population chain, with the Euclidean norm on its domain. -/
def carmonChainValue {T : ℕ} (x : Point T) : ℝ := carmonChain (fun i => x i)

theorem carmonChainValue_eq_pullback (T : ℕ) :
    (carmonChainValue (T := T)) =
      (fun x => carmonChain (frameCoordinates (carmonStandardFrame T) x)) := by
  funext x
  simp [carmonChainValue]

/-- The unique explicit population gradient, synthesized from the link derivatives. -/
def carmonChainGradient {T : ℕ} (x : Point T) : Point T :=
  ∑ k : Fin T,
    (chainLinkPrev (chainPredecessor (fun i => x i) k) (x k) •
        chainPredecessorVector (carmonStandardFrame T) k +
      chainLinkCurrent (chainPredecessor (fun i => x i) k) (x k) •
        carmonStandardFrame T k)

theorem hasGradientAt_carmonChainValue {T : ℕ} (x : Point T) :
    HasGradientAt carmonChainValue (carmonChainGradient x) x := by
  rw [hasGradientAt_iff_hasFDerivAt, carmonChainValue_eq_pullback]
  convert (hasFDerivAt_carmonChain_pullback (carmonStandardFrame T) x) using 1
  ext v
  simp [carmonChainGradient, InnerProductSpace.toDual_apply_apply,
    innerSL_apply_apply, sum_inner, real_inner_smul_left, inner_add_left]

theorem carmonChainGradient_eq_gradient (T : ℕ) :
    (carmonChainGradient (T := T)) = gradient (carmonChainValue (T := T)) := by
  funext x
  exact (hasGradientAt_carmonChainValue x).unique
    (hasGradientAt_carmonChainValue x).differentiableAt.hasGradientAt

theorem contDiff_carmonChainValue_two (T : ℕ) :
    ContDiff ℝ 2 (carmonChainValue (T := T)) := by
  rw [carmonChainValue_eq_pullback]
  exact (contDiff_carmonChain_two T).comp
    (contDiff_frameCoordinates_two (carmonStandardFrame T))

theorem contDiff_carmonChainGradient_one (T : ℕ) :
    ContDiff ℝ 1 (carmonChainGradient (T := T)) := by
  rw [carmonChainGradient_eq_gradient]
  exact (InnerProductSpace.toDual ℝ (Point T)).symm.contDiff.comp
    ((contDiff_carmonChainValue_two T).fderiv_right (m := 1) (by norm_num))

theorem norm_carmonChainGradient_le_23_sqrt {T : ℕ} (x : Point T) :
    ‖carmonChainGradient x‖ ≤ 23 * Real.sqrt T := by
  have heq : fderiv ℝ carmonChainValue x =
      InnerProductSpace.toDual ℝ (Point T) (carmonChainGradient x) :=
    (hasGradientAt_carmonChainValue x).hasFDerivAt.fderiv
  have hn := norm_fderiv_carmonChain_pullback_le_23_sqrt
    (orthonormal_carmonStandardFrame T) x
  rw [← carmonChainValue_eq_pullback, heq] at hn
  simpa using hn

theorem norm_second_fderiv_carmonChainValue_le_152 {T : ℕ} (x : Point T) :
    ‖fderiv ℝ (fderiv ℝ (carmonChainValue (T := T))) x‖ ≤ 152 := by
  rw [carmonChainValue_eq_pullback]
  exact norm_second_fderiv_carmonChain_pullback_le_152
    (orthonormal_carmonStandardFrame T) x

theorem lipschitzWith_carmonChainGradient (T : ℕ) :
    LipschitzWith 152 (carmonChainGradient (T := T)) := by
  have hf : Differentiable ℝ (fderiv ℝ (carmonChainValue (T := T))) :=
    ((contDiff_carmonChainValue_two T).fderiv_right
      (m := 1) (by norm_num)).differentiable (by norm_num)
  have hLips : LipschitzWith 152 (fderiv ℝ (carmonChainValue (T := T))) :=
    lipschitzWith_of_nnnorm_fderiv_le hf (fun x => by
      exact_mod_cast norm_second_fderiv_carmonChainValue_le_152 x)
  have hcomp := (InnerProductSpace.toDual ℝ (Point T)).symm.lipschitz.comp hLips
  rw [one_mul] at hcomp
  rw [carmonChainGradient_eq_gradient]
  exact hcomp

theorem norm_carmonChainGradient_sub_le_152 {T : ℕ} (x y : Point T) :
    ‖carmonChainGradient x - carmonChainGradient y‖ ≤ 152 * ‖x - y‖ :=
  (lipschitzWith_carmonChainGradient T).norm_sub_le x y

theorem continuous_carmonChainGradient (T : ℕ) :
    Continuous (carmonChainGradient (T := T)) :=
  (lipschitzWith_carmonChainGradient T).continuous

theorem norm_fderiv_carmonChainGradient_le_152 {T : ℕ} (x : Point T) :
    ‖fderiv ℝ (carmonChainGradient (T := T)) x‖ ≤ 152 :=
  norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_carmonChainGradient T)

theorem carmonChainValue_gap_le_12T {T : ℕ} (x : Point T) :
    carmonChainValue (0 : Point T) - carmonChainValue x ≤ 12 * T := by
  have hl := carmonChain_lower_bound (fun i => x i)
  have hz := carmonChain_zero_nonpos T
  change carmonChain (fun _ : Fin T => 0) - carmonChain (fun i => x i) ≤ _
  linarith

private theorem carmon_sum_apply {T : ℕ} (v : Fin T → Point T) (i : Fin T) :
    (∑ k, v k) i = ∑ k, v k i := by
  change (WithLp.ofLp (∑ k, v k)) i = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

private theorem carmonStandardFrame_synthesis_apply {T : ℕ}
    (c : Fin T → ℝ) (i : Fin T) :
    (∑ k : Fin T, c k • carmonStandardFrame T k) i = c i := by
  simp [carmon_sum_apply, carmonStandardFrame, PiLp.single_apply]

private theorem carmonPredecessor_synthesis_apply {T : ℕ}
    (c : Fin T → ℝ) (i : Fin T) :
    (∑ k : Fin T, c k • chainPredecessorVector (carmonStandardFrame T) k) i =
      if h : i.val + 1 < T then c ⟨i.val + 1, h⟩ else 0 := by
  classical
  by_cases hs : i.val + 1 < T
  · simp only [dif_pos hs]
    let j : Fin T := ⟨i.val + 1, hs⟩
    have hj : j.val ≠ 0 := by dsimp [j]; omega
    have hji : (⟨j.val - 1, by omega⟩ : Fin T) = i := by
      apply Fin.ext
      simp [j]
    rw [carmon_sum_apply]
    calc
      (∑ k : Fin T, (c k • chainPredecessorVector (carmonStandardFrame T) k) i) =
          (c j • chainPredecessorVector (carmonStandardFrame T) j) i := by
        apply Finset.sum_eq_single j
        · intro k hk hkj
          by_cases hk0 : k.val = 0
          · simp [chainPredecessorVector, hk0]
          · have hpred : (⟨k.val - 1, by omega⟩ : Fin T) ≠ i := by
              intro h
              apply hkj
              apply Fin.ext
              have hv := congrArg Fin.val h
              dsimp [j] at *
              omega
            simp [chainPredecessorVector, hk0, carmonStandardFrame,
              PiLp.single_apply, hpred, Ne.symm hpred]
        · simp
      _ = c ⟨i.val + 1, hs⟩ := by
        simp [chainPredecessorVector, hj, hji, carmonStandardFrame,
          PiLp.single_apply, j]
  · simp only [dif_neg hs]
    rw [carmon_sum_apply]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hk0 : k.val = 0
    · simp [chainPredecessorVector, hk0]
    · have hpred : (⟨k.val - 1, by omega⟩ : Fin T) ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_mk] at hv
        omega
      simp [chainPredecessorVector, hk0, carmonStandardFrame,
        PiLp.single_apply, hpred, Ne.symm hpred]

/-- Each coordinate receives exactly its current link and its successor link. -/
theorem carmonChainGradient_apply {T : ℕ} (x : Point T) (i : Fin T) :
    carmonChainGradient x i =
      chainLinkCurrent (chainPredecessor (fun k => x k) i) (x i) +
        if h : i.val + 1 < T then chainLinkPrev (x i) (x ⟨i.val + 1, h⟩) else 0 := by
  unfold carmonChainGradient
  rw [Finset.sum_add_distrib]
  simp only [PiLp.add_apply, carmonStandardFrame_synthesis_apply,
    carmonPredecessor_synthesis_apply]
  by_cases hs : i.val + 1 < T
  · simp only [dif_pos hs]
    have hj : i.val + 1 ≠ 0 := by omega
    have hji : (⟨i.val + 1 - 1, by omega⟩ : Fin T) = i := by
      apply Fin.ext
      simp
    simp [chainPredecessor, hj, hji, add_comm]
  · simp [hs]

theorem abs_carmonChainGradient_apply_le_23 {T : ℕ} (x : Point T) (i : Fin T) :
    |carmonChainGradient x i| ≤ 23 := by
  rw [carmonChainGradient_apply]
  split_ifs
  · exact (abs_add_le _ _).trans
      ((add_le_add (abs_chainLinkCurrent_le _ _) (abs_chainLinkPrev_le _ _)).trans
        (by norm_num))
  · simpa using (abs_chainLinkCurrent_le
      (chainPredecessor (fun k => x k) i) (x i)).trans (by norm_num)

theorem chainLinkPrev_eq_zero_of_abs_le_half {a b : ℝ} (ha : |a| ≤ 1 / 2) :
    chainLinkPrev a b = 0 := by
  have hap := (abs_le.mp ha).2
  have han : -a ≤ 1 / 2 := by linarith [(abs_le.mp ha).1]
  simp [chainLinkPrev, deriv_carmonPsi_zero_of_le hap, deriv_carmonPsi_zero_of_le han]

theorem chainLinkCurrent_eq_zero_of_abs_le_half {a b : ℝ} (ha : |a| ≤ 1 / 2) :
    chainLinkCurrent a b = 0 := by
  have hap := (abs_le.mp ha).2
  have han : -a ≤ 1 / 2 := by linarith [(abs_le.mp ha).1]
  simp [chainLinkCurrent, carmonPsi_zero_of_le hap, carmonPsi_zero_of_le han]

/-- The robust zero-chain property uses both predecessor and current thresholds. -/
theorem carmonChainGradient_apply_eq_zero {T : ℕ} (x : Point T) (i : Fin T)
    (hprev : |chainPredecessor (fun k => x k) i| ≤ 1 / 2)
    (hcurrent : |x i| ≤ 1 / 2) : carmonChainGradient x i = 0 := by
  rw [carmonChainGradient_apply, chainLinkCurrent_eq_zero_of_abs_le_half hprev]
  split_ifs <;> simp [chainLinkPrev_eq_zero_of_abs_le_half hcurrent]

theorem carmonChainGradient_tail_eq_zero {T n : ℕ} (x : Point T)
    (hx : ∀ i : Fin T, n ≤ i.val → |x i| ≤ 1 / 2)
    (i : Fin T) (hi : n + 1 ≤ i.val) : carmonChainGradient x i = 0 := by
  have hi0 : i.val ≠ 0 := by omega
  apply carmonChainGradient_apply_eq_zero
  · simpa [chainPredecessor, hi0] using
      hx ⟨i.val - 1, by omega⟩ (by change n ≤ i.val - 1; omega)
  · exact hx i (by omega)

/-- A coordinate with magnitude below one prevents stationarity of the chain. -/
theorem one_lt_norm_carmonChainGradient_of_small_coordinate {T : ℕ} (x : Point T)
    (hx : ∃ i : Fin T, |x i| < 1) : 1 < ‖carmonChainGradient x‖ := by
  obtain ⟨k, hk, hp⟩ := exists_carmon_frontier_of_small_coordinate (fun i => x i) hx
  have hfront := fderiv_carmonChain_frontier_lt_neg_one
    (orthonormal_carmonStandardFrame T) x k (by simpa using hp) (by simpa using hk)
  rw [← carmonChainValue_eq_pullback,
    (hasGradientAt_carmonChainValue x).hasFDerivAt.fderiv] at hfront
  have hc : carmonChainGradient x k < -1 := by
    simpa [InnerProductSpace.toDual_apply_apply, carmonStandardFrame,
      EuclideanSpace.inner_single_right] using hfront
  have hcoord : |carmonChainGradient x k| ≤ ‖carmonChainGradient x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (carmonChainGradient x) k
  have ha := neg_le_abs (carmonChainGradient x k)
  linarith

end
end HeavyTailedNoise
