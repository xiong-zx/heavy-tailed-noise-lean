import HeavyTailedNoise.Analysis.CarmonChainQuantitative

namespace HeavyTailedNoise

open Set Filter
open scoped BigOperators Topology Classical
noncomputable section

theorem carmonPsi_monotone : Monotone carmonPsi :=
  monotone_of_deriv_nonneg (contDiff_carmonPsi_two.differentiable (by norm_num)) deriv_carmonPsi_nonneg

theorem one_le_carmonPsi_of_one_le {t : ℝ} (ht : 1 ≤ t) : 1 ≤ carmonPsi t := by
  calc
    1 = carmonPsi 1 := carmonPsi_one.symm
    _ ≤ carmonPsi t := carmonPsi_monotone ht

theorem one_lt_deriv_carmonPhi_of_abs_lt_one {t : ℝ} (ht : |t| < 1) :
    1 < deriv carmonPhi t := by
  have hs : t ^ 2 < 1 := by
    have h := (sq_lt_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1)).mpr ht
    simpa only [sq_abs, one_pow] using h
  rw [deriv_carmonPhi, ← Real.exp_half 1, ← Real.exp_add, Real.one_lt_exp_iff]
  linarith

theorem chainLinkPrev_nonpos (a b : ℝ) : chainLinkPrev a b ≤ 0 := by
  unfold chainLinkPrev
  nlinarith [mul_nonneg (deriv_carmonPsi_nonneg (-a)) (carmonPhi_pos (-b)).le,
    mul_nonneg (deriv_carmonPsi_nonneg a) (carmonPhi_pos b).le]

theorem chainLinkCurrent_nonpos (a b : ℝ) : chainLinkCurrent a b ≤ 0 := by
  unfold chainLinkCurrent
  nlinarith [mul_nonneg (carmonPsi_nonneg (-a)) (deriv_carmonPhi_pos (-b)).le,
    mul_nonneg (carmonPsi_nonneg a) (deriv_carmonPhi_pos b).le]

theorem chainLinkCurrent_lt_neg_one {a b : ℝ} (ha : 1 ≤ |a|) (hb : |b| < 1) :
    chainLinkCurrent a b < -1 := by
  by_cases ha0 : 0 ≤ a
  · have ha1 : 1 ≤ a := by simpa only [abs_of_nonneg ha0] using ha
    have hψ := one_le_carmonPsi_of_one_le ha1
    have hφ := one_lt_deriv_carmonPhi_of_abs_lt_one hb
    have hm := mul_le_mul_of_nonneg_right hψ (deriv_carmonPhi_pos b).le
    have hp : 1 < carmonPsi a * deriv carmonPhi b := hφ.trans_le (by simpa using hm)
    have hz : carmonPsi (-a) = 0 := carmonPsi_zero_of_le (by linarith)
    simp only [chainLinkCurrent, hz, neg_zero, zero_mul, zero_sub]
    exact neg_lt_neg hp
  · have ha0' : a < 0 := lt_of_not_ge ha0
    have ha1 : 1 ≤ -a := by simpa only [abs_of_neg ha0'] using ha
    have hψ := one_le_carmonPsi_of_one_le ha1
    have hφ := one_lt_deriv_carmonPhi_of_abs_lt_one (t := -b) (by simpa using hb)
    have hm := mul_le_mul_of_nonneg_right hψ (deriv_carmonPhi_pos (-b)).le
    have hp : 1 < carmonPsi (-a) * deriv carmonPhi (-b) := hφ.trans_le (by simpa using hm)
    have hz : carmonPsi a = 0 := carmonPsi_zero_of_le (by linarith)
    simp only [chainLinkCurrent, hz, zero_mul, sub_zero, neg_mul]
    exact neg_lt_neg hp

theorem orthonormal_real_inner_nonneg {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (i k : Fin T) : 0 ≤ inner ℝ (U i) (U k) := by
  rw [orthonormal_iff_ite.mp hU i k]
  split_ifs <;> norm_num

theorem chainPredecessorVector_inner_nonneg {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (i k : Fin T) :
    0 ≤ inner ℝ (chainPredecessorVector U i) (U k) := by
  by_cases hi : i.val = 0
  · simp [chainPredecessorVector, hi]
  · simp only [chainPredecessorVector, dif_neg hi]
    exact orthonormal_real_inner_nonneg hU _ k

/-- The actual ambient Carmon force at a frontier coordinate. -/
theorem fderiv_carmonChain_frontier_lt_neg_one {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (y : Point d) (k : Fin T)
    (hprev : 1 ≤ |chainPredecessor (frameCoordinates U y) k|)
    (hcurrent : |frameCoordinates U y k| < 1) :
    fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x)) y (U k) < -1 := by
  let c : Fin T → ℝ := fun i =>
    chainLinkPrev (chainPredecessor (frameCoordinates U y) i) (frameCoordinates U y i) *
      inner ℝ (chainPredecessorVector U i) (U k) +
    chainLinkCurrent (chainPredecessor (frameCoordinates U y) i) (frameCoordinates U y i) *
      inner ℝ (U i) (U k)
  have hc (i : Fin T) : c i ≤ 0 := add_nonpos
    (mul_nonpos_of_nonpos_of_nonneg (chainLinkPrev_nonpos _ _) (chainPredecessorVector_inner_nonneg hU i k))
    (mul_nonpos_of_nonpos_of_nonneg (chainLinkCurrent_nonpos _ _) (orthonormal_real_inner_nonneg hU i k))
  have hsum : (∑ i : Fin T, c i) ≤ c k := by
    have hr : (∑ i ∈ Finset.univ.erase k, c i) ≤ 0 := Finset.sum_nonpos (fun i _ => hc i)
    have heq := Finset.sum_erase_add Finset.univ c (Finset.mem_univ k)
    linarith
  have hself : inner ℝ (U k) (U k) = 1 := by simpa using orthonormal_iff_ite.mp hU k k
  have hck : c k = chainLinkCurrent (chainPredecessor (frameCoordinates U y) k) (frameCoordinates U y k) := by
    simp [c, chainPredecessorVector_orthogonal hU k, hU.norm_eq_one k]
  rw [(hasFDerivAt_carmonChain_pullback U y).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  change (∑ i : Fin T, c i) < -1
  exact hsum.trans_lt (by rw [hck]; exact chainLinkCurrent_lt_neg_one hprev hcurrent)

theorem exists_carmon_frontier_of_small_coordinate {T : ℕ} (z : Fin T → ℝ)
    (hs : ∃ i, |z i| < 1) : ∃ k, |z k| < 1 ∧ 1 ≤ |chainPredecessor z k| := by
  let s := Finset.univ.filter (fun i : Fin T => |z i| < 1)
  have hsne : s.Nonempty := by
    obtain ⟨i, hi⟩ := hs
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let k := s.min' hsne
  have hkmem : k ∈ s := Finset.min'_mem s hsne
  refine ⟨k, (Finset.mem_filter.mp hkmem).2, ?_⟩
  by_cases hk0 : k.val = 0
  · simp [chainPredecessor, hk0]
  · let i : Fin T := ⟨k.val - 1, by omega⟩
    have hki : ¬ |z i| < 1 := by
      intro hi
      have himem : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      have hle : k ≤ i := Finset.min'_le s i himem
      change k.val ≤ k.val - 1 at hle
      omega
    simpa [chainPredecessor, hk0, i] using le_of_not_gt hki


end

end HeavyTailedNoise
