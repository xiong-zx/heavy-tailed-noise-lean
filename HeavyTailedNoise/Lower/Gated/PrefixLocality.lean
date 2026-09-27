import HeavyTailedNoise.Lower.Gated.HardPreprojectionBounds

/-!
Exact deterministic prefix locality for Lemmas 4 and 7 of the frozen gated
Haar construction. The zero-based index `j` denotes the last revealed vector;
`prefixHardPotential U j` is the manuscript's `H^(j+1)`. Setting the unrevealed
frame vectors to zero uses the existing objective and automatically retains
its boundary correction. No norm bound is imposed on the ambient query.
-/

namespace HeavyTailedNoise

open Filter
open scoped BigOperators Topology Classical

noncomputable section

/-- Retain the revealed prefix and set all unrevealed vectors to zero. -/
def prefixFrame {d T : ℕ} (U : Fin T → Point d) (j : Fin T) (i : Fin T) : Point d :=
  if i ≤ j then U i else 0

/-- The exact truncated response potential, with the original radius `2500√T`. -/
def prefixHardPotential {d T : ℕ} (U : Fin T → Point d) (j : Fin T) : Point d → ℝ :=
  hardPotential (prefixFrame U j)

def prefixAccidentSet {d T : ℕ} (U : Fin T → Point d) (j : Fin T) : Set (Point d) :=
  {y | ∃ i, j < i ∧ (1 / 32 : ℝ) ≤ |frameCoordinates U y i|}

def prefixCapSet {d T : ℕ} (U : Fin T → Point d) (j : Fin T) : Set (Point d) :=
  {y | (1 / 2 : ℝ) ≤ |frameCoordinates U y j| ∧
    ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) y‖ ^ 2 ≤ 1000 + 1 / 16 + 1}

def prefixGoodSet {d T : ℕ} (U : Fin T → Point d) (j : Fin T) : Set (Point d) :=
  (prefixAccidentSet U j ∪ prefixCapSet U j)ᶜ

theorem mem_prefixGoodSet_iff {d T : ℕ} (U : Fin T → Point d) (j : Fin T) (y : Point d) :
    y ∈ prefixGoodSet U j ↔
      (∀ i, j < i → |frameCoordinates U y i| < (1 / 32 : ℝ)) ∧
      (|frameCoordinates U y j| < (1 / 2 : ℝ) ∨
        1000 + 1 / 16 + 1 < ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) y‖ ^ 2) := by
  simp only [prefixGoodSet, prefixAccidentSet, prefixCapSet, Set.mem_compl_iff,
    Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, not_le]
  constructor
  · rintro ⟨hf, hg⟩
    refine ⟨hf, ?_⟩
    by_cases h : |frameCoordinates U y j| < (1 / 2 : ℝ)
    · exact Or.inl h
    · exact Or.inr (hg (le_of_not_gt h))
  · rintro ⟨hf, hsmall | hfar⟩
    · refine ⟨hf, ?_⟩
      intro h
      linarith
    · exact ⟨hf, fun _ => hfar⟩

theorem prefixFrame_eq_of_agree {d T : ℕ} {U V : Fin T → Point d} (j : Fin T)
    (h : ∀ i, i ≤ j → U i = V i) : prefixFrame U j = prefixFrame V j := by
  funext i
  by_cases hi : i ≤ j <;> simp [prefixFrame, hi, h i]

/-- The entire truncated response depends only on the revealed frame prefix. -/
theorem prefixHardPotential_eq_of_agree {d T : ℕ} {U V : Fin T → Point d} (j : Fin T)
    (h : ∀ i, i ≤ j → U i = V i) : prefixHardPotential U j = prefixHardPotential V j := by
  rw [prefixHardPotential, prefixHardPotential, prefixFrame_eq_of_agree j h]

theorem frameCoordinates_prefixFrame_of_le {d T : ℕ} (U : Fin T → Point d)
    (j i : Fin T) (y : Point d) (hi : i ≤ j) :
    frameCoordinates (prefixFrame U j) y i = frameCoordinates U y i := by
  simp [frameCoordinates, prefixFrame, hi]

theorem frameCoordinates_prefixFrame_of_gt {d T : ℕ} (U : Fin T → Point d)
    (j i : Fin T) (y : Point d) (hi : j < i) :
    frameCoordinates (prefixFrame U j) y i = 0 := by
  simp [frameCoordinates, prefixFrame, not_le.mpr hi]

theorem chainPredecessor_prefixFrame {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : k.val ≤ j.val + 1) :
    chainPredecessor (frameCoordinates (prefixFrame U j) y) k =
      chainPredecessor (frameCoordinates U y) k := by
  by_cases hzero : k.val = 0
  · simp [chainPredecessor, hzero]
  · simp only [chainPredecessor, dif_neg hzero]
    exact frameCoordinates_prefixFrame_of_le U j _ y (by change k.val - 1 ≤ j.val; omega)

theorem frameOrthogonalResidual_prefixFrame_of_le {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : k ≤ j) :
    frameOrthogonalResidual (prefixFrame U j) (Finset.univ.filter (· ≤ k)) y =
      frameOrthogonalResidual U (Finset.univ.filter (· ≤ k)) y := by
  unfold frameOrthogonalResidual
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := le_trans (Finset.mem_filter.mp hi).2 hk
  simp [frameCoordinates, prefixFrame, hij]

theorem prefix_flat_windowThree {d T : ℕ} (U : Fin T → Point d) (j : Fin T) (y : Point d)
    (hfuture : ∀ i, j < i → |frameCoordinates U y i| < (1 / 32 : ℝ)) (i : Fin T) :
    carmonOmegaThree (frameCoordinates (prefixFrame U j) y i) =
      carmonOmegaThree (frameCoordinates U y i) := by
  by_cases hi : i ≤ j
  · rw [frameCoordinates_prefixFrame_of_le U j i y hi]
  · have hji := lt_of_not_ge hi
    rw [frameCoordinates_prefixFrame_of_gt U j i y hji,
      carmonOmegaThree_zero (by norm_num : |(0 : ℝ)| ≤ 1 / 4),
      carmonOmegaThree_zero (by linarith [hfuture i hji])]

theorem prefix_flat_windowSix_mass {d T : ℕ} (U : Fin T → Point d) (j : Fin T) (y : Point d)
    (hfuture : ∀ i, j < i → |frameCoordinates U y i| < (1 / 32 : ℝ)) (i : Fin T) :
    carmonOmegaSix (frameCoordinates (prefixFrame U j) y i) *
        (frameCoordinates (prefixFrame U j) y i) ^ 2 =
      carmonOmegaSix (frameCoordinates U y i) * (frameCoordinates U y i) ^ 2 := by
  by_cases hi : i ≤ j
  · rw [frameCoordinates_prefixFrame_of_le U j i y hi]
  · have hji := lt_of_not_ge hi
    rw [frameCoordinates_prefixFrame_of_gt U j i y hji,
      carmonOmegaSix_zero (z := frameCoordinates U y i) (by linarith [hfuture i hji])]
    simp

theorem chainSelector_prefixFrame {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d)
    (hfuture : ∀ i, j < i → |frameCoordinates U y i| < (1 / 32 : ℝ)) :
    chainSelector carmonOmegaThree (frameCoordinates (prefixFrame U j) y) k =
      chainSelector carmonOmegaThree (frameCoordinates U y) k := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [prefix_flat_windowThree U j y hfuture i]

theorem gatedResidual_prefixFrame_of_le {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : k ≤ j)
    (hfuture : ∀ i, j < i → |frameCoordinates U y i| < (1 / 32 : ℝ)) :
    gatedResidual (prefixFrame U j) k y = gatedResidual U k y := by
  unfold gatedResidual
  rw [frameOrthogonalResidual_prefixFrame_of_le U j k y hk]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact prefix_flat_windowSix_mass U j y hfuture i

/-- A view of the existing preprojection potential as a sum of paired links. -/
def hardPreprojectionLink {d T : ℕ} (U : Fin T → Point d) (k : Fin T) (y : Point d) : ℝ :=
  carmonChainLink (chainPredecessor (frameCoordinates U y) k) (frameCoordinates U y k) +
    (1 - carmonChi (gatedResidual U k y)) *
      chainGateTerm carmonPsi carmonPhi carmonOmega carmonOmegaThree 1 (frameCoordinates U y) k

theorem hardPreprojectionPotential_eq_sum {d T : ℕ} (U : Fin T → Point d) (y : Point d) :
    hardPreprojectionPotential U y = ∑ k, hardPreprojectionLink U k y := by
  unfold hardPreprojectionPotential hardPreprojectionLink
  rw [carmonChain_eq_sum_links]
  simp only [gatedCorrection, Finset.sum_add_distrib]

theorem hardPreprojectionLink_prefixFrame_of_le {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : k ≤ j)
    (hfuture : ∀ i, j < i → |frameCoordinates U y i| < (1 / 32 : ℝ)) :
    hardPreprojectionLink (prefixFrame U j) k y = hardPreprojectionLink U k y := by
  unfold hardPreprojectionLink chainGateTerm chainCorrection
  rw [frameCoordinates_prefixFrame_of_le U j k y hk,
    chainPredecessor_prefixFrame U j k y (by omega),
    gatedResidual_prefixFrame_of_le U j k y hk hfuture,
    chainSelector_prefixFrame U j k y hfuture]

theorem hardPreprojectionLink_zero_of_predecessor_small {d T : ℕ}
    (U : Fin T → Point d) (k : Fin T) (y : Point d)
    (hsmall : |chainPredecessor (frameCoordinates U y) k| ≤ (1 / 2 : ℝ)) :
    hardPreprojectionLink U k y = 0 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hsmall
  have hp := carmonPsi_zero_of_le hhi
  have hn := carmonPsi_zero_of_le (by linarith :
    -chainPredecessor (frameCoordinates U y) k ≤ (1 / 2 : ℝ))
  simp [hardPreprojectionLink, carmonChainLink, chainGateTerm, chainCorrection,
    frontierCorrection, hp, hn]


theorem chainPredecessor_at_successor {T : ℕ} (z : Fin T → ℝ) (j k : Fin T)
    (hk : k.val = j.val + 1) : chainPredecessor z k = z j := by
  have hzero : k.val ≠ 0 := by omega
  simp only [chainPredecessor, dif_neg hzero]
  congr 1
  apply Fin.ext
  dsimp
  omega

theorem prefix_filter_successor {T : ℕ} (j k : Fin T) (hk : k.val = j.val + 1) :
    Finset.univ.filter (· ≤ k) = insert k (Finset.univ.filter (· ≤ j)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hi
    by_cases hik : i = k
    · exact Or.inl hik
    · right
      change i.val ≤ j.val
      have hneq : i.val ≠ k.val := fun hv => hik (Fin.ext hv)
      change i.val ≤ k.val at hi
      omega
  · rintro (rfl | hi)
    · exact le_rfl
    · change i.val ≤ k.val
      change i.val ≤ j.val at hi
      omega

theorem frameOrthogonalResidual_prefixFrame_successor {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : k.val = j.val + 1) :
    frameOrthogonalResidual (prefixFrame U j) (Finset.univ.filter (· ≤ k)) y =
      frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) y := by
  have hkj : j < k := by change j.val < k.val; omega
  have hnot : k ∉ Finset.univ.filter (· ≤ j) := by simp [not_le.mpr hkj]
  calc
    _ = frameOrthogonalResidual (prefixFrame U j) (Finset.univ.filter (· ≤ j)) y := by
      unfold frameOrthogonalResidual
      rw [prefix_filter_successor j k hk, Finset.sum_insert hnot,
        frameCoordinates_prefixFrame_of_gt U j k y hkj]
      simp
    _ = _ := frameOrthogonalResidual_prefixFrame_of_le U j j y le_rfl

theorem frameOrthogonalResidual_norm_sq_successor {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (j k : Fin T) (y : Point d) (hk : k.val = j.val + 1) :
    ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ k)) y‖ ^ 2 =
      ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) y‖ ^ 2 -
        (frameCoordinates U y k) ^ 2 := by
  have hkj : j < k := by change j.val < k.val; omega
  have hnot : k ∉ Finset.univ.filter (· ≤ j) := by simp [not_le.mpr hkj]
  rw [frameOrthogonalResidual_norm_sq hU, frameOrthogonalResidual_norm_sq hU,
    prefix_filter_successor j k hk, Finset.sum_insert hnot]
  ring

theorem carmonChi_zero_of_ge {s : ℝ} (hs : 1000 + 1 / 16 ≤ s) : carmonChi s = 0 := by
  unfold carmonChi
  rw [smoothstep_one_of_one_le (by linarith : (1 : ℝ) ≤ (s - 1 / 16) / 1000)]
  norm_num

theorem chainSelector_one_after_prefix {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hjk : j ≤ k)
    (hfuture : ∀ i, j < i → |frameCoordinates U y i| < (1 / 32 : ℝ)) :
    chainSelector carmonOmegaThree (frameCoordinates U y) k = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  have hji : j < i := lt_of_le_of_lt hjk (Finset.mem_filter.mp hi).2
  rw [carmonOmegaThree_zero (by linarith [hfuture i hji])]
  norm_num

theorem gatedResidual_eq_prefix_norm_after_prefix {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hjk : j ≤ k)
    (hfuture : ∀ i, j < i → |frameCoordinates U y i| < (1 / 32 : ℝ)) :
    gatedResidual U k y = ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ k)) y‖ ^ 2 := by
  unfold gatedResidual
  have hs : (∑ i ∈ Finset.univ.filter (k < ·),
      carmonOmegaSix (frameCoordinates U y i) * (frameCoordinates U y i) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hji : j < i := lt_of_le_of_lt hjk (Finset.mem_filter.mp hi).2
    rw [carmonOmegaSix_zero (by linarith [hfuture i hji]), zero_mul]
  rw [hs, sub_zero]

theorem gatedResidual_prefixFrame_successor {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : k.val = j.val + 1) :
    gatedResidual (prefixFrame U j) k y =
      ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) y‖ ^ 2 := by
  unfold gatedResidual
  rw [frameOrthogonalResidual_prefixFrame_successor U j k y hk]
  have hs : (∑ i ∈ Finset.univ.filter (k < ·),
      carmonOmegaSix (frameCoordinates (prefixFrame U j) y i) *
        (frameCoordinates (prefixFrame U j) y i) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hji : j < i := by
      have hki := (Finset.mem_filter.mp hi).2
      change k.val < i.val at hki
      change j.val < i.val
      omega
    rw [frameCoordinates_prefixFrame_of_gt U j i y hji]
    simp
  rw [hs, sub_zero]

theorem hardPreprojectionLink_prefixFrame_of_tail {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : j.val + 1 < k.val)
    (hfuture : ∀ i, j < i → |frameCoordinates U y i| < (1 / 32 : ℝ)) :
    hardPreprojectionLink (prefixFrame U j) k y = hardPreprojectionLink U k y := by
  have hzero : k.val ≠ 0 := by omega
  let i : Fin T := ⟨k.val - 1, by omega⟩
  have hji : j < i := by change j.val < k.val - 1; omega
  have hp : chainPredecessor (frameCoordinates U y) k = frameCoordinates U y i := by
    simp [chainPredecessor, hzero, i]
  have ht : chainPredecessor (frameCoordinates (prefixFrame U j) y) k = 0 := by
    simp only [chainPredecessor, dif_neg hzero]
    exact frameCoordinates_prefixFrame_of_gt U j i y hji
  rw [hardPreprojectionLink_zero_of_predecessor_small U k y (by rw [hp]; linarith [hfuture i hji]),
    hardPreprojectionLink_zero_of_predecessor_small (prefixFrame U j) k y (by rw [ht]; norm_num)]

theorem hardPreprojectionLink_prefixFrame_of_successor {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (j k : Fin T) (y : Point d) (hk : k.val = j.val + 1)
    (hfuture : ∀ i, j < i → |frameCoordinates U y i| < (1 / 32 : ℝ))
    (hcap : |frameCoordinates U y j| < (1 / 2 : ℝ) ∨
      1000 + 1 / 16 + 1 < ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) y‖ ^ 2) :
    hardPreprojectionLink (prefixFrame U j) k y = hardPreprojectionLink U k y := by
  have hkj : j < k := by change j.val < k.val; omega
  have hp := chainPredecessor_at_successor (frameCoordinates U y) j k hk
  have hpt : chainPredecessor (frameCoordinates (prefixFrame U j) y) k = frameCoordinates U y j := by
    rw [chainPredecessor_at_successor _ j k hk, frameCoordinates_prefixFrame_of_le U j j y le_rfl]
  rcases hcap with hsmall | hfar
  · rw [hardPreprojectionLink_zero_of_predecessor_small U k y (by rw [hp]; exact hsmall.le),
      hardPreprojectionLink_zero_of_predecessor_small (prefixFrame U j) k y
        (by rw [hpt]; exact hsmall.le)]
  · have hb := hfuture k hkj
    have hb1 : (frameCoordinates U y k) ^ 2 < (1 : ℝ) := by
      have h := (sq_lt_sq₀ (abs_nonneg (frameCoordinates U y k)) (by norm_num : (0 : ℝ) ≤ 1)).mpr
        (show |frameCoordinates U y k| < (1 : ℝ) by linarith)
      simpa only [sq_abs, one_pow] using h
    have hσ := gatedResidual_eq_prefix_norm_after_prefix U j k y hkj.le hfuture
    rw [frameOrthogonalResidual_norm_sq_successor hU j k y hk] at hσ
    have hχ : carmonChi (gatedResidual U k y) = 0 :=
      carmonChi_zero_of_ge (by rw [hσ]; linarith)
    have hχt : carmonChi (gatedResidual (prefixFrame U j) k y) = 0 :=
      carmonChi_zero_of_ge (by rw [gatedResidual_prefixFrame_successor U j k y hk]; linarith)
    have hsel := chainSelector_one_after_prefix U j k y hkj.le hfuture
    have hselt : chainSelector carmonOmegaThree (frameCoordinates (prefixFrame U j) y) k = 1 := by
      rw [chainSelector_prefixFrame U j k y hfuture, hsel]
    have hω : carmonOmega (frameCoordinates U y k) = 0 := carmonOmega_zero (by linarith)
    have hω0 : carmonOmega 0 = 0 := carmonOmega_zero (by norm_num)
    have hf := gated_frontier_cancellation carmonPsi carmonPhi carmonOmega carmonChi 1
      (frameCoordinates U y j) (frameCoordinates U y k) (gatedResidual U k y) hω hχ
    have ht := gated_frontier_cancellation carmonPsi carmonPhi carmonOmega carmonChi 1
      (frameCoordinates U y j) 0 (gatedResidual (prefixFrame U j) k y) hω0 hχt
    unfold hardPreprojectionLink chainGateTerm chainCorrection
    rw [hp, hpt, frameCoordinates_prefixFrame_of_gt U j k y hkj, hsel, hselt, mul_one, mul_one]
    exact ht.trans hf.symm

/-- The manuscript's exact function identity on its good region. -/
theorem hardPreprojectionPotential_eq_prefix_of_good {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (j : Fin T) (y : Point d) (hy : y ∈ prefixGoodSet U j) :
    hardPreprojectionPotential U y = hardPreprojectionPotential (prefixFrame U j) y := by
  obtain ⟨hfuture, hcap⟩ := (mem_prefixGoodSet_iff U j y).mp hy
  rw [hardPreprojectionPotential_eq_sum, hardPreprojectionPotential_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  symm
  by_cases hkj : k ≤ j
  · exact hardPreprojectionLink_prefixFrame_of_le U j k y hkj hfuture
  by_cases hsucc : k.val = j.val + 1
  · exact hardPreprojectionLink_prefixFrame_of_successor hU j k y hsucc hfuture hcap
  · exact hardPreprojectionLink_prefixFrame_of_tail U j k y (by
      have hlt := lt_of_not_ge hkj
      change j.val < k.val at hlt
      omega) hfuture

theorem prefixGoodSet_mem_nhds {d T : ℕ} (U : Fin T → Point d) (j : Fin T)
    {y : Point d} (hy : y ∈ prefixGoodSet U j) : prefixGoodSet U j ∈ 𝓝 y := by
  obtain ⟨hfuture, hcap⟩ := (mem_prefixGoodSet_iff U j y).mp hy
  have hc (i : Fin T) : Continuous (fun x : Point d => |frameCoordinates U x i|) :=
    (((contDiff_pi.mp (contDiff_frameCoordinates_two U)) i).continuous).abs
  have hf : ∀ᶠ x in 𝓝 y, ∀ i, j < i → |frameCoordinates U x i| < (1 / 32 : ℝ) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : j < i
    · filter_upwards [(isOpen_lt (hc i) continuous_const).mem_nhds (hfuture i hi)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall (fun x hx => (hi hx).elim)
  have hg : ∀ᶠ x in 𝓝 y, |frameCoordinates U x j| < (1 / 2 : ℝ) ∨
      1000 + 1 / 16 + 1 < ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) x‖ ^ 2 := by
    rcases hcap with hsmall | hfar
    · filter_upwards [(isOpen_lt (hc j) continuous_const).mem_nhds hsmall] with x hx
      exact Or.inl hx
    · have hr : Continuous (fun x : Point d =>
          ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) x‖ ^ 2) :=
        ((contDiff_frameOrthogonalResidual_two U _).norm_sq ℝ).continuous
      filter_upwards [(isOpen_lt continuous_const hr).mem_nhds hfar] with x hx
      exact Or.inr hx
  filter_upwards [hf, hg] with x hxf hxg
  exact (mem_prefixGoodSet_iff U j x).mpr ⟨hxf, hxg⟩

theorem hardPreprojectionPotential_eventuallyEq_prefix {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (j : Fin T) {y : Point d} (hy : y ∈ prefixGoodSet U j) :
    hardPreprojectionPotential U =ᶠ[𝓝 y] hardPreprojectionPotential (prefixFrame U j) := by
  filter_upwards [prefixGoodSet_mem_nhds U j hy] with x hx
  exact hardPreprojectionPotential_eq_prefix_of_good hU j x hx

/-- Neighborhood equality after soft projection, for arbitrary ambient queries. -/
theorem hardPotential_eventuallyEq_prefix {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (j : Fin T) {x : Point d}
    (hx : softProjection (hardRadius T) x ∈ prefixGoodSet U j) :
    hardPotential U =ᶠ[𝓝 x] prefixHardPotential U j := by
  have hT : 0 < T := by have h := j.isLt; omega
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < hardRadius T := by unfold hardRadius; positivity
  have heq := (hardPreprojectionPotential_eventuallyEq_prefix hU j hx).comp_tendsto
    (contDiff_softProjection_two hR).continuous.continuousAt.tendsto
  filter_upwards [heq] with z hz
  simp only [Function.comp_apply] at hz
  change hardPreprojectionPotential U (softProjection (hardRadius T) z) + (1 / 10 : ℝ) * ‖z‖ ^ 2 =
    hardPreprojectionPotential (prefixFrame U j) (softProjection (hardRadius T) z) +
      (1 / 10 : ℝ) * ‖z‖ ^ 2
  rw [hz]

theorem fderiv_hardPotential_eq_prefix_of_good {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (j : Fin T) (x : Point d)
    (hx : softProjection (hardRadius T) x ∈ prefixGoodSet U j) :
    fderiv ℝ (hardPotential U) x = fderiv ℝ (prefixHardPotential U j) x :=
  (hardPotential_eventuallyEq_prefix hU j hx).fderiv_eq

theorem gradient_hardPotential_eq_prefix_of_good {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (j : Fin T) (x : Point d)
    (hx : softProjection (hardRadius T) x ∈ prefixGoodSet U j) :
    gradient (hardPotential U) x = gradient (prefixHardPotential U j) x := by
  unfold gradient
  rw [fderiv_hardPotential_eq_prefix_of_good hU j x hx]


/-- The prefix-only residual in the manuscript's displayed truncation. -/
def prefixResidual {d T : ℕ} (U : Fin T → Point d) (j k : Fin T) (y : Point d) : ℝ :=
  ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ k)) y‖ ^ 2 -
    ∑ i ∈ Finset.univ.filter (fun i => k < i ∧ i ≤ j),
      carmonOmegaSix (frameCoordinates U y i) * (frameCoordinates U y i) ^ 2

/-- The prefix-only selector in the manuscript's displayed truncation. -/
def prefixSelector {d T : ℕ} (U : Fin T → Point d) (j k : Fin T) (y : Point d) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i => k < i ∧ i ≤ j),
    (1 - carmonOmegaThree (frameCoordinates U y i))

theorem gatedResidual_prefixFrame_eq_prefixResidual {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : k ≤ j) :
    gatedResidual (prefixFrame U j) k y = prefixResidual U j k y := by
  unfold gatedResidual prefixResidual
  rw [frameOrthogonalResidual_prefixFrame_of_le U j k y hk]
  congr 1
  have hs : Finset.univ.filter (fun i : Fin T => k < i ∧ i ≤ j) ⊆
      Finset.univ.filter (k < ·) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.1⟩
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin T => k < i ∧ i ≤ j),
        carmonOmegaSix (frameCoordinates (prefixFrame U j) y i) *
          (frameCoordinates (prefixFrame U j) y i) ^ 2 := by
      symm
      apply Finset.sum_subset hs
      intro i hi hnot
      have hij : ¬ i ≤ j := by
        intro hij
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2, hij⟩)
      rw [frameCoordinates_prefixFrame_of_gt U j i y (lt_of_not_ge hij)]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [frameCoordinates_prefixFrame_of_le U j i y (Finset.mem_filter.mp hi).2.2]

theorem chainSelector_prefixFrame_eq_prefixSelector {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) :
    chainSelector carmonOmegaThree (frameCoordinates (prefixFrame U j) y) k =
      prefixSelector U j k y := by
  unfold chainSelector prefixSelector
  have hs : Finset.univ.filter (fun i : Fin T => k < i ∧ i ≤ j) ⊆
      Finset.univ.filter (k < ·) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.1⟩
  calc
    _ = ∏ i ∈ Finset.univ.filter (fun i : Fin T => k < i ∧ i ≤ j),
        (1 - carmonOmegaThree (frameCoordinates (prefixFrame U j) y i)) := by
      symm
      apply Finset.prod_subset hs
      intro i hi hnot
      have hij : ¬ i ≤ j := by
        intro hij
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2, hij⟩)
      rw [frameCoordinates_prefixFrame_of_gt U j i y (lt_of_not_ge hij),
        carmonOmegaThree_zero (by norm_num : |(0 : ℝ)| ≤ 1 / 4)]
      norm_num
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [frameCoordinates_prefixFrame_of_le U j i y (Finset.mem_filter.mp hi).2.2]

theorem gatedCorrectionTerm_prefixFrame_of_tail {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : j.val + 1 < k.val) :
    gatedCorrectionTerm (prefixFrame U j) k y = 0 := by
  have hzero : k.val ≠ 0 := by omega
  have hp : chainPredecessor (frameCoordinates (prefixFrame U j) y) k = 0 := by
    simp only [chainPredecessor, dif_neg hzero]
    exact frameCoordinates_prefixFrame_of_gt U j _ y (by change j.val < k.val - 1; omega)
  simp [gatedCorrectionTerm, chainGateTerm, chainCorrection, frontierCorrection, hp,
    carmonPsi_zero_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]

theorem gatedCorrectionTerm_prefixFrame_at_successor {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : k.val = j.val + 1) :
    gatedCorrectionTerm (prefixFrame U j) k y =
      (1 - carmonChi (‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) y‖ ^ 2)) *
        (carmonPsi (frameCoordinates U y j) + carmonPsi (-frameCoordinates U y j)) := by
  have hkj : j < k := by change j.val < k.val; omega
  have hp : chainPredecessor (frameCoordinates (prefixFrame U j) y) k = frameCoordinates U y j := by
    rw [chainPredecessor_at_successor _ j k hk, frameCoordinates_prefixFrame_of_le U j j y le_rfl]
  have hsel : chainSelector carmonOmegaThree (frameCoordinates (prefixFrame U j) y) k = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hji := hkj.trans (Finset.mem_filter.mp hi).2
    rw [frameCoordinates_prefixFrame_of_gt U j i y hji,
      carmonOmegaThree_zero (by norm_num : |(0 : ℝ)| ≤ 1 / 4)]
    norm_num
  unfold gatedCorrectionTerm chainGateTerm chainCorrection
  rw [hp, frameCoordinates_prefixFrame_of_gt U j k y hkj,
    gatedResidual_prefixFrame_successor U j k y hk, hsel]
  simp [frontierCorrection, carmonOmega_zero (by norm_num : |(0 : ℝ)| ≤ 1 / 8)]

/-- Exact equality with the displayed `F^(j+1)`, including its boundary correction.
This is a global identity for the truncated function and needs no good-region assumption. -/
theorem hardPreprojectionPotential_prefix_expansion {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) (hk : k.val = j.val + 1) :
    hardPreprojectionPotential (prefixFrame U j) y =
      carmonChain (fun i => if i ≤ j then frameCoordinates U y i else 0) +
      (∑ i ∈ Finset.univ.filter (· ≤ j),
        (1 - carmonChi (prefixResidual U j i y)) *
          chainCorrection carmonPsi carmonPhi carmonOmega 1 (frameCoordinates U y) i *
          prefixSelector U j i y) +
      (1 - carmonChi (‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) y‖ ^ 2)) *
        (carmonPsi (frameCoordinates U y j) + carmonPsi (-frameCoordinates U y j)) := by
  have hz : frameCoordinates (prefixFrame U j) y =
      (fun i => if i ≤ j then frameCoordinates U y i else 0) := by
    funext i
    by_cases hi : i ≤ j
    · simp [hi, frameCoordinates_prefixFrame_of_le U j i y hi]
    · simp [hi, frameCoordinates_prefixFrame_of_gt U j i y (lt_of_not_ge hi)]
  have hsum : gatedCorrection (prefixFrame U j) y =
      (∑ i ∈ Finset.univ.filter (· ≤ j), gatedCorrectionTerm (prefixFrame U j) i y) +
        gatedCorrectionTerm (prefixFrame U j) k y := by
    rw [gatedCorrection_eq_sum_terms]
    dsimp only
    have heq : (∑ i : Fin T, gatedCorrectionTerm (prefixFrame U j) i y) =
        ∑ i ∈ Finset.univ.filter (· ≤ k), gatedCorrectionTerm (prefixFrame U j) i y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i hi hnot
      have hki : k < i := by simpa using hnot
      apply gatedCorrectionTerm_prefixFrame_of_tail U j i y
      change k.val < i.val at hki
      omega
    rw [heq, prefix_filter_successor j k hk]
    have hnot : k ∉ Finset.univ.filter (· ≤ j) := by
      have hkj : j < k := by change j.val < k.val; omega
      simp [not_le.mpr hkj]
    rw [Finset.sum_insert hnot, add_comm]
  have hterm (i : Fin T) (hi : i ≤ j) : gatedCorrectionTerm (prefixFrame U j) i y =
      (1 - carmonChi (prefixResidual U j i y)) *
        chainCorrection carmonPsi carmonPhi carmonOmega 1 (frameCoordinates U y) i *
        prefixSelector U j i y := by
    unfold gatedCorrectionTerm chainGateTerm chainCorrection
    rw [gatedResidual_prefixFrame_eq_prefixResidual U j i y hi,
      chainSelector_prefixFrame_eq_prefixSelector U j i y,
      chainPredecessor_prefixFrame U j i y (by omega),
      frameCoordinates_prefixFrame_of_le U j i y hi]
    ring
  unfold hardPreprojectionPotential
  rw [hz, hsum, gatedCorrectionTerm_prefixFrame_at_successor U j k y hk]
  have hterms : (∑ i ∈ Finset.univ.filter (· ≤ j), gatedCorrectionTerm (prefixFrame U j) i y) =
      ∑ i ∈ Finset.univ.filter (· ≤ j),
        (1 - carmonChi (prefixResidual U j i y)) *
          chainCorrection carmonPsi carmonPhi carmonOmega 1 (frameCoordinates U y) i *
          prefixSelector U j i y :=
    Finset.sum_congr rfl (fun i hi => hterm i (Finset.mem_filter.mp hi).2)
  rw [hterms]
  ring

/-- The terminal truncation is exactly the full objective, as in the manuscript convention. -/
theorem prefixHardPotential_eq_full_at_last {d T : ℕ} (U : Fin T → Point d)
    (j : Fin T) (hj : j.val + 1 = T) : prefixHardPotential U j = hardPotential U := by
  have hframe : prefixFrame U j = U := by
    funext i
    have hi : i ≤ j := by have h := i.isLt; change i.val ≤ j.val; omega
    simp [prefixFrame, hi]
  rw [prefixHardPotential, hframe]


/-- Outside the accident set, the next unrevealed coordinate is too small
for the next cap. This is the deterministic post-reveal step in Lemma 7(i). -/
theorem mem_prefixGoodSet_successor_of_not_accident {d T : ℕ}
    (U : Fin T → Point d) (j k : Fin T) (y : Point d) (hk : k.val = j.val + 1)
    (hno : y ∉ prefixAccidentSet U j) : y ∈ prefixGoodSet U k := by
  have hf (i : Fin T) (hi : j < i) : |frameCoordinates U y i| < (1 / 32 : ℝ) := by
    by_contra h
    exact hno ⟨i, hi, le_of_not_gt h⟩
  have hjk : j < k := by change j.val < k.val; omega
  apply (mem_prefixGoodSet_iff U k y).mpr
  refine ⟨fun i hi => hf i (hjk.trans hi), Or.inl ?_⟩
  linarith [hf k hjk]

/-- Exact response-mean identity for either branch of the one-step reveal rule.
The query `x` is arbitrary, including arbitrarily distant points. -/
theorem gradient_hardPotential_eq_prefix_after_reveal {d T : ℕ}
    {U : Fin T → Point d} (hU : Orthonormal ℝ U) (j k : Fin T) (hk : k.val = j.val + 1)
    (x : Point d) (hno : softProjection (hardRadius T) x ∉ prefixAccidentSet U j) :
    gradient (hardPotential U) x =
      if softProjection (hardRadius T) x ∈ prefixCapSet U j then
        gradient (prefixHardPotential U k) x
      else gradient (prefixHardPotential U j) x := by
  classical
  by_cases hcap : softProjection (hardRadius T) x ∈ prefixCapSet U j
  · rw [if_pos hcap]
    exact gradient_hardPotential_eq_prefix_of_good hU k x
      (mem_prefixGoodSet_successor_of_not_accident U j k _ hk hno)
  · rw [if_neg hcap]
    apply gradient_hardPotential_eq_prefix_of_good hU j x
    change ¬ (softProjection (hardRadius T) x ∈ prefixAccidentSet U j ∨
      softProjection (hardRadius T) x ∈ prefixCapSet U j)
    exact not_or.mpr ⟨hno, hcap⟩

end

end HeavyTailedNoise
