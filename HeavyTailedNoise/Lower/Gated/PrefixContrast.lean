import HeavyTailedNoise.Lower.Gated.PrefixLocality
import HeavyTailedNoise.Lower.Gated.HardProjectionOperatorBounds

/-!
Uniform contrast of the exact truncated responses. Zero suffix columns are
handled by an explicit Euclidean isometric lift, never by treating the masked
frame as orthonormal. The lift is an auxiliary norm certificate only.
-/

namespace HeavyTailedNoise

open scoped BigOperators Topology Classical

noncomputable section

def prefixLiftLeftBasis (d T : ℕ) (i : Fin d) : Point (d + T) :=
  EuclideanSpace.single (Fin.castAdd T i) 1

def prefixLiftRightBasis (d T : ℕ) (i : Fin T) : Point (d + T) :=
  EuclideanSpace.single (Fin.natAdd d i) 1

theorem orthonormal_prefixLiftLeftBasis (d T : ℕ) : Orthonormal ℝ (prefixLiftLeftBasis d T) := by
  apply (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (d + T))).comp (Fin.castAdd T)
  intro i j hij
  exact Fin.ext (by simpa using congrArg Fin.val hij)

theorem orthonormal_prefixLiftRightBasis (d T : ℕ) : Orthonormal ℝ (prefixLiftRightBasis d T) := by
  apply (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (d + T))).comp (Fin.natAdd d)
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  simp only [Fin.val_natAdd] at h
  omega

theorem inner_prefixLiftLeft_right (d T : ℕ) (i : Fin d) (j : Fin T) :
    inner ℝ (prefixLiftLeftBasis d T i) (prefixLiftRightBasis d T j) = 0 := by
  apply (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (d + T))).inner_eq_zero
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

/-- Euclidean insertion into the first `d` coordinates, as a continuous linear map. -/
def prefixLiftEmbedding (d T : ℕ) : Point d →L[ℝ] Point (d + T) :=
  ∑ i : Fin d, (innerSL ℝ (EuclideanSpace.single i 1)).smulRight (prefixLiftLeftBasis d T i)

theorem prefixLiftEmbedding_apply (d T : ℕ) (x : Point d) :
    prefixLiftEmbedding d T x = ∑ i : Fin d, x i • prefixLiftLeftBasis d T i := by
  simp [prefixLiftEmbedding, EuclideanSpace.inner_single_left]

theorem inner_prefixLiftEmbedding (d T : ℕ) (x y : Point d) :
    inner ℝ (prefixLiftEmbedding d T x) (prefixLiftEmbedding d T y) = inner ℝ x y := by
  rw [prefixLiftEmbedding_apply, prefixLiftEmbedding_apply]
  have h := (orthonormal_prefixLiftLeftBasis d T).inner_sum (fun i => x i) (fun i => y i) Finset.univ
  simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using h

theorem norm_prefixLiftEmbedding (d T : ℕ) (x : Point d) : ‖prefixLiftEmbedding d T x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_prefixLiftEmbedding d T x x

theorem norm_prefixLiftEmbedding_le_one (d T : ℕ) : ‖prefixLiftEmbedding d T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp [norm_prefixLiftEmbedding]

theorem inner_prefixLiftEmbedding_right (d T : ℕ) (x : Point d) (i : Fin T) :
    inner ℝ (prefixLiftEmbedding d T x) (prefixLiftRightBasis d T i) = 0 := by
  rw [prefixLiftEmbedding_apply, sum_inner]
  simp [real_inner_smul_left, inner_prefixLiftLeft_right]

/-- Complete the masked frame using orthogonal coordinates in an auxiliary space. -/
def liftedPrefixFrame {d T : ℕ} (U : Fin T → Point d) (j i : Fin T) : Point (d + T) :=
  if i ≤ j then prefixLiftEmbedding d T (U i) else prefixLiftRightBasis d T i

theorem orthonormal_liftedPrefixFrame {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (j : Fin T) : Orthonormal ℝ (liftedPrefixFrame U j) := by
  rw [orthonormal_iff_ite]
  intro i k
  by_cases hi : i ≤ j <;> by_cases hk : k ≤ j
  · simpa [liftedPrefixFrame, hi, hk, inner_prefixLiftEmbedding] using
      (orthonormal_iff_ite.mp hU i k)
  · have hik : i ≠ k := by intro h; subst k; exact hk hi
    simp [liftedPrefixFrame, hi, hk, inner_prefixLiftEmbedding_right, hik]
  · have hik : i ≠ k := by intro h; subst k; exact hi hk
    rw [real_inner_comm]
    simp [liftedPrefixFrame, hi, hk, inner_prefixLiftEmbedding_right, hik, Ne.symm hik]
  · simpa [liftedPrefixFrame, hi, hk] using
      (orthonormal_iff_ite.mp (orthonormal_prefixLiftRightBasis d T) i k)

theorem frameCoordinates_liftedPrefixFrame {d T : ℕ} (U : Fin T → Point d)
    (j : Fin T) (y : Point d) :
    frameCoordinates (liftedPrefixFrame U j) (prefixLiftEmbedding d T y) =
      frameCoordinates (prefixFrame U j) y := by
  funext i
  by_cases hi : i ≤ j
  · simp [frameCoordinates, liftedPrefixFrame, prefixFrame, hi, inner_prefixLiftEmbedding]
  · have h : inner ℝ (prefixLiftRightBasis d T i) (prefixLiftEmbedding d T y) = 0 := by
      rw [real_inner_comm]
      exact inner_prefixLiftEmbedding_right d T y i
    simp [frameCoordinates, liftedPrefixFrame, prefixFrame, hi, h]

theorem frameOrthogonalResidual_liftedPrefixFrame {d T : ℕ} (U : Fin T → Point d)
    (j : Fin T) (s : Finset (Fin T)) (y : Point d) :
    frameOrthogonalResidual (liftedPrefixFrame U j) s (prefixLiftEmbedding d T y) =
      prefixLiftEmbedding d T (frameOrthogonalResidual (prefixFrame U j) s y) := by
  unfold frameOrthogonalResidual
  rw [frameCoordinates_liftedPrefixFrame, map_sub, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  by_cases hij : i ≤ j
  · simp [liftedPrefixFrame, prefixFrame, hij]
  · rw [frameCoordinates_prefixFrame_of_gt U j i y (lt_of_not_ge hij)]
    simp

theorem gatedResidual_liftedPrefixFrame {d T : ℕ} (U : Fin T → Point d)
    (j k : Fin T) (y : Point d) :
    gatedResidual (liftedPrefixFrame U j) k (prefixLiftEmbedding d T y) =
      gatedResidual (prefixFrame U j) k y := by
  unfold gatedResidual
  rw [frameCoordinates_liftedPrefixFrame, frameOrthogonalResidual_liftedPrefixFrame,
    norm_prefixLiftEmbedding]

theorem gatedCorrection_liftedPrefixFrame {d T : ℕ} (U : Fin T → Point d)
    (j : Fin T) (y : Point d) :
    gatedCorrection (liftedPrefixFrame U j) (prefixLiftEmbedding d T y) =
      gatedCorrection (prefixFrame U j) y := by
  unfold gatedCorrection
  rw [frameCoordinates_liftedPrefixFrame]
  apply Finset.sum_congr rfl
  intro k hk
  rw [gatedResidual_liftedPrefixFrame]

/-- The actual truncated correction inherits `100` by isometric pullback
from an orthonormal lifted frame; the masked frame is not assumed orthonormal. -/
theorem norm_fderiv_gatedCorrection_prefixFrame_le_100 {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (j : Fin T) (y : Point d) :
    ‖fderiv ℝ (gatedCorrection (prefixFrame U j)) y‖ ≤ 100 := by
  let L := prefixLiftEmbedding d T
  let V := liftedPrefixFrame U j
  have heq : gatedCorrection (prefixFrame U j) = (fun x => gatedCorrection V (L x)) := by
    funext x
    exact (gatedCorrection_liftedPrefixFrame U j x).symm
  have hd := ((contDiff_gatedCorrection_two V).differentiable (by norm_num) (L y)).hasFDerivAt.comp y
    L.hasFDerivAt
  rw [heq]
  change ‖fderiv ℝ (gatedCorrection V ∘ L) y‖ ≤ 100
  rw [hd.fderiv]
  have hV : Orthonormal ℝ V := orthonormal_liftedPrefixFrame hU j
  have hq : ‖fderiv ℝ (gatedCorrection V) (L y)‖ ≤ 100 := by
    simpa [gradient] using norm_gradient_gatedCorrection_le_100_of_orthonormal hV (L y)
  calc
    _ ≤ ‖fderiv ℝ (gatedCorrection V) (L y)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (100 : ℝ) * 1 := mul_le_mul hq (norm_prefixLiftEmbedding_le_one d T) (norm_nonneg _) (by norm_num)
    _ = 100 := by norm_num


theorem chainPredecessorVector_norm_le_of_columns {d T : ℕ} (U : Fin T → Point d)
    (hU : ∀ i, ‖U i‖ ≤ 1) (k : Fin T) : ‖chainPredecessorVector U k‖ ≤ 1 := by
  by_cases hk : k.val = 0
  · simp [chainPredecessorVector, hk]
  · simpa [chainPredecessorVector, hk] using hU ⟨k.val - 1, by omega⟩

theorem norm_fderiv_chainLink_pullback_le_23 {d T : ℕ} (U : Fin T → Point d)
    (hU : ∀ i, ‖U i‖ ≤ 1) (k : Fin T) (y : Point d) :
    ‖fderiv ℝ (fun x : Point d => carmonChainLink (chainPredecessor (frameCoordinates U x) k)
      (frameCoordinates U x k)) y‖ ≤ 23 := by
  have hd := hasFDerivAt_carmonChainLink_comp (hasFDerivAt_chainPredecessor_pullback U k y)
    (innerSL ℝ (U k)).hasFDerivAt
  rw [show fderiv ℝ (fun x : Point d => carmonChainLink
    (chainPredecessor (frameCoordinates U x) k) (frameCoordinates U x k)) y = _ from hd.fderiv]
  let a := chainPredecessor (frameCoordinates U y) k
  let b := frameCoordinates U y k
  have hp : ‖chainLinkPrev a b • innerSL ℝ (chainPredecessorVector U k)‖ ≤ (46161 / 2500 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
    calc
      _ ≤ (46161 / 2500 : ℝ) * 1 := mul_le_mul (abs_chainLinkPrev_le a b)
        (chainPredecessorVector_norm_le_of_columns U hU k) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hc : ‖chainLinkCurrent a b • innerSL ℝ (U k)‖ ≤ (89727 / 20000 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, innerSL_apply_norm]
    calc
      _ ≤ (89727 / 20000 : ℝ) * 1 := mul_le_mul (abs_chainLinkCurrent_le a b)
        (hU k) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ‖chainLinkPrev a b • innerSL ℝ (chainPredecessorVector U k)‖ +
        ‖chainLinkCurrent a b • innerSL ℝ (U k)‖ := ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ (46161 / 2500 : ℝ) + 89727 / 20000 := add_le_add hp hc
    _ ≤ 23 := by norm_num

theorem prefixFrame_norm_le_one {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (j i : Fin T) : ‖prefixFrame U j i‖ ≤ 1 := by
  by_cases hi : i ≤ j <;> simp [prefixFrame, hi, hU.norm_eq_one]

theorem prefixFrame_eq_away_from_last {d T : ℕ} {U V : Fin T → Point d} (j : Fin T)
    (hpre : ∀ i, i < j → U i = V i) (i : Fin T) (hne : i ≠ j) :
    prefixFrame U j i = prefixFrame V j i := by
  by_cases hi : i ≤ j
  · have hij : i < j := by
      have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
      change i.val ≤ j.val at hi
      change i.val < j.val
      omega
    simp [prefixFrame, hi, hpre i hij]
  · simp [prefixFrame, hi]

theorem chainLink_prefixFrame_eq_of_away {d T : ℕ} {U V : Fin T → Point d} (j k : Fin T)
    (hpre : ∀ i, i < j → U i = V i) (hkj : k ≠ j) (hnext : k.val ≠ j.val + 1) :
    (fun x : Point d => carmonChainLink
      (chainPredecessor (frameCoordinates (prefixFrame U j) x) k)
      (frameCoordinates (prefixFrame U j) x k)) =
    (fun x : Point d => carmonChainLink
      (chainPredecessor (frameCoordinates (prefixFrame V j) x) k)
      (frameCoordinates (prefixFrame V j) x k)) := by
  funext x
  have hc : frameCoordinates (prefixFrame U j) x k = frameCoordinates (prefixFrame V j) x k := by
    unfold frameCoordinates
    rw [prefixFrame_eq_away_from_last j hpre k hkj]
  have hp : chainPredecessor (frameCoordinates (prefixFrame U j) x) k =
      chainPredecessor (frameCoordinates (prefixFrame V j) x) k := by
    by_cases hzero : k.val = 0
    · simp [chainPredecessor, hzero]
    · simp only [chainPredecessor, dif_neg hzero]
      have hne : (⟨k.val - 1, by omega⟩ : Fin T) ≠ j := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_mk] at hv
        omega
      unfold frameCoordinates
      rw [prefixFrame_eq_away_from_last j hpre _ hne]
  rw [hp, hc]

def prefixAffectedLinks {T : ℕ} (j : Fin T) : Finset (Fin T) :=
  Finset.univ.filter (fun k => k = j ∨ k.val = j.val + 1)

theorem card_prefixAffectedLinks_le_two {T : ℕ} (j : Fin T) : (prefixAffectedLinks j).card ≤ 2 := by
  by_cases hnext : j.val + 1 < T
  · let k : Fin T := ⟨j.val + 1, hnext⟩
    have hs : prefixAffectedLinks j ⊆ {j, k} := by
      intro i hi
      rcases (Finset.mem_filter.mp hi).2 with h | h
      · simp [h]
      · have hik : i = k := Fin.ext h
        simp [hik]
    exact (Finset.card_le_card hs).trans Finset.card_le_two
  · have hs : prefixAffectedLinks j ⊆ {j} := by
      intro i hi
      rcases (Finset.mem_filter.mp hi).2 with h | h
      · simp [h]
      · have hiT := i.isLt
        omega
    exact (Finset.card_le_card hs).trans (by simp)

theorem fderiv_carmonChain_pullback_eq_link_sum {d T : ℕ} (U : Fin T → Point d) (y : Point d) :
    fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates U x)) y =
      ∑ k : Fin T, fderiv ℝ (fun x : Point d => carmonChainLink
        (chainPredecessor (frameCoordinates U x) k) (frameCoordinates U x k)) y := by
  have heq : (fun x : Point d => carmonChain (frameCoordinates U x)) =
      (fun x => ∑ k, carmonChainLink (chainPredecessor (frameCoordinates U x) k)
        (frameCoordinates U x k)) := funext fun x => carmonChain_eq_sum_links _
  rw [heq]
  apply fderiv_fun_sum
  intro k hk
  exact (hasFDerivAt_carmonChainLink_comp (hasFDerivAt_chainPredecessor_pullback U k y)
    (innerSL ℝ (U k)).hasFDerivAt).differentiableAt

/-- Only the last revealed link and its constant-coordinate successor can change. -/
theorem norm_fderiv_prefix_chain_sub_le_92 {d T : ℕ} {U V : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (j : Fin T)
    (hpre : ∀ i, i < j → U i = V i) (y : Point d) :
    ‖fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates (prefixFrame U j) x)) y -
      fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates (prefixFrame V j) x)) y‖ ≤ 92 := by
  let D (W : Fin T → Point d) (k : Fin T) := fderiv ℝ (fun x : Point d => carmonChainLink
    (chainPredecessor (frameCoordinates (prefixFrame W j) x) k)
    (frameCoordinates (prefixFrame W j) x k)) y
  have heq : (∑ k : Fin T, (D U k - D V k)) = ∑ k ∈ prefixAffectedLinks j, (D U k - D V k) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k hk hnot
    have hne : k ≠ j ∧ k.val ≠ j.val + 1 := by
      simpa [prefixAffectedLinks, not_or] using hnot
    have hf := chainLink_prefixFrame_eq_of_away j k hpre hne.1 hne.2
    dsimp only [D]
    rw [hf, sub_self]
  rw [fderiv_carmonChain_pullback_eq_link_sum, fderiv_carmonChain_pullback_eq_link_sum,
    ← Finset.sum_sub_distrib]
  change ‖∑ k : Fin T, (D U k - D V k)‖ ≤ 92
  rw [heq]
  calc
    _ ≤ ∑ k ∈ prefixAffectedLinks j, ‖D U k - D V k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ prefixAffectedLinks j, (46 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hu := norm_fderiv_chainLink_pullback_le_23 (prefixFrame U j) (prefixFrame_norm_le_one hU j) k y
      have hv := norm_fderiv_chainLink_pullback_le_23 (prefixFrame V j) (prefixFrame_norm_le_one hV j) k y
      change ‖D U k‖ ≤ 23 at hu
      change ‖D V k‖ ≤ 23 at hv
      exact (norm_sub_le _ _).trans (by change ‖D U k‖ + ‖D V k‖ ≤ 46; linarith)
    _ ≤ 92 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : ((prefixAffectedLinks j).card : ℝ) ≤ 2 := by exact_mod_cast card_prefixAffectedLinks_le_two j
      nlinarith

/-- Exact truncated preprojection contrast. The safe budget is `92 + 100 + 100`. -/
theorem norm_fderiv_prefix_preprojection_sub_le_292 {d T : ℕ} {U V : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (j : Fin T)
    (hpre : ∀ i, i < j → U i = V i) (y : Point d) :
    ‖fderiv ℝ (hardPreprojectionPotential (prefixFrame U j)) y -
      fderiv ℝ (hardPreprojectionPotential (prefixFrame V j)) y‖ ≤ 292 := by
  rw [fderiv_hardPreprojectionPotential, fderiv_hardPreprojectionPotential]
  have hq : ‖fderiv ℝ (gatedCorrection (prefixFrame U j)) y -
      fderiv ℝ (gatedCorrection (prefixFrame V j)) y‖ ≤ 200 :=
    (norm_sub_le _ _).trans (by
      have hu := norm_fderiv_gatedCorrection_prefixFrame_le_100 hU j y
      have hv := norm_fderiv_gatedCorrection_prefixFrame_le_100 hV j y
      linarith)
  have heq : (fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates (prefixFrame U j) x)) y +
        fderiv ℝ (gatedCorrection (prefixFrame U j)) y) -
      (fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates (prefixFrame V j) x)) y +
        fderiv ℝ (gatedCorrection (prefixFrame V j)) y) =
      (fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates (prefixFrame U j) x)) y -
        fderiv ℝ (fun x : Point d => carmonChain (frameCoordinates (prefixFrame V j) x)) y) +
      (fderiv ℝ (gatedCorrection (prefixFrame U j)) y -
        fderiv ℝ (gatedCorrection (prefixFrame V j)) y) := by abel
  rw [heq]
  exact (ContinuousLinearMap.opNorm_add_le _ _).trans (by
    have hc := norm_fderiv_prefix_chain_sub_le_92 hU hV j hpre y
    linarith)

theorem fderiv_prefixHardPotential {d T : ℕ} (U : Fin T → Point d) (j : Fin T) (x : Point d) :
    fderiv ℝ (prefixHardPotential U j) x =
      (fderiv ℝ (hardPreprojectionPotential (prefixFrame U j)) (softProjection (hardRadius T) x)).comp
        (fderiv ℝ (softProjection (hardRadius T)) x) +
      fderiv ℝ (fun z : Point d => (1 / 10 : ℝ) * ‖z‖ ^ 2) x := by
  have hT : 0 < T := by have h := j.isLt; omega
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < hardRadius T := by unfold hardRadius; positivity
  have hp := ((contDiff_hardPreprojectionPotential_two (prefixFrame U j)).differentiable
    (by norm_num) (softProjection (hardRadius T) x)).hasFDerivAt.comp x
      ((contDiff_softProjection_two hR).differentiable (by norm_num) x).hasFDerivAt
  have hq : ContDiff ℝ 2 (fun z : Point d => (1 / 10 : ℝ) * ‖z‖ ^ 2) :=
    contDiff_const.mul (contDiff_id.norm_sq ℝ)
  exact (hp.fun_add (hq.differentiable (by norm_num) x).hasFDerivAt).fderiv

/-- The actual ambient response-mean contrast, uniformly over arbitrary queries.
The frames agree on the first `j` vectors and may differ thereafter. -/
theorem norm_gradient_prefixHardPotential_sub_le_300 {d T : ℕ} {U V : Fin T → Point d}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (j : Fin T)
    (hpre : ∀ i, i < j → U i = V i) (x : Point d) :
    ‖gradient (prefixHardPotential U j) x - gradient (prefixHardPotential V j) x‖ ≤ 300 := by
  have hT : 0 < T := by have h := j.isLt; omega
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < hardRadius T := by unfold hardRadius; positivity
  have hn : ‖gradient (prefixHardPotential U j) x - gradient (prefixHardPotential V j) x‖ =
      ‖fderiv ℝ (prefixHardPotential U j) x - fderiv ℝ (prefixHardPotential V j) x‖ := by
    simp [gradient, ← map_sub]
  rw [hn, fderiv_prefixHardPotential, fderiv_prefixHardPotential]
  let A := fderiv ℝ (hardPreprojectionPotential (prefixFrame U j)) (softProjection (hardRadius T) x)
  let B := fderiv ℝ (hardPreprojectionPotential (prefixFrame V j)) (softProjection (hardRadius T) x)
  let L := fderiv ℝ (softProjection (hardRadius T)) x
  have heq : A.comp L + fderiv ℝ (fun z : Point d => (1 / 10 : ℝ) * ‖z‖ ^ 2) x -
      (B.comp L + fderiv ℝ (fun z : Point d => (1 / 10 : ℝ) * ‖z‖ ^ 2) x) = (A - B).comp L := by
    ext v
    simp
  rw [show _ = (A - B).comp L from heq]
  calc
    _ ≤ ‖A - B‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (292 : ℝ) * 1 := mul_le_mul (norm_fderiv_prefix_preprojection_sub_le_292 hU hV j hpre _)
      (norm_fderiv_softProjection_le_one hR x) (norm_nonneg _) (by norm_num)
    _ ≤ 300 := by norm_num

end

end HeavyTailedNoise
