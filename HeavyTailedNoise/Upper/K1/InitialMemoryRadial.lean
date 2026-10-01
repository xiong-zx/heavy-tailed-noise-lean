import HeavyTailedNoise.Upper.K1.InitialMemoryCombined
import HeavyTailedNoise.Upper.K1.KernelShellSupport
import HeavyTailedNoise.Upper.K1.RateArithmetic

/-!
The combined initialization transform is radial. All dyadic shells point in
the response direction, and the retention coefficients lie in `[0,1]` for
the literal schedule. Consequently the norm of the complete same-source
sum is bounded by both the original residual norm and the terminal cutoff.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

private theorem weighted_successive_differences_le
    (J : ℕ) (a b : ℕ → ℝ)
    (ha0 : 0 ≤ a 0) (ha : ∀ j, a j ≤ a (j + 1))
    (hb0 : ∀ j, 0 ≤ b j) (hb1 : ∀ j, b j ≤ 1) :
    0 ≤ ∑ j ∈ Finset.range J, b j * (a (j + 1) - a j) ∧
      (∑ j ∈ Finset.range J, b j * (a (j + 1) - a j)) ≤ a J := by
  have htel (n : ℕ) :
      (∑ j ∈ Finset.range n, (a (j + 1) - a j)) = a n - a 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hb0 j) (sub_nonneg.mpr (ha j))
  · calc
      (∑ j ∈ Finset.range J, b j * (a (j + 1) - a j)) ≤
          ∑ j ∈ Finset.range J, (a (j + 1) - a j) := by
            apply Finset.sum_le_sum
            intro j hj
            have hd : 0 ≤ a (j + 1) - a j := sub_nonneg.mpr (ha j)
            have hproduct := mul_nonneg (sub_nonneg.mpr (hb1 j)) hd
            nlinarith
      _ = a J - a 0 := htel J
      _ ≤ a J := by linarith

/-- The literal schedule's combined same-seed initialization kernel has
no band-count factor. This is the geometry used before the original
heavy-tailed moment is applied. -/
theorem paperSchedule_initialMemoryKernel_norm_le_min
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} (t : ℕ) (z : Point d) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    ‖initialMemoryKernel P t z‖ ≤
      min ‖z‖ (P.tau ⟨P.J, Nat.lt_succ_self P.J⟩) := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  dsimp only
  by_cases hz : z = 0
  · subst z
    simpa [initialMemoryKernel, highBand, upperShell] using
      (P.tau_pos ⟨P.J, Nat.lt_succ_self P.J⟩).le
  have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let a : ℕ → ℝ := fun j => min 1 (paperTau σ ε j / ‖z‖)
  let b : ℕ → ℝ := fun j => (1 - paperAlpha p q κ j) ^ t
  have ha0 : 0 ≤ a 0 := by
    dsimp [a]
    exact le_min (by norm_num)
      (div_nonneg (paperTau_pos hε 0).le hρ.le)
  have ha (j : ℕ) : a j ≤ a (j + 1) := by
    have hτ : paperTau σ ε j ≤ paperTau σ ε (j + 1) := by
      rw [paperTau_succ]
      have hpos := paperTau_pos (σ := σ) hε j
      linarith
    dsimp [a]
    exact min_le_min_left 1 (div_le_div_of_nonneg_right hτ hρ.le)
  have hb0 (j : ℕ) : 0 ≤ b j := by
    dsimp [b]
    exact pow_nonneg (sub_nonneg.mpr (paperAlpha_le_one p q κ j)) t
  have hb1 (j : ℕ) : b j ≤ 1 := by
    dsimp [b]
    have hα := paperAlpha_pos (p := p) (q := q) hκ j
    exact pow_le_one₀ (sub_nonneg.mpr (paperAlpha_le_one p q κ j))
      (by linarith : 1 - paperAlpha p q κ j ≤ 1)
  have hc := weighted_successive_differences_le P.J a b ha0 ha hb0 hb1
  let c : ℝ := ∑ j : Fin P.J,
    b j.val * (a (j.val + 1) - a j.val)
  have hsum :
      (∑ j : Fin P.J,
        b j.val * (a (j.val + 1) - a j.val)) =
      ∑ j ∈ Finset.range P.J, b j * (a (j + 1) - a j) := by
    simpa only using (Fin.sum_univ_eq_sum_range
      (fun j => b j * (a (j + 1) - a j)) P.J)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    rw [hsum]
    exact hc.1
  have hcJ : c ≤ a P.J := by
    dsimp [c]
    rw [hsum]
    exact hc.2
  have hshell (j : Fin P.J) :
      highBand P j z = (a (j.val + 1) - a j.val) • z := by
    have hhi : P.tau j.succ = paperTau σ ε (j.val + 1) := rfl
    have hlo : P.tau j.castSucc = paperTau σ ε j.val := rfl
    rw [highBand, upperShell, upperClip_eq_min_smul (P.tau_pos j.succ),
      upperClip_eq_min_smul (P.tau_pos j.castSucc)]
    rw [hhi, hlo]
    exact (sub_smul _ _ z).symm
  have hrepr : initialMemoryKernel P t z = c • z := by
    unfold initialMemoryKernel c
    simp_rw [hshell, smul_smul]
    exact (Finset.sum_smul ..).symm
  have hnorm : ‖initialMemoryKernel P t z‖ = c * ‖z‖ := by
    rw [hrepr, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  have hleρ : c * ‖z‖ ≤ ‖z‖ := by
    have h1 : a P.J ≤ 1 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right (hcJ.trans h1) hρ.le]
  have hleτ : c * ‖z‖ ≤ P.tau ⟨P.J, Nat.lt_succ_self P.J⟩ := by
    have hdiv : a P.J ≤ paperTau σ ε P.J / ‖z‖ :=
      min_le_right _ _
    have h := mul_le_mul_of_nonneg_right (hcJ.trans hdiv) hρ.le
    have hcancel : paperTau σ ε P.J / ‖z‖ * ‖z‖ =
        paperTau σ ε P.J := div_mul_cancel₀ _ (ne_of_gt hρ)
    change c * ‖z‖ ≤ paperTau σ ε P.J
    rwa [hcancel] at h
  rw [hnorm]
  exact le_min hleρ hleτ

/-- Pointwise interpolation for the entire correlated high-band initial
sample. It is valid at zero residual and at `p=2`. -/
theorem paperSchedule_initialMemoryKernel_sq_le_residual_p
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p ∧ p ≤ 2)
    (hε : 0 < ε) (hch : 0 < ch) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} (t : ℕ) (z : Point d) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    ‖initialMemoryKernel P t z‖ ^ 2 ≤
      (P.tau ⟨P.J, Nat.lt_succ_self P.J⟩) ^ (2 - p) * ‖z‖ ^ p := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  let a : ℝ := ‖initialMemoryKernel P t z‖
  let b : ℝ := ‖z‖
  let M : ℝ := P.tau ⟨P.J, Nat.lt_succ_self P.J⟩
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hM0 : 0 ≤ M := (P.tau_pos _).le
  have hap : 0 ≤ p := by linarith [hp.1]
  have h2p : 0 ≤ 2 - p := by linarith [hp.2]
  have hbound := paperSchedule_initialMemoryKernel_norm_le_min
    p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hκ hCb hCI t z
  have hab : a ≤ b := hbound.trans (min_le_left _ _)
  have haM : a ≤ M := hbound.trans (min_le_right _ _)
  have hpow1 : a ^ p ≤ b ^ p := Real.rpow_le_rpow ha0 hab hap
  have hpow2 : a ^ (2 - p) ≤ M ^ (2 - p) :=
    Real.rpow_le_rpow ha0 haM h2p
  have hmul : a ^ p * a ^ (2 - p) ≤ b ^ p * M ^ (2 - p) :=
    mul_le_mul hpow1 hpow2 (Real.rpow_nonneg ha0 _)
      (Real.rpow_nonneg hb0 _)
  have hidentity : a ^ 2 = a ^ p * a ^ (2 - p) := by
    calc
      a ^ 2 = a ^ (2 : ℝ) := by simp
      _ = a ^ (p + (2 - p)) := by congr 1; ring
      _ = a ^ p * a ^ (2 - p) :=
        Real.rpow_add' ha0 (by norm_num : p + (2 - p) ≠ 0)
  dsimp only [a, b, M] at hmul hidentity ⊢
  rw [hidentity]
  simpa only [mul_comm] using hmul

end

end HeavyTailedNoise.UpperK1
