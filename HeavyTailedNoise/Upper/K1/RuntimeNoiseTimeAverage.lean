import HeavyTailedNoise.Upper.K1.RuntimeKernelNoise
import HeavyTailedNoise.Upper.K1.KernelPhiResidualMoment
import HeavyTailedNoise.Upper.K1.ResidualPhysicalMoment
import HeavyTailedNoise.Upper.K1.RuntimeNoisePhysicalCoefficient
import HeavyTailedNoise.Upper.K1.RuntimeNoisePrivateIndependence

/-!
Finite triangular time accounting for the complete shared-source runtime
kernel.  A source at batch `u` contributes lag `k` only at output time
`u+k+1`; hence each source-lag pair is counted at most once.  The kernel
square is formed before this accounting, preserving every within-seed
cross-scale term.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The triangular output-time/source sum is exactly the triangular
source/lag sum. -/
theorem triangular_runtime_lag_sum_eq (T : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ t ∈ Finset.range T,
      ∑ u ∈ Finset.range (t + 1), f u (t - u)) =
    ∑ u ∈ Finset.range T,
      ∑ k ∈ Finset.range (T - u), f u k := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      have hright :
          (∑ u ∈ Finset.range (T + 1),
            ∑ k ∈ Finset.range (T + 1 - u), f u k) =
          (∑ u ∈ Finset.range T,
            ∑ k ∈ Finset.range (T - u), f u k) +
            ∑ u ∈ Finset.range (T + 1), f u (T - u) := by
        calc
          (∑ u ∈ Finset.range (T + 1),
              ∑ k ∈ Finset.range (T + 1 - u), f u k) =
              (∑ u ∈ Finset.range T,
                ((∑ k ∈ Finset.range (T - u), f u k) +
                  f u (T - u))) + f T 0 := by
                    rw [Finset.sum_range_succ]
                    congr 1
                    · apply Finset.sum_congr rfl
                      intro u hu
                      have hindex : T + 1 - u = (T - u) + 1 := by
                        have := Finset.mem_range.mp hu
                        omega
                      rw [hindex, Finset.sum_range_succ]
                    · simp
          _ = (∑ u ∈ Finset.range T,
                ∑ k ∈ Finset.range (T - u), f u k) +
              ((∑ u ∈ Finset.range T, f u (T - u)) + f T 0) := by
                rw [Finset.sum_add_distrib]
                ring
          _ = (∑ u ∈ Finset.range T,
                ∑ k ∈ Finset.range (T - u), f u k) +
              ∑ u ∈ Finset.range (T + 1), f u (T - u) := by
                rw [Finset.sum_range_succ]
                simp
      exact hright.symm

/-- Extending each source's available lag range to the whole horizon only
adds nonnegative squared-kernel terms. -/
theorem triangular_runtime_lag_sum_le_rect
    (T : ℕ) (f : ℕ → ℕ → ℝ) (hf : ∀ u k, 0 ≤ f u k) :
    (∑ t ∈ Finset.range T,
      ∑ u ∈ Finset.range (t + 1), f u (t - u)) ≤
    ∑ u ∈ Finset.range T, ∑ k ∈ Finset.range T, f u k := by
  rw [triangular_runtime_lag_sum_eq]
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.sub_le T u)
  · intro k hk _
    exact hf u k

/-- One actual batch's complete-kernel sum is controlled by the original
oracle moment and the physical tracker bound. -/
theorem Admissible.paperSchedule_actualKernelSource_sq_sum_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    ∀ (u : Fin P.T) (T : ℕ),
      (∑ k ∈ Finset.range T,
        ∫ H : BatchHistory P d u,
          ∫ ξ : Seed,
            ‖kernelPhi P k
              (I.oracle.response (batchDecision P u H) ξ -
                batchCenter P u H)‖ ^ 2
            ∂I.oracle.law ∂batchPastHistoryLaw P I.oracle u) ≤
      physicalKernelNoiseConstant p q κ *
        (paperNu σ ε) ^ (2 - p) *
        (paperU p σ ε Ctail) ^ (paperEplus p q) *
        (2 * (1 + physicalResidualTrackerConstant p) *
          (paperNu σ ε) ^ p) := by
  dsimp only
  intro u T
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (batchPastHistoryLaw P I.oracle u) := by
    unfold batchPastHistoryLaw
    infer_instance
  let μ := (batchPastHistoryLaw P I.oracle u).prod I.oracle.law
  let R : BatchHistory P d u × Seed → ℝ := fun z =>
    ‖I.oracle.response (batchDecision P u z.1) z.2 -
      batchCenter P u z.1‖ ^ p
  let F (k : ℕ) : BatchHistory P d u × Seed → ℝ := fun z =>
    ‖kernelPhi P k
      (I.oracle.response (batchDecision P u z.1) z.2 -
        batchCenter P u z.1)‖ ^ 2
  let C := physicalKernelNoiseConstant p q κ *
    (paperNu σ ε) ^ (2 - p) *
    (paperU p σ ε Ctail) ^ (paperEplus p q)
  have hR := Admissible.paperSchedule_actualResidual_p_integrable_bound
    I ε Ctail κ Cb CI hε hCb hCI u
  change Integrable
      (fun z : BatchHistory P d u × Seed => actualResidualPower P I u z) μ ∧
    (∫ z, actualResidualPower P I u z ∂μ) ≤
      2 * (1 + physicalResidualTrackerConstant p) *
        (paperNu σ ε) ^ p at hR
  simp only [actualResidualPower] at hR
  change Integrable R μ ∧ (∫ z, R z ∂μ) ≤
    2 * (1 + physicalResidualTrackerConstant p) *
      (paperNu σ ε) ^ p at hR
  have hFint (k : ℕ) : Integrable (F k) μ :=
    kernelSourceMoment_joint_integrable P I.oracle u k
  have hC : 0 ≤ C := by
    dsimp [C, physicalKernelNoiseConstant]
    have hν : 0 < paperNu σ ε := paperNu_pos hε
    have hU : 0 < paperU p σ ε Ctail := paperU_pos hε
    positivity
  have hpoint (z : BatchHistory P d u × Seed) :
      (∑ k ∈ Finset.range T, F k z) ≤ C * R z := by
    change (∑ k ∈ Finset.range T,
      ‖kernelPhi P k
        (I.oracle.response (batchDecision P u z.1) z.2 -
          batchCenter P u z.1)‖ ^ 2) ≤
      C * ‖I.oracle.response (batchDecision P u z.1) z.2 -
          batchCenter P u z.1‖ ^ p
    exact paperSchedule_kernelPhi_sq_sum_le_physical
      p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      I.p_range.1 I.p_range.2 I.q_range hε
      (by norm_num) hκ hCb hCI _
  have hswap :
      (∑ k ∈ Finset.range T,
        ∫ H : BatchHistory P d u,
          ∫ ξ : Seed, F k (H, ξ) ∂I.oracle.law
          ∂batchPastHistoryLaw P I.oracle u) =
      ∫ z : BatchHistory P d u × Seed,
        ∑ k ∈ Finset.range T, F k z ∂μ := by
    calc
      _ = ∑ k ∈ Finset.range T, ∫ z, F k z ∂μ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (integral_prod _ (hFint k)).symm
      _ = _ := by
        rw [integral_finsetSum]
        intro k hk
        exact hFint k
  rw [hswap]
  calc
    (∫ z, ∑ k ∈ Finset.range T, F k z ∂μ) ≤
        ∫ z, C * R z ∂μ := by
          apply integral_mono
          · apply integrable_finsetSum
            intro k hk
            exact hFint k
          · exact hR.1.const_mul C
          · exact hpoint
    _ = C * ∫ z, R z ∂μ := by rw [integral_const_mul]
    _ ≤ C * (2 * (1 + physicalResidualTrackerConstant p) *
        (paperNu σ ε) ^ p) :=
      mul_le_mul_of_nonneg_left hR.2 hC

/-- Generic finite-time estimate: a uniform complete source-lag square bound
controls the average runtime-kernel square with exactly one `1/n` factor.
Each source-lag pair enters one output time, and cross-time terms have already
vanished in `runtimeKernelNoise_sq_le_sources`. -/
theorem runtimeKernelNoise_sq_average_le_of_source_bound
    {q : ℝ} (P : Schedule q)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (B : ℝ)
    (hsource : ∀ u : Fin P.T,
      (∑ k ∈ Finset.range P.T,
        ∫ H : BatchHistory P d u,
          ∫ ξ : Seed,
            ‖kernelPhi P k
              (O.response (batchDecision P u H) ξ - batchCenter P u H)‖ ^ 2
            ∂O.law ∂batchPastHistoryLaw P O u) ≤ B) :
    (P.T : ℝ)⁻¹ *
      (∑ t : Fin P.T,
        ∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖runtimeKernelNoise P O (t.val + 1)
            (Nat.succ_le_iff.mpr t.isLt) z‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw O (responseCount P)))) ≤
      (P.n : ℝ)⁻¹ * B := by
  let f (u k : ℕ) : ℝ :=
    if hu : u < P.T then
      ∫ H : BatchHistory P d ⟨u, hu⟩,
        ∫ ξ : Seed,
          ‖kernelPhi P k
            (O.response (batchDecision P ⟨u, hu⟩ H) ξ -
              batchCenter P ⟨u, hu⟩ H)‖ ^ 2
        ∂O.law ∂batchPastHistoryLaw P O ⟨u, hu⟩
    else 0
  let V (t : ℕ) : ℝ :=
    if ht : t + 1 ≤ P.T then
      ∫ z : Fin P.T × (Fin (responseCount P) → Seed),
        ‖runtimeKernelNoise P O (t + 1) ht z‖ ^ 2
        ∂((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw O (responseCount P)))
    else 0
  have hf_nonneg (u k : ℕ) : 0 ≤ f u k := by
    dsimp [f]
    split
    · apply integral_nonneg
      intro H
      exact integral_nonneg (fun ξ => sq_nonneg _)
    · exact le_rfl
  have hindex (u : Fin P.T) (k : ℕ) :
      f u.val k =
        ∫ H : BatchHistory P d u,
          ∫ ξ : Seed,
            ‖kernelPhi P k
              (O.response (batchDecision P u H) ξ -
                batchCenter P u H)‖ ^ 2
            ∂O.law ∂batchPastHistoryLaw P O u := by
    dsimp [f]
    simp only [dif_pos u.isLt]
  have hV (t : Fin P.T) :
      V t.val =
      ∫ z : Fin P.T × (Fin (responseCount P) → Seed),
        ‖runtimeKernelNoise P O (t.val + 1)
          (Nat.succ_le_iff.mpr t.isLt) z‖ ^ 2
        ∂((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw O (responseCount P))) := by
    dsimp [V]
    rw [dif_pos (Nat.succ_le_iff.mpr t.isLt)]
  have hstep (t : ℕ) (ht : t < P.T) :
      V t ≤ (P.n : ℝ)⁻¹ *
        ∑ u ∈ Finset.range (t + 1), f u (t - u) := by
    have ht' : t + 1 ≤ P.T := Nat.succ_le_iff.mpr ht
    have hbase := runtimeKernelNoise_sq_le_sources
      P O (t + 1) ht'
    have hsum :
        (∑ u : Fin (t + 1),
          (P.n : ℝ)⁻¹ *
            ∫ H : BatchHistory P d (u.castLE ht'),
              ∫ ξ : Seed,
                ‖kernelPhi P (t - u.val)
                  (O.response (batchDecision P (u.castLE ht') H) ξ -
                    batchCenter P (u.castLE ht') H)‖ ^ 2
                ∂O.law ∂batchPastHistoryLaw P O (u.castLE ht')) =
        (P.n : ℝ)⁻¹ *
          ∑ u ∈ Finset.range (t + 1), f u (t - u) := by
      rw [← Finset.mul_sum]
      congr 1
      have heach (u : Fin (t + 1)) :
          (∫ H : BatchHistory P d (u.castLE ht'),
              ∫ ξ : Seed,
                ‖kernelPhi P (t - u.val)
                  (O.response (batchDecision P (u.castLE ht') H) ξ -
                    batchCenter P (u.castLE ht') H)‖ ^ 2
                ∂O.law ∂batchPastHistoryLaw P O (u.castLE ht')) =
              f u.val (t - u.val) :=
        (hindex (u.castLE ht') (t - u.val)).symm
      simp_rw [heach]
      exact Fin.sum_univ_eq_sum_range (fun u : ℕ => f u (t - u)) (t + 1)
    change (if h : t + 1 ≤ P.T then
      (∫ z,
        ‖runtimeKernelNoise P O (t + 1) h z‖ ^ 2
        ∂((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw O (responseCount P)))) else 0) ≤ _
    rw [dif_pos ht']
    exact hbase.trans_eq hsum
  have htime :
      (∑ t : Fin P.T,
        ∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖runtimeKernelNoise P O (t.val + 1)
            (Nat.succ_le_iff.mpr t.isLt) z‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw O (responseCount P)))) ≤
      (P.n : ℝ)⁻¹ *
        ∑ t ∈ Finset.range P.T,
          ∑ u ∈ Finset.range (t + 1), f u (t - u) := by
    have hfin :
        (∑ t : Fin P.T,
          ∫ z : Fin P.T × (Fin (responseCount P) → Seed),
            ‖runtimeKernelNoise P O (t.val + 1)
              (Nat.succ_le_iff.mpr t.isLt) z‖ ^ 2
            ∂((algorithm (d := d) P).privateLaw.prod
              (freshSeedLaw O (responseCount P)))) =
          ∑ t ∈ Finset.range P.T, V t := by
      simp_rw [← hV]
      exact Fin.sum_univ_eq_sum_range V P.T
    rw [hfin, Finset.mul_sum]
    exact Finset.sum_le_sum (fun t ht =>
      hstep t (Finset.mem_range.mp ht))
  have hrect := triangular_runtime_lag_sum_le_rect P.T f hf_nonneg
  have hsourceSum :
      (∑ u ∈ Finset.range P.T,
        ∑ k ∈ Finset.range P.T, f u k) ≤ (P.T : ℝ) * B := by
    calc
      _ ≤ ∑ u ∈ Finset.range P.T, B := by
        apply Finset.sum_le_sum
        intro u hu
        let uf : Fin P.T := ⟨u, Finset.mem_range.mp hu⟩
        have h := hsource uf
        simpa only [← hindex uf] using h
      _ = (P.T : ℝ) * B := by simp [mul_comm]
  have hn : 0 ≤ (P.n : ℝ)⁻¹ := by positivity
  have htotal :
      (∑ t : Fin P.T,
        ∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖runtimeKernelNoise P O (t.val + 1)
            (Nat.succ_le_iff.mpr t.isLt) z‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw O (responseCount P)))) ≤
      (P.n : ℝ)⁻¹ * ((P.T : ℝ) * B) :=
    htime.trans ((mul_le_mul_of_nonneg_left hrect hn).trans
      (mul_le_mul_of_nonneg_left hsourceSum hn))
  have hT : (0 : ℝ) < P.T := by exact_mod_cast P.T_pos
  have hTinv : 0 ≤ (P.T : ℝ)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left htotal hTinv
  calc
    _ ≤ (P.T : ℝ)⁻¹ * ((P.n : ℝ)⁻¹ * ((P.T : ℝ) * B)) := hscaled
    _ = ((P.T : ℝ)⁻¹ * (P.T : ℝ)) * ((P.n : ℝ)⁻¹ * B) := by ring
    _ = (P.n : ℝ)⁻¹ * B := by
      rw [inv_mul_cancel₀ hT.ne', one_mul]

/-- The actual complete shared-source runtime-kernel noise obeys a physical
time-average `L²` bound on the original seed tape.  The coefficient depends
only on `p`, `q`, and `κ`; there is no extra residual-noise hypothesis. -/
theorem Admissible.paperSchedule_runtimeKernelNoise_sq_seed_average_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    (P.T : ℝ)⁻¹ *
      (∑ t : Fin P.T,
        ∫ seeds : Fin (responseCount P) → Seed,
          ‖runtimeKernelNoise P I.oracle (t.val + 1)
            (Nat.succ_le_iff.mpr t.isLt)
            (⟨0, P.T_pos⟩, seeds)‖ ^ 2
          ∂freshSeedLaw I.oracle (responseCount P)) ≤
      (2 * (1 + physicalResidualTrackerConstant p) *
        physicalKernelNoiseConstant p q κ) * ε ^ 2 / Cb := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let ν := paperNu σ ε
  let S := paperS σ ε
  let U := paperU p σ ε Ctail
  let e := paperEplus p q
  let K := physicalKernelNoiseConstant p q κ
  let M := 2 * (1 + physicalResidualTrackerConstant p)
  let B := K * ν ^ (2 - p) * U ^ e * (M * ν ^ p)
  have hsource (u : Fin P.T) :
      (∑ k ∈ Finset.range P.T,
        ∫ H : BatchHistory P d u,
          ∫ ξ : Seed,
            ‖kernelPhi P k
              (I.oracle.response (batchDecision P u H) ξ -
                batchCenter P u H)‖ ^ 2
            ∂I.oracle.law ∂batchPastHistoryLaw P I.oracle u) ≤ B := by
    simpa only [B, K, M, ν, U, e] using
      (Admissible.paperSchedule_actualKernelSource_sq_sum_le
        I ε Ctail κ Cb CI hε hκ hCb hCI u P.T)
  have hproduct := runtimeKernelNoise_sq_average_le_of_source_bound
    P I.oracle B hsource
  have hseed :
      (∑ t : Fin P.T,
        ∫ seeds : Fin (responseCount P) → Seed,
          ‖runtimeKernelNoise P I.oracle (t.val + 1)
            (Nat.succ_le_iff.mpr t.isLt)
            (⟨0, P.T_pos⟩, seeds)‖ ^ 2
          ∂freshSeedLaw I.oracle (responseCount P)) =
      (∑ t : Fin P.T,
        ∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖runtimeKernelNoise P I.oracle (t.val + 1)
            (Nat.succ_le_iff.mpr t.isLt) z‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw I.oracle (responseCount P)))) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact runtimeKernelNoise_sq_seed_integral_eq_joint P I.oracle
      (t.val + 1) (Nat.succ_le_iff.mpr t.isLt) ⟨0, P.T_pos⟩
  have hν : 0 < ν := paperNu_pos hε
  have hS : 0 < S := paperS_pos σ ε
  have hU : 0 < U := paperU_pos hε
  have hUe : 0 < U ^ e := Real.rpow_pos_of_pos hU _
  have hK : 0 ≤ K := by
    dsimp [K, physicalKernelNoiseConstant]
    positivity
  have hM : 0 ≤ M := by
    dsimp [M, physicalResidualTrackerConstant]
    positivity
  have hn : 0 < (P.n : ℝ) := by exact_mod_cast P.n_pos
  have hnLower : Cb * S ^ 2 * U ^ e ≤ (P.n : ℝ) := by
    change Cb * (paperS σ ε) ^ 2 *
      (paperU p σ ε Ctail) ^ (paperEplus p q) ≤
      (paperBatchSize p q σ ε Ctail Cb : ℝ)
    unfold paperBatchSize
    exact Nat.le_ceil _
  have hA : S ^ 2 * U ^ e / (P.n : ℝ) ≤ 1 / Cb := by
    apply (div_le_div_iff₀ hn hCb).2
    nlinarith [hnLower]
  have hνPow : ν ^ (2 - p) * ν ^ p = ν ^ (2 : ℝ) := by
    rw [← Real.rpow_add hν]
    congr 1
    ring
  have hνS : ν = ε * S := paperNu_eq_epsilon_mul_paperS hε
  have hscale : (P.n : ℝ)⁻¹ * B ≤
      (M * K) * ε ^ 2 / Cb := by
    have hcoef : 0 ≤ (M * K) * ε ^ 2 := by positivity
    calc
      (P.n : ℝ)⁻¹ * B =
          (M * K) * (ν ^ (2 - p) * ν ^ p) *
            (U ^ e / (P.n : ℝ)) := by dsimp [B]; ring
      _ = (M * K) * ε ^ 2 * (S ^ 2 * U ^ e / (P.n : ℝ)) := by
        rw [hνPow, Real.rpow_two, hνS]
        ring
      _ ≤ (M * K) * ε ^ 2 * (1 / Cb) :=
        mul_le_mul_of_nonneg_left hA hcoef
      _ = (M * K) * ε ^ 2 / Cb := by ring
  rw [hseed]
  exact hproduct.trans (by simpa only [M, K] using hscale)


end

end HeavyTailedNoise.UpperK1
