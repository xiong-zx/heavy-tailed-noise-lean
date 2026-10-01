import HeavyTailedNoise.Upper.K1.ActualEstimatorFourErrors
import HeavyTailedNoise.Upper.K1.RuntimeNoiseNorm
import HeavyTailedNoise.Upper.K1.InitialMemoryNorm
import HeavyTailedNoise.Upper.K1.EMADriftSeed
import HeavyTailedNoise.Upper.K1.EMADriftNoLag
import HeavyTailedNoise.Upper.K1.TerminalClipBiasExpectation
import HeavyTailedNoise.Upper.K1.ConvergenceConstants
import HeavyTailedNoise.Upper.Foundations.FiniteAverageAssembly

/-!
The four errors of the literal completed estimator are averaged under the
one original global-seed law.  The constants are fixed functions of `p,q`;
the runtime batches, initial memory, source means, and terminal clip all
belong to the canonical strict-K=1 algorithm.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem Admissible.paperSchedule_average_actual_estimator_error_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε : ℝ) (hε : 0 < ε) :
    let P := paperSchedule p q Δ σ Lbar ε (upperCtail p)
      (1 / 8) (upperKappa p q) (upperCb p q) upperCI
      hε (by norm_num) (upperCb_pos p q) upperCI_pos
    (P.T : ENNReal)⁻¹ *
      (∫⁻ seeds : Fin (responseCount P) → Seed,
        ENNReal.ofReal
          (∑ t ∈ Finset.range P.T,
            ‖actualRuntimeEstimate P I.oracle seeds t -
              I.objective.grad (actualRuntimePoint P I.oracle seeds t)‖)
        ∂freshSeedLaw I.oracle (responseCount P)) ≤
      ENNReal.ofReal (ε / 8) := by
  dsimp only
  let Ctail := upperCtail p
  let κ := upperKappa p q
  let Cb := upperCb p q
  let CI := upperCI
  have hCtail : 0 < Ctail := upperCtail_pos p
  have hκ : 0 < κ := upperKappa_pos p q
  have hκle : κ ≤ 1 := upperKappa_le_one p q
  have hCb : 0 < Cb := upperCb_pos p q
  have hCI : 0 < CI := upperCI_pos
  have hCIge : 4096 ≤ CI := by norm_num [CI, upperCI]
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail
    (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
  let r₀ : Fin P.T := ⟨0, P.T_pos⟩
  let μ := freshSeedLaw I.oracle (responseCount P)
  let c : ENNReal := (P.T : ENNReal)⁻¹
  let Err : (Fin (responseCount P) → Seed) → ℝ := fun seeds =>
    ∑ t ∈ Finset.range P.T,
      ‖actualRuntimeEstimate P I.oracle seeds t -
        I.objective.grad (actualRuntimePoint P I.oracle seeds t)‖
  let Noise : (Fin (responseCount P) → Seed) → ℝ := fun seeds =>
    ∑ u : Fin P.T,
      ‖runtimeKernelNoise P I.oracle (u.val + 1)
        (Nat.succ_le_iff.mpr u.isLt) (r₀, seeds)‖
  let Initial : (Fin (responseCount P) → Seed) → ℝ := fun seeds =>
    ∑ u : Fin P.T, ‖actualInitialMemoryError P I.oracle seeds (u.val + 1)‖
  let Lag : (Fin (responseCount P) → Seed) → ℝ := fun seeds =>
    ∑ u : Fin P.T, ‖actualMeanLag P I.oracle seeds u.val‖
  let Bias : (Fin (responseCount P) → Seed) → ℝ := fun seeds =>
    ∑ u : Fin P.T, actualTerminalClipBiasNorm I P u (r₀, seeds)
  let e : (Fin (responseCount P) → Seed) → ENNReal :=
    fun seeds => ENNReal.ofReal (Err seeds)
  let f : (Fin (responseCount P) → Seed) → ENNReal :=
    fun seeds => ENNReal.ofReal (Noise seeds)
  let g : (Fin (responseCount P) → Seed) → ENNReal :=
    fun seeds => ENNReal.ofReal (Initial seeds)
  let h : (Fin (responseCount P) → Seed) → ENNReal :=
    fun seeds => ENNReal.ofReal (Lag seeds)
  let b : (Fin (responseCount P) → Seed) → ENNReal :=
    fun seeds => ENNReal.ofReal (Bias seeds)
  have hBiasEq (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) :
      actualTerminalClipBiasNorm I P u (r₀, seeds) =
      ‖actualClippedSourceEstimate P I.oracle seeds u -
        I.objective.grad (actualRuntimePoint P I.oracle seeds u.val)‖ := by
    rw [actualTerminalClipBiasNorm, actualClippedSourceEstimate,
      actualRuntimePoint_eq_batchDecision P I.oracle seeds u]
  have hErrFin (seeds : Fin (responseCount P) → Seed) :
      (∑ u : Fin P.T,
        ‖actualRuntimeEstimate P I.oracle seeds u.val -
          I.objective.grad (actualRuntimePoint P I.oracle seeds u.val)‖) =
        Err seeds := by
    exact Fin.sum_univ_eq_sum_range
      (fun t : ℕ => ‖actualRuntimeEstimate P I.oracle seeds t -
        I.objective.grad (actualRuntimePoint P I.oracle seeds t)‖) P.T
  have hpointReal (seeds : Fin (responseCount P) → Seed) :
      Err seeds ≤ Noise seeds + Initial seeds + Lag seeds + Bias seeds := by
    have hsum :
        (∑ u : Fin P.T,
          ‖actualRuntimeEstimate P I.oracle seeds u.val -
            I.objective.grad (actualRuntimePoint P I.oracle seeds u.val)‖) ≤
        ∑ u : Fin P.T,
          (‖runtimeKernelNoise P I.oracle (u.val + 1)
              (Nat.succ_le_iff.mpr u.isLt) (r₀, seeds)‖ +
            ‖actualInitialMemoryError P I.oracle seeds (u.val + 1)‖ +
            ‖actualMeanLag P I.oracle seeds u.val‖ +
            actualTerminalClipBiasNorm I P u (r₀, seeds)) := by
      apply Finset.sum_le_sum
      intro u hu
      simpa only [r₀, ← hBiasEq seeds u] using
        (actualRuntime_error_norm_le_four_errors P I seeds u)
    calc
      Err seeds = ∑ u : Fin P.T,
          ‖actualRuntimeEstimate P I.oracle seeds u.val -
            I.objective.grad (actualRuntimePoint P I.oracle seeds u.val)‖ :=
        (hErrFin seeds).symm
      _ ≤ ∑ u : Fin P.T,
          (‖runtimeKernelNoise P I.oracle (u.val + 1)
              (Nat.succ_le_iff.mpr u.isLt) (r₀, seeds)‖ +
            ‖actualInitialMemoryError P I.oracle seeds (u.val + 1)‖ +
            ‖actualMeanLag P I.oracle seeds u.val‖ +
            actualTerminalClipBiasNorm I P u (r₀, seeds)) := hsum
      _ = Noise seeds + Initial seeds + Lag seeds + Bias seeds := by
        simp only [Noise, Initial, Lag, Bias, Finset.sum_add_distrib]
  have hNoise0 (seeds : Fin (responseCount P) → Seed) : 0 ≤ Noise seeds := by
    exact Finset.sum_nonneg fun u _ => norm_nonneg _
  have hInitial0 (seeds : Fin (responseCount P) → Seed) :
      0 ≤ Initial seeds := by
    exact Finset.sum_nonneg fun u _ => norm_nonneg _
  have hLag0 (seeds : Fin (responseCount P) → Seed) : 0 ≤ Lag seeds := by
    exact Finset.sum_nonneg fun u _ => norm_nonneg _
  have hBias0 (seeds : Fin (responseCount P) → Seed) : 0 ≤ Bias seeds := by
    exact Finset.sum_nonneg fun u _ => by
      unfold actualTerminalClipBiasNorm
      exact norm_nonneg _
  have hpoint (seeds : Fin (responseCount P) → Seed) :
      e seeds ≤ f seeds + g seeds + h seeds + b seeds := by
    have hadd : ENNReal.ofReal
        (Noise seeds + Initial seeds + Lag seeds + Bias seeds) =
        f seeds + g seeds + h seeds + b seeds := by
      dsimp [f, g, h, b]
      rw [ENNReal.ofReal_add
        (add_nonneg (add_nonneg (hNoise0 seeds) (hInitial0 seeds))
          (hLag0 seeds)) (hBias0 seeds)]
      rw [ENNReal.ofReal_add
        (add_nonneg (hNoise0 seeds) (hInitial0 seeds)) (hLag0 seeds)]
      rw [ENNReal.ofReal_add (hNoise0 seeds) (hInitial0 seeds)]
    exact (ENNReal.ofReal_le_ofReal (hpointReal seeds)).trans_eq hadd
  have hNoiseMem (u : Fin P.T) : MemLp
      (fun seeds : Fin (responseCount P) → Seed =>
        runtimeKernelNoise P I.oracle (u.val + 1)
          (Nat.succ_le_iff.mpr u.isLt) (r₀, seeds)) 2 μ :=
    runtimeKernelNoise_seed_memLp_two P I.oracle
      (u.val + 1) (Nat.succ_le_iff.mpr u.isLt) r₀
  have hInitialMem (u : Fin P.T) : MemLp
      (fun seeds : Fin (responseCount P) → Seed =>
        actualInitialMemoryError P I.oracle seeds (u.val + 1)) 2 μ := by
    exact Admissible.paperSchedule_actualInitialMemoryError_seed_memLp_two
      I ε Ctail (1 / 8) κ Cb CI hε (by norm_num) hκ hκle hCb hCI
      (u.val + 1) (Nat.zero_lt_succ _)
  have hf : AEMeasurable f μ := by
    dsimp [f, Noise]
    apply AEMeasurable.ennreal_ofReal
    apply Finset.aemeasurable_fun_sum
    intro u hu
    exact (hNoiseMem u).aestronglyMeasurable.aemeasurable.norm
  have hg : AEMeasurable g μ := by
    dsimp [g, Initial]
    apply AEMeasurable.ennreal_ofReal
    apply Finset.aemeasurable_fun_sum
    intro u hu
    exact (hInitialMem u).aestronglyMeasurable.aemeasurable.norm
  have hLagMeas (u : Fin P.T) : Measurable
      (fun seeds : Fin (responseCount P) → Seed =>
        actualMeanLag P I.oracle seeds u.val) := by
    have hread := measurable_aggregate_actualBoundaryMeanLag
      P I.oracle u.val
    have hcomp : Measurable
        (fun seeds : Fin (responseCount P) → Seed =>
          aggregateMeanLag P
            (actualBandSourceSequence P I.oracle (r₀, seeds)) u.val) :=
      hread.comp
        ((measurable_const : Measurable
          (fun _ : Fin (responseCount P) → Seed => r₀)).prodMk
            measurable_id)
    have heq :
        (fun seeds : Fin (responseCount P) → Seed =>
          actualMeanLag P I.oracle seeds u.val) =
        (fun seeds => aggregateMeanLag P
          (actualBandSourceSequence P I.oracle (r₀, seeds)) u.val) := by
      funext seeds
      exact actualMeanLag_eq_boundarySourceLag P I.oracle seeds
        u.val u.isLt
    rw [heq]
    exact hcomp
  have hh : AEMeasurable h μ := by
    dsimp [h, Lag]
    apply AEMeasurable.ennreal_ofReal
    apply Finset.aemeasurable_fun_sum
    intro u hu
    exact (hLagMeas u).norm.aemeasurable
  have hNoiseBudget : c * (∫⁻ seeds, f seeds ∂μ) ≤
      ENNReal.ofReal (ε / 32) := by
    have hmain := Admissible.paperSchedule_runtimeKernelNoise_norm_seed_average_le
      I ε Ctail κ Cb CI hε hκ hCb hCI
      (upper_runtime_variance_coefficient_le p q)
    change c * (∫⁻ seeds, f seeds ∂μ) ≤
      ENNReal.ofReal (ε / 32) at hmain
    exact hmain
  have hInitialBudget : c * (∫⁻ seeds, g seeds ∂μ) ≤
      ENNReal.ofReal (ε / 32) := by
    have hmain := Admissible.paperSchedule_actualInitialMemoryError_average_norm_le
      I ε Ctail (1 / 8) κ Cb CI hε (by norm_num) hκ hκle hCb hCIge
    change c * (∫⁻ seeds, g seeds ∂μ) ≤
      ENNReal.ofReal (ε / 32) at hmain
    exact hmain
  have hLagBudget : c * (∫⁻ seeds, h seeds ∂μ) ≤
      ENNReal.ofReal (ε / 32) := by
    by_cases hqone : q = 1
    · subst q
      have hzero := paperSchedule_actualMeanLag_q_one
        p Δ σ Lbar ε Ctail κ Cb CI hε hCb hCI hκ hκle I.oracle
      have hfun : h = (fun _ => 0) := by
        funext seeds
        change ENNReal.ofReal (Lag seeds) = 0
        have hLagZero : Lag seeds = 0 := by
          dsimp [Lag]
          apply Finset.sum_eq_zero
          intro u hu
          rw [hzero seeds u.val, norm_zero]
        rw [hLagZero]
        simp
      rw [hfun]
      simp [show (0 : ℝ) ≤ ε / 32 by positivity]
    · have hqgt : 1 < q := by
        have hqle := I.q_range
        exact lt_of_le_of_ne hqle (Ne.symm hqone)
      have hbase := paperSchedule_actualMeanLag_seed_average_le
        p q Δ σ Lbar ε Ctail κ Cb CI
        I.p_range.1 hqgt hε hκ hCb hCI I
      have hLagRange (seeds : Fin (responseCount P) → Seed) :
          Lag seeds = ∑ t ∈ Finset.range P.T,
            ‖actualMeanLag P I.oracle seeds t‖ := by
        exact Fin.sum_univ_eq_sum_range
          (fun t : ℕ => ‖actualMeanLag P I.oracle seeds t‖) P.T
      have hcoef : paperMeanDriftConstant p q * κ * ε ≤ ε / 32 := by
        have hm := mul_le_mul_of_nonneg_right
          (upperKappa_drift_le p q) hε.le
        nlinarith
      calc
        c * (∫⁻ seeds, h seeds ∂μ) =
            (P.T : ENNReal)⁻¹ *
              (∫⁻ seeds, ENNReal.ofReal
                (∑ t ∈ Finset.range P.T,
                  ‖actualMeanLag P I.oracle seeds t‖) ∂μ) := by
                  congr 1
                  apply lintegral_congr
                  intro seeds
                  rw [show h seeds = ENNReal.ofReal (Lag seeds) from rfl,
                    hLagRange seeds]
        _ ≤ ENNReal.ofReal (paperMeanDriftConstant p q * κ * ε) := hbase
        _ ≤ ENNReal.ofReal (ε / 32) :=
          ENNReal.ofReal_le_ofReal hcoef
  have hBiasBudget : c * (∫⁻ seeds, b seeds ∂μ) ≤
      ENNReal.ofReal (ε / 32) := by
    have hmain := Admissible.paperSchedule_actualTerminalClipBias_seed_average_le
      I ε Ctail κ Cb CI hε hCtail hCb hCI
    have hscalar :
        4 * (1 + physicalResidualTrackerConstant p) *
          ε / Ctail ^ (p - 1) = ε / 32 := by
      have hc := upper_bias_coefficient p I.p_range.1
      calc
        _ = (4 * (1 + physicalResidualTrackerConstant p) /
              Ctail ^ (p - 1)) * ε := by ring
        _ = (1 / 32 : ℝ) * ε := by simpa only [Ctail] using congrArg (· * ε) hc
        _ = ε / 32 := by ring
    change c * (∫⁻ seeds, b seeds ∂μ) ≤
      ENNReal.ofReal
        (4 * (1 + physicalResidualTrackerConstant p) *
          ε / Ctail ^ (p - 1)) at hmain
    rw [hscalar] at hmain
    exact hmain
  have hassembly := extended_average_four_errors μ c e f g h b
    hf hg hh hpoint hNoiseBudget hInitialBudget hLagBudget hBiasBudget
  have hsum : ENNReal.ofReal (ε / 32) + ENNReal.ofReal (ε / 32) +
      ENNReal.ofReal (ε / 32) + ENNReal.ofReal (ε / 32) =
      ENNReal.ofReal (ε / 8) := by
    have hsmall : (0 : ℝ) ≤ ε / 32 := by positivity
    rw [← ENNReal.ofReal_add hsmall hsmall,
      ← ENNReal.ofReal_add (add_nonneg hsmall hsmall) hsmall,
      ← ENNReal.ofReal_add
        (add_nonneg (add_nonneg hsmall hsmall) hsmall) hsmall]
    congr 1
    ring
  change c * (∫⁻ seeds, e seeds ∂μ) ≤ ENNReal.ofReal (ε / 8)
  exact hassembly.trans_eq hsum

end

end HeavyTailedNoise.UpperK1
