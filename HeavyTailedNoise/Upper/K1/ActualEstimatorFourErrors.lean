import HeavyTailedNoise.Upper.K1.ActualEstimatorKernelIdentity

/-!
The completed estimator on the literal global seed path has four errors:
complete shared-source kernel noise, initialization sample error, EMA mean
lag, and terminal clipping bias. This pointwise identity introduces no
probabilistic independence assumption.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem actualRuntime_error_norm_le_four_errors
    {q : ℝ} (P : Schedule q)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) :
    ‖actualRuntimeEstimate P I.oracle seeds u.val -
        I.objective.grad (actualRuntimePoint P I.oracle seeds u.val)‖ ≤
      ‖runtimeKernelNoise P I.oracle (u.val + 1)
        (Nat.succ_le_iff.mpr u.isLt)
        ((⟨0, P.T_pos⟩ : Fin P.T), seeds)‖ +
      ‖actualInitialMemoryError P I.oracle seeds (u.val + 1)‖ +
      ‖actualMeanLag P I.oracle seeds u.val‖ +
      ‖actualClippedSourceEstimate P I.oracle seeds u -
        I.objective.grad (actualRuntimePoint P I.oracle seeds u.val)‖ := by
  have hfirst := actualRuntime_error_norm_le_centered_plus_terminalBias
    P I seeds u
  rw [actualEstimator_centered_eq_kernel_initial_lag P I.oracle seeds u] at hfirst
  have hcenter := (norm_add_le
    (runtimeKernelNoise P I.oracle (u.val + 1)
      (Nat.succ_le_iff.mpr u.isLt)
      ((⟨0, P.T_pos⟩ : Fin P.T), seeds) +
        actualInitialMemoryError P I.oracle seeds (u.val + 1))
    (actualMeanLag P I.oracle seeds u.val)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  exact hfirst.trans (add_le_add hcenter le_rfl)

end

end HeavyTailedNoise.UpperK1
