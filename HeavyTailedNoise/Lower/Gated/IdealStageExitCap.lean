import HeavyTailedNoise.Lower.Gated.IdealStageStartOrder

/-!
The decision that first starts stage `j+1` is exactly a cap hit for stage `j`.
This includes a cap hit at the algorithm's response-free final output, and
also handles stage zero starting and exiting on its first query.
-/

namespace HeavyTailedNoise

noncomputable section

theorem idealStageBeforeAt_nextStart_eq
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (j : ℕ)
    (hnext : idealStageStart hT U A r ξ a (j + 1) ≤ N) :
    (idealStateAt hT U A r ξ a
      (idealStageStart hT U A r ξ a (j + 1))).stage = j := by
  let τ := idealStageStart hT U A r ξ a (j + 1)
  have hafter := idealAfterAt_eq_stage_at_firstStart
    hT U A r ξ a (j + 1) (by omega) hnext
  change (idealStateAt hT U A r ξ a τ).stage = j
  change idealAfterAt hT U A r ξ a τ = j + 1 at hafter
  by_cases hz : τ = 0
  · have hupper : idealAfterAt hT U A r ξ a 0 ≤ 1 := by
      unfold idealAfterAt
      simpa [idealStateAt] using
        (idealStageAfter_le_succ U 0
          (idealDecisionAt hT U A r ξ a 0))
    have hjzero : j = 0 := by
      rw [hz] at hafter
      omega
    rw [hz, hjzero]
    rfl
  · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hbefore := idealStageStart_before hT U A r ξ a
      (j + 1) t (by simpa [τ, ht]) (by omega)
    have hstep := idealAfterAt_step_le_succ hT U A r ξ a
      (n := t) (by omega)
    have hnextEq : idealAfterAt hT U A r ξ a (t + 1) = j + 1 := by
      simpa [τ, ht, Nat.succ_eq_add_one] using hafter
    have hprevEq : idealAfterAt hT U A r ξ a t = j := by omega
    have hstate := idealStateAt_stage_succ_eq_after
      hT U A r ξ a (n := t) (by omega)
    rw [ht]
    simpa [Nat.succ_eq_add_one, hprevEq] using hstate

theorem idealExitQuery_mem_prefixCap
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hnext : idealStageStart hT U A r ξ a (j.val + 1) ≤ N) :
    softProjection (hardRadius T)
      (idealDecisionAt hT U A r ξ a
        (idealStageStart hT U A r ξ a (j.val + 1))) ∈
      prefixCapSet U j := by
  let τ := idealStageStart hT U A r ξ a (j.val + 1)
  have hbefore := idealStageBeforeAt_nextStart_eq
    hT U A r ξ a j.val hnext
  have hafter := idealAfterAt_eq_stage_at_firstStart
    hT U A r ξ a (j.val + 1) (by omega) hnext
  have hstep : idealStageAfter U j.val
      (idealDecisionAt hT U A r ξ a τ) = j.val + 1 := by
    unfold idealAfterAt at hafter
    rw [hbefore] at hafter
    exact hafter
  have hcap : idealCapHit U j.val
      (idealDecisionAt hT U A r ξ a τ) := by
    by_contra hnot
    have hstay : idealStageAfter U j.val
        (idealDecisionAt hT U A r ξ a τ) = j.val := by
      simp [idealStageAfter, hnot]
    omega
  obtain ⟨hj, hmem⟩ := hcap
  simpa [τ, idealCapHit] using hmem

end

end HeavyTailedNoise
