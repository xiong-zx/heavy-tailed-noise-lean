import HeavyTailedNoise.Lower.Gated.IdealStageMonotonicity

/-!
At a first hitting time the ideal stage equals the target exactly; before the
next hitting time it stays there. This supplies the fixed-stage premise in the
checked frozen/ideal full-transcript path identity.
-/

namespace HeavyTailedNoise

noncomputable section

theorem idealAfterAt_eq_stage_at_firstStart
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (j : ℕ) (hj : 0 < j)
    (hstart : idealStageStart hT U A r ξ a j ≤ N) :
    idealAfterAt hT U A r ξ a
      (idealStageStart hT U A r ξ a j) = j := by
  let τ := idealStageStart hT U A r ξ a j
  have hhit : j ≤ idealAfterAt hT U A r ξ a τ :=
    idealStageStart_hit hT U A r ξ a j hstart
  have hupper : idealAfterAt hT U A r ξ a τ ≤ j := by
    by_cases hzero : τ = 0
    · have hstep : idealAfterAt hT U A r ξ a 0 ≤ 1 := by
        unfold idealAfterAt
        simpa [idealStateAt] using
          (idealStageAfter_le_succ U 0
            (idealDecisionAt hT U A r ξ a 0))
      rw [hzero] at hhit ⊢
      omega
    · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hbefore := idealStageStart_before hT U A r ξ a j t
        (by simpa [τ, ht]) (by omega)
      have hstep := idealAfterAt_step_le_succ hT U A r ξ a
        (n := t) (by omega)
      have hstep' : idealAfterAt hT U A r ξ a τ ≤
          idealAfterAt hT U A r ξ a t + 1 := by
        simpa [ht, Nat.succ_eq_add_one] using hstep
      omega
  exact le_antisymm hupper hhit

theorem idealAfterAt_eq_stage_betweenStarts
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (j t : ℕ) (hj : 0 < j)
    (hstart : idealStageStart hT U A r ξ a j ≤ N)
    (hlo : idealStageStart hT U A r ξ a j ≤ t)
    (hhi : t < idealStageStart hT U A r ξ a (j + 1))
    (htN : t ≤ N) :
    idealAfterAt hT U A r ξ a t = j := by
  have hlow : j ≤ idealAfterAt hT U A r ξ a t := by
    rw [← idealAfterAt_eq_stage_at_firstStart
      hT U A r ξ a j hj hstart]
    exact idealAfterAt_mono_of_le hT U A r ξ a _ t hlo htN
  have hhigh := idealStageStart_before hT U A r ξ a
    (j + 1) t hhi htN
  omega

theorem idealAfterAt_eq_zero_before_firstStart
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (t : ℕ)
    (hhi : t < idealStageStart hT U A r ξ a 1)
    (htN : t ≤ N) :
    idealAfterAt hT U A r ξ a t = 0 := by
  have hhigh := idealStageStart_before hT U A r ξ a 1 t hhi htN
  omega

end

end HeavyTailedNoise
