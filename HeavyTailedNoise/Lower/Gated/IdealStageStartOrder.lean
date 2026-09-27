import HeavyTailedNoise.Lower.Gated.IdealFrozenOutputQuery

/-!
First hitting times are ordered by stage threshold. Positive consecutive
stages have strictly ordered starts because one decision advances at most one
column; the virtual stage-zero start is handled separately.
-/

namespace HeavyTailedNoise

noncomputable section

lemma idealStageStart_le_of_hit
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (j t : ℕ) (htN : t ≤ N)
    (hhit : j ≤ idealAfterAt hT U A r ξ a t) :
    idealStageStart hT U A r ξ a j ≤ t := by
  classical
  have hex : ∃ s : ℕ, s ≤ N ∧
      j ≤ idealAfterAt hT U A r ξ a s := ⟨t, htN, hhit⟩
  rw [idealStageStart, dif_pos hex]
  exact Nat.find_le ⟨htN, hhit⟩

theorem idealStageStart_mono_target
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (j k : ℕ) (hjk : j ≤ k) :
    idealStageStart hT U A r ξ a j ≤
      idealStageStart hT U A r ξ a k := by
  by_cases hk : idealStageStart hT U A r ξ a k ≤ N
  · have hhit := idealStageStart_hit hT U A r ξ a k hk
    exact idealStageStart_le_of_hit hT U A r ξ a
      j _ hk (le_trans hjk hhit)
  · have heq : idealStageStart hT U A r ξ a k = N + 1 := by
      have hb := idealStageStart_le_succ hT U A r ξ a k
      omega
    rw [heq]
    exact idealStageStart_le_succ hT U A r ξ a j

theorem idealStageStart_lt_next_of_started
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (j : ℕ) (hj : 0 < j)
    (hnext : idealStageStart hT U A r ξ a (j + 1) ≤ N) :
    idealStageStart hT U A r ξ a j <
      idealStageStart hT U A r ξ a (j + 1) := by
  have hle := idealStageStart_mono_target hT U A r ξ a
    j (j + 1) (by omega)
  have hstart : idealStageStart hT U A r ξ a j ≤ N :=
    le_trans hle hnext
  have hjAfter := idealAfterAt_eq_stage_at_firstStart
    hT U A r ξ a j hj hstart
  have hnextAfter := idealAfterAt_eq_stage_at_firstStart
    hT U A r ξ a (j + 1) (by omega) hnext
  by_contra hnot
  have heq : idealStageStart hT U A r ξ a j =
      idealStageStart hT U A r ξ a (j + 1) := by omega
  rw [heq] at hjAfter
  omega

end

end HeavyTailedNoise
