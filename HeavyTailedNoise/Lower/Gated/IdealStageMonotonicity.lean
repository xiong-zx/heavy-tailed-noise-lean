import HeavyTailedNoise.Lower.Gated.IdealStoppedFrozenPathwise

/-!
The ideal post-cap stage is monotone through the `N` responsive decisions and
the final response-free output decision. Each decision advances at most one
column. No query-location restriction is used.
-/

namespace HeavyTailedNoise

noncomputable section

lemma idealStateAt_stage_succ_eq_after
    {d T N n : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (hn : n < N) :
    (idealStateAt hT U A r ξ a (n + 1)).stage =
      idealAfterAt hT U A r ξ a n := by
  simp [idealStateAt, idealStepState, idealAfterAt,
    idealDecisionAt, hn]

lemma idealAfterAt_step_mono
    {d T N n : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (hn : n < N) :
    idealAfterAt hT U A r ξ a n ≤
      idealAfterAt hT U A r ξ a (n + 1) := by
  have hs := idealStateAt_stage_succ_eq_after hT U A r ξ a hn
  calc
    idealAfterAt hT U A r ξ a n =
        (idealStateAt hT U A r ξ a (n + 1)).stage := hs.symm
    _ ≤ idealAfterAt hT U A r ξ a (n + 1) :=
      idealStage_le_after U _ _

lemma idealAfterAt_step_le_succ
    {d T N n : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (hn : n < N) :
    idealAfterAt hT U A r ξ a (n + 1) ≤
      idealAfterAt hT U A r ξ a n + 1 := by
  have hs := idealStateAt_stage_succ_eq_after hT U A r ξ a hn
  calc
    idealAfterAt hT U A r ξ a (n + 1) ≤
        (idealStateAt hT U A r ξ a (n + 1)).stage + 1 :=
      idealStageAfter_le_succ U _ _
    _ = idealAfterAt hT U A r ξ a n + 1 := by rw [hs]

theorem idealAfterAt_mono_of_le
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (t u : ℕ) (htu : t ≤ u) (hu : u ≤ N) :
    idealAfterAt hT U A r ξ a t ≤
      idealAfterAt hT U A r ξ a u := by
  induction u with
  | zero =>
      have ht : t = 0 := by omega
      subst t
      exact le_rfl
  | succ u ih =>
      by_cases ht : t ≤ u
      · exact (ih ht (by omega)).trans
          (idealAfterAt_step_mono hT U A r ξ a (by omega))
      · have heq : t = u + 1 := by omega
        subst t
        exact le_rfl

end

end HeavyTailedNoise
