import HeavyTailedNoise.Upper.K1.CoarseTrackerAdaptiveDrift

/-!
Finite, pathwise last-exit decomposition for a scalar tracker.  No stopping
time is chosen by hindsight in the probabilistic argument: the existential
start below is used only for a finite union of stopped interval events.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

/-- At every time there is a last-exit start whose value is at most the
initial-or-one-step overshoot level and after which the path stayed in the
large-error region.  The proof uses only the deterministic increment cap. -/
theorem tracker_lastExit_start (ρ : ℕ → ℝ) (b C : ℝ)
    (hstep : ∀ t, ρ (t + 1) ≤ ρ t + C) (t : ℕ) :
    ∃ u ≤ t,
      ρ u ≤ max (ρ 0) (b + C) ∧
      ∀ s, u ≤ s → s < t → b ≤ ρ s := by
  induction t with
  | zero =>
      refine ⟨0, le_refl 0, le_max_left _ _, ?_⟩
      intro s hs hst
      omega
  | succ t ih =>
      by_cases hlarge : b ≤ ρ t
      · obtain ⟨u, hu, hbase, hstay⟩ := ih
        refine ⟨u, Nat.le_trans hu (Nat.le_succ t), hbase, ?_⟩
        intro s hus hst
        by_cases hst' : s < t
        · exact hstay s hus hst'
        · have hst'' : s = t := by omega
          simpa [hst''] using hlarge
      · refine ⟨t + 1, le_refl _, ?_, ?_⟩
        · have hsmall : ρ t < b := lt_of_not_ge hlarge
          have hbound : ρ (t + 1) ≤ b + C := by
            linarith [hstep t]
          exact hbound.trans (le_max_right _ _)
        · intro s hus hst
          omega

/-- A positive excursion above the base level must be realized by one
nonempty interval that remained in the large-error region throughout. -/
theorem tracker_large_excursion_has_stopped_interval
    (ρ : ℕ → ℝ) (b C x : ℝ)
    (hstep : ∀ t, ρ (t + 1) ≤ ρ t + C)
    (hx : 0 < x) (t : ℕ)
    (hhigh : max (ρ 0) (b + C) + x < ρ t) :
    ∃ u < t,
      (∀ s, u ≤ s → s < t → b ≤ ρ s) ∧
      x < ρ t - ρ u := by
  obtain ⟨u, hu, hbase, hstay⟩ := tracker_lastExit_start ρ b C hstep t
  refine ⟨u, ?_, hstay, ?_⟩
  · by_contra hnot
    have hut : u = t := by omega
    subst u
    linarith
  · linarith

end

end HeavyTailedNoise.UpperK1
