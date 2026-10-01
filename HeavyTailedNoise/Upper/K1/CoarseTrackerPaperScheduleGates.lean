import HeavyTailedNoise.Upper.K1.CoarseTrackerPhysicalCoefficients

/-!
All tracker coefficient gates for the literal paper schedule after choosing
the allowed fixed step coefficient `c_h = 1/8`.  No noise-floor or band-count
restriction is made.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem paperSchedule_eighth_tracker_gates
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hLbar : 0 < Lbar)
    (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail
      (1 / 8) κ Cb CI hε (by norm_num) hCb hCI
    0 < P.beta ∧ P.beta ≤ 1 / 4 ∧ 0 ≤ P.h ∧
      12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ∧
      Lbar * P.h ≤ P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change 0 < paperBeta σ ε
    exact paperBeta_pos σ ε
  · change paperBeta σ ε ≤ 1 / 4
    exact paperBeta_le_quarter σ ε
  · change 0 ≤ paperStep (1 / 8) ε Lbar
    exact paperStep_eighth_nonneg hε hLbar
  · change 12 * σ ≤ paperTau σ ε 0
    exact paperTau_zero_ge_twelve_sigma σ ε
  · change Lbar * paperStep (1 / 8) ε Lbar ≤
        paperBeta σ ε * paperTau σ ε 0 / 8
    exact paperStep_eighth_tracker_move hε hLbar

end

end HeavyTailedNoise.UpperK1
