import HeavyTailedNoise.Upper.Foundations.CoarseTrackerDrift

/-!
The coarse tracker's one-step negative drift on the small-noise event. The
center update is the exact `coarseCenter` called by the algorithm after the
current shared batch, and the point movement uses its normalized direction.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- The good-event branch of the manuscript's drift calculation. This is a
pathwise statement, prior to Markov's inequality and conditional averaging. -/
theorem tracker_goodEvent_increment_le {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (x w y estimate : Point d)
    (hbeta : 0 ≤ P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8)
    (hlarge : 2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ≤
      trackerError I x w)
    (hgood : ‖y - I.objective.grad x‖ ≤
      P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 2) :
    trackerError I (x - P.h • direction estimate) (coarseCenter P w y) -
      trackerError I x w ≤
        -(3 / 8 : ℝ) * P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ := by
  let τ := P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  let x' := x - P.h • direction estimate
  have hresidual :
      (y - I.objective.grad x) - (w - I.objective.grad x) = y - w := by abel
  have hcenter_repr : coarseCenter P w y - I.objective.grad x =
      (w - I.objective.grad x) +
        P.beta • upperClip τ
          ((y - I.objective.grad x) - (w - I.objective.grad x)) := by
    rw [hresidual]
    dsimp [coarseCenter, lowBand, τ]
    abel
  have hcontract := goodEvent_center_contract (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩)
    hbeta hbeta_le (w - I.objective.grad x) (y - I.objective.grad x)
    hlarge hgood
  have hcenter :
      ‖coarseCenter P w y - I.objective.grad x‖ ≤
        ‖w - I.objective.grad x‖ - P.beta * τ / 2 := by
    rw [hcenter_repr]
    exact hcontract
  have hstep := normalized_step_norm_le P x estimate hh
  have hstep_rev : ‖x - x'‖ ≤ P.h := by
    rw [norm_sub_rev]
    exact hstep
  have hgrad := I.grad_lipschitz x x'
  have htriangle :
      ‖coarseCenter P w y - I.objective.grad x'‖ ≤
        ‖coarseCenter P w y - I.objective.grad x‖ +
          ‖I.objective.grad x - I.objective.grad x'‖ := by
    have hvec : coarseCenter P w y - I.objective.grad x' =
        (coarseCenter P w y - I.objective.grad x) +
          (I.objective.grad x - I.objective.grad x') := by abel
    rw [hvec]
    exact norm_add_le _ _
  have hgradmove : ‖I.objective.grad x - I.objective.grad x'‖ ≤ Lbar * P.h :=
    hgrad.trans (mul_le_mul_of_nonneg_left hstep_rev I.Lbar_pos.le)
  have hmoveτ : Lbar * P.h ≤ P.beta * τ / 8 := hmove
  change ‖coarseCenter P w y - I.objective.grad x'‖ -
    ‖w - I.objective.grad x‖ ≤ -(3 / 8 : ℝ) * P.beta * τ
  calc
    _ ≤ (‖coarseCenter P w y - I.objective.grad x‖ +
        ‖I.objective.grad x - I.objective.grad x'‖) -
        ‖w - I.objective.grad x‖ :=
          sub_le_sub_right htriangle _
    _ ≤ (‖w - I.objective.grad x‖ - P.beta * τ / 2 +
        Lbar * P.h) - ‖w - I.objective.grad x‖ :=
          sub_le_sub_right (add_le_add hcenter hgradmove) _
    _ ≤ (‖w - I.objective.grad x‖ - P.beta * τ / 2 +
        P.beta * τ / 8) - ‖w - I.objective.grad x‖ :=
          sub_le_sub_right
            (add_le_add_right hmoveτ (‖w - I.objective.grad x‖ - P.beta * τ / 2)) _
    _ = -(3 / 8 : ℝ) * P.beta * τ := by ring

end

end HeavyTailedNoise.UpperK1
