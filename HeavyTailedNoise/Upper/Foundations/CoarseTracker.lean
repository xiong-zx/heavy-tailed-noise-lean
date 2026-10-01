import HeavyTailedNoise.Upper.K1.Algorithm
import HeavyTailedNoise.Upper.Foundations.UpperMomentFoundations
import HeavyTailedNoise.Analysis.Smoothness

/-!
The coarse tracker in the literal shared-batch `K=1` method. All statements
below use the first returned vector of a runtime batch and the center and
query point fixed before that batch. No conditional residual-moment premise is
added to the admissible oracle class.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- The tracker error at a pre-batch decision and center. -/
def trackerError {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x w : Point d) : ℝ := ‖w - I.objective.grad x‖

theorem measurable_trackerError {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar) :
    Measurable (fun z : Point d × Point d => trackerError I z.1 z.2) := by
  exact (measurable_snd.sub
    (I.objective.continuous_grad.measurable.comp measurable_fst)).norm

theorem normalized_step_norm_le {d : ℕ} (x estimate : Point d)
    (hh : 0 ≤ P.h) :
    ‖(x - P.h • direction estimate) - x‖ ≤ P.h := by
  have hvec : (x - P.h • direction estimate) - x =
      -(P.h • direction estimate) := by abel
  rw [hvec, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  exact (mul_le_mul_of_nonneg_left (direction_norm_le_one estimate) hh).trans
    (by simp)

theorem coarseCenter_increment_norm_le {d : ℕ} (w y : Point d)
    (hbeta : 0 ≤ P.beta) :
    ‖coarseCenter P w y - w‖ ≤ P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ := by
  have hclip := upperClip_norm_le (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩) (y - w)
  calc
    ‖coarseCenter P w y - w‖ = ‖P.beta • lowBand P (y - w)‖ := by
      simp [coarseCenter]
    _ = P.beta * ‖lowBand P (y - w)‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbeta]
    _ ≤ P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ := by
      exact mul_le_mul_of_nonneg_left hclip hbeta

/-- Exact deterministic increment envelope before inserting the physical
schedule. It is dimension free and uses only population smoothness. -/
theorem trackerError_increment_abs_le {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (x w y estimate : Point d) (hbeta : 0 ≤ P.beta) (hh : 0 ≤ P.h) :
    |trackerError I (x - P.h • direction estimate) (coarseCenter P w y) -
        trackerError I x w| ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h := by
  let x' := x - P.h • direction estimate
  let w' := coarseCenter P w y
  have hreverse :
      |‖w' - I.objective.grad x'‖ - ‖w - I.objective.grad x‖| ≤
        ‖w' - w‖ + ‖I.objective.grad x' - I.objective.grad x‖ := by
    calc
      _ ≤ ‖(w' - I.objective.grad x') - (w - I.objective.grad x)‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖(w' - w) - (I.objective.grad x' - I.objective.grad x)‖ := by
        congr 1
        abel
      _ ≤ _ := norm_sub_le _ _
  have hcenter := coarseCenter_increment_norm_le P w y hbeta
  have hgrad := I.grad_lipschitz x' x
  have hstep := normalized_step_norm_le P x estimate hh
  change |‖w' - I.objective.grad x'‖ - ‖w - I.objective.grad x‖| ≤ _
  calc
    _ ≤ ‖w' - w‖ + ‖I.objective.grad x' - I.objective.grad x‖ := hreverse
    _ ≤ P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * ‖x' - x‖ :=
      add_le_add hcenter hgrad
    _ ≤ P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hstep I.Lbar_pos.le)

/-- The source vector is one fresh first-batch response, before any center
update. Its p-moment is the original admissibility bound. -/
theorem firstResponse_centered_moment {d : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x : History → Point d) (hx : Measurable x) :
    (∫⁻ hist : History, ∫⁻ seeds : Fin P.n → Seed,
      ENNReal.ofReal
        (‖I.oracle.response (x hist) (seeds ⟨0, P.n_pos⟩) -
          I.objective.grad (x hist)‖ ^ p)
      ∂freshSeedLaw I.oracle P.n ∂historyLaw) ≤ ENNReal.ofReal (σ ^ p) :=
  I.predictable_freshBatch_coordinate_centered_moment historyLaw x hx
    P.n ⟨0, P.n_pos⟩

/-- The raw first response initializes the tracker at `x₁=0` with exactly
the admissible centered p-moment, without a separate initialization oracle. -/
theorem initial_tracker_moment {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar) :
    (∫⁻ ξ, ENNReal.ofReal
      (trackerError I 0 (I.oracle.response 0 ξ) ^ p) ∂I.oracle.law) ≤
        ENNReal.ofReal (σ ^ p) := by
  simpa only [trackerError] using I.centered_moment 0

end

end HeavyTailedNoise.UpperK1
