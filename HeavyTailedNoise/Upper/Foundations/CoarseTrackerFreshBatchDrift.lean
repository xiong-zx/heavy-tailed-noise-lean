import HeavyTailedNoise.Upper.Foundations.CoarseTrackerConditionalDrift

/-!
One whole fresh batch, conditioned on an arbitrary fixed pre-batch decision
and center. The direction estimate may process all responses of that batch;
the tracker uses only its first response to update the next center. This
statement does not add a residual-moment assumption or restrict seed spaces.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem Admissible.tracker_freshBatch_mean_increment_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x w : Point d)
    (estimate : (Fin P.n → Seed) → Point d) (hestimate : Measurable estimate)
    (hbeta : 0 ≤ P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hscale : 12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8)
    (hlarge : 2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ≤
      trackerError I x w) :
    (∫ seeds : Fin P.n → Seed,
      trackerError I (x - P.h • direction (estimate seeds))
        (coarseCenter P w
          (I.oracle.response x (seeds ⟨0, P.n_pos⟩))) -
        trackerError I x w ∂freshSeedLaw I.oracle P.n) ≤
      -(1 / 8 : ℝ) *
        (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle P.n) :=
    freshSeedLaw_probability I.oracle P.n
  let τ := P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  let a := P.beta * τ
  let C := a + Lbar * P.h
  let y : (Fin P.n → Seed) → Point d := fun seeds =>
    I.oracle.response x (seeds ⟨0, P.n_pos⟩)
  let χ : (Fin P.n → Seed) → ℝ := fun seeds =>
    trackerError I (x - P.h • direction (estimate seeds))
      (coarseCenter P w (y seeds)) - trackerError I x w
  let B : Set (Fin P.n → Seed) :=
    {seeds | τ / 2 < ‖y seeds - I.objective.grad x‖}
  have hτ : 0 < τ := P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩
  have ha : 0 ≤ a := mul_nonneg hbeta hτ.le
  have hC : C ≤ (9 / 8 : ℝ) * a := by
    have hmove' : Lbar * P.h ≤ a / 8 := hmove
    dsimp [C]
    linarith [hmove']
  have hresponse : Measurable (I.oracle.response x) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hy : Measurable y := by
    exact hresponse.comp (measurable_pi_apply (⟨0, P.n_pos⟩ : Fin P.n))
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_lt measurable_const (hy.sub measurable_const).norm
  have hhscalar : Measurable (fun _ : Fin P.n → Seed => P.h) := measurable_const
  have hxnext : Measurable (fun seeds : Fin P.n → Seed =>
      x - P.h • direction (estimate seeds)) :=
    measurable_const.sub (hhscalar.smul ((measurable_direction).comp hestimate))
  have hcenter : Measurable (fun seeds : Fin P.n → Seed =>
      coarseCenter P w (y seeds)) :=
    measurable_coarseCenter P measurable_const hy
  have hχ : Measurable χ := by
    change Measurable (fun seeds : Fin P.n → Seed =>
      ‖coarseCenter P w (y seeds) - I.objective.grad
        (x - P.h • direction (estimate seeds))‖ - trackerError I x w)
    exact (hcenter.sub (I.objective.continuous_grad.measurable.comp hxnext)).norm.sub
      measurable_const
  have hbound (seeds : Fin P.n → Seed) : |χ seeds| ≤ C := by
    simpa only [χ, C, a, τ] using
      trackerError_increment_abs_le P I x w (y seeds) (estimate seeds) hbeta hh
  have hχint : Integrable χ (freshSeedLaw I.oracle P.n) :=
    Integrable.of_bound hχ.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun seeds => by
        simpa only [Real.norm_eq_abs] using hbound seeds)
  have hgood (seeds : Fin P.n → Seed) (hnot : seeds ∉ B) :
      χ seeds ≤ -(3 / 8 : ℝ) * a := by
    have hsource : ‖y seeds - I.objective.grad x‖ ≤ τ / 2 :=
      le_of_not_gt hnot
    simpa only [χ, y, a, τ, mul_assoc] using
      tracker_goodEvent_increment_le P I x w (y seeds) (estimate seeds)
        hbeta hbeta_le hh hmove hlarge hsource
  have hglobal (seeds : Fin P.n → Seed) : χ seeds ≤ (9 / 8 : ℝ) * a :=
    (le_abs_self _).trans ((hbound seeds).trans hC)
  have hbad : (freshSeedLaw I.oracle P.n) B ≤ (1 / 6 : ENNReal) := by
    simpa only [B, y, τ] using
      Admissible.firstBatch_badEvent_measure_le P I hτ hscale x
  change (∫ seeds, χ seeds ∂freshSeedLaw I.oracle P.n) ≤
    -(1 / 8 : ℝ) * a
  exact integral_increment_le_of_bad_event
    (freshSeedLaw I.oracle P.n) B hB χ hχint a ha hgood hglobal hbad

end

end HeavyTailedNoise.UpperK1
