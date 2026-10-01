import HeavyTailedNoise.Upper.K1.CoarseTrackerPredictableWeight

/-!
The actual adaptive one-step Lyapunov contraction.  Its stopped weight is
measurable before the complete current batch; the law used here is the
already proved pre-batch-history × whole-fresh-batch product law.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualTracker_shiftedStep_contract
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T)
    (hbeta : 0 ≤ P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hscale : 12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (∫ z in {z : Fin P.T × (Fin (responseCount P) → Seed) |
        2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ≤
          actualTrackerAtBoundary P I u.val z},
      shiftedTrackerWeight (actualTrackerAtBoundary P I)
        (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
        (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h)
        lam (u.val + 1) z
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P)))) ≤
    trackerMGFContraction P Lbar lam *
      ∫ z in {z : Fin P.T × (Fin (responseCount P) → Seed) |
          2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ≤
            actualTrackerAtBoundary P I u.val z},
        shiftedTrackerWeight (actualTrackerAtBoundary P I)
          (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
          (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h)
          lam u.val z
        ∂((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw I.oracle (responseCount P))) := by
  let b := 2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
  let r := trackerMGFContraction P Lbar lam
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  let ν := (batchPastHistoryLaw P I.oracle u).prod
    (freshSeedLaw I.oracle P.n)
  let f := stoppedWeightOnHistory P I u b C lam
  let S : Set (Fin P.T × (Fin (responseCount P) → Seed)) :=
    {z | b ≤ actualTrackerAtBoundary P I u.val z}
  let V : ℕ → (Fin P.T × (Fin (responseCount P) → Seed)) → ℝ :=
    shiftedTrackerWeight (actualTrackerAtBoundary P I) b C lam
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const (measurable_actualTrackerAtBoundary P I u.val)
  have hfmeas : Measurable f := measurable_stoppedWeightOnHistory P I u b C lam
  have hfInt : Integrable f (batchPastHistoryLaw P I.oracle u) :=
    stoppedWeightOnHistory_integrable P I u b lam hlam hbeta hh
  have hweightedInt : Integrable
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        f z.1 * Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2)) ν :=
    stoppedWeight_batchProduct_integrable P I u b lam hlam hbeta hh
  have hlarge (H : BatchHistory P d u) (hpos : f H ≠ 0) :
      b ≤ trackerError I (batchDecision P u H) (batchCenter P u H) :=
    stoppedWeightOnHistory_large P I u b C lam H hpos
  have hproduct := tracker_stoppedWeight_exponential_le P I u
    hbeta hbeta_le hh hscale hmove lam hlam f
    (stoppedWeightOnHistory_nonneg P I u b C lam) hlarge
    hfInt hweightedInt
  have hleftTransport := tracker_stoppedWeight_actual_integral_eq
    (lam := lam) P I u f hfmeas
  have hhistoryTransport :
      (∫ H, f H ∂batchPastHistoryLaw P I.oracle u) =
        ∫ z, f (batchHistoryOfRun P I.oracle u z) ∂μ := by
    have hmap := measurePreserving_actualBatchHistory P I.oracle u
    rw [← hmap.map_eq]
    exact integral_map_of_stronglyMeasurable hmap.measurable hfmeas.stronglyMeasurable
  have hleftPoint (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      S.indicator (V (u.val + 1)) z =
        f (batchHistoryOfRun P I.oracle u z) *
          Real.exp (lam * trackerIncrementOnHistory P I u
            (batchHistoryOfRun P I.oracle u z)
            (batchSeedBlock P u z.2)) := by
    rw [stoppedWeight_mul_increment_actual_eq P I u b C lam z]
    by_cases h : b ≤ actualTrackerAtBoundary P I u.val z
    · have hz : z ∈ S := h
      simp only [Set.indicator_of_mem hz, if_pos h, V]
    · have hz : z ∉ S := h
      simp only [Set.indicator_of_notMem hz, if_neg h]
  have hrightPoint (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      S.indicator (V u.val) z =
        f (batchHistoryOfRun P I.oracle u z) := by
    change S.indicator (V u.val) z =
      stoppedWeightOnHistory P I u b C lam
        (batchHistoryOfRun P I.oracle u z)
    rw [stoppedWeightOnHistory_actual_eq P I u b C lam z]
    by_cases h : b ≤ actualTrackerAtBoundary P I u.val z
    · have hz : z ∈ S := h
      simp only [Set.indicator_of_mem hz, if_pos h, V]
    · have hz : z ∉ S := h
      simp only [Set.indicator_of_notMem hz, if_neg h]
  change (∫ z in S, V (u.val + 1) z ∂μ) ≤ r * ∫ z in S, V u.val z ∂μ
  calc
    (∫ z in S, V (u.val + 1) z ∂μ) =
        ∫ z, f (batchHistoryOfRun P I.oracle u z) *
          Real.exp (lam * trackerIncrementOnHistory P I u
            (batchHistoryOfRun P I.oracle u z)
            (batchSeedBlock P u z.2)) ∂μ := by
        rw [← integral_indicator hS]
        exact integral_congr_ae (Filter.Eventually.of_forall hleftPoint)
    _ = ∫ z : BatchHistory P d u × (Fin P.n → Seed),
          f z.1 * Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2)
          ∂ν := hleftTransport
    _ ≤ r * ∫ H, f H ∂batchPastHistoryLaw P I.oracle u := hproduct
    _ = r * ∫ z in S, V u.val z ∂μ := by
      rw [hhistoryTransport, ← integral_indicator hS]
      have hfun :
          (fun z => f (batchHistoryOfRun P I.oracle u z)) =
          S.indicator (V u.val) := by
        funext z
        exact (hrightPoint z).symm
      rw [hfun]

/-- Uniform shifted exponential moment along every actual runtime boundary.
The scalar `K` is later instantiated by a constant once the physical
schedule gives `0 ≤ r < 1`; no exponential moment of `ρ₁` is required. -/
theorem actualTracker_shiftedWeight_uniform
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hbeta : 0 ≤ P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hscale : 12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8)
    (lam K : ℝ) (hlam : 0 ≤ lam)
    (hKbase : 1 ≤ K)
    (hKstep : trackerMGFContraction P Lbar lam * K + 1 ≤ K) :
    ∀ t ≤ P.T,
      (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
        shiftedTrackerWeight (actualTrackerAtBoundary P I)
          (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
          (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h)
          lam t z
        ∂((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw I.oracle (responseCount P)))) ≤ K := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle (responseCount P)) :=
    freshSeedLaw_probability I.oracle (responseCount P)
  let b := 2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩
  let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
  let r := trackerMGFContraction P Lbar lam
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (by norm_num)
      (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩).le
  have hC : 0 ≤ C :=
    add_nonneg (mul_nonneg hbeta (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩).le)
      (mul_nonneg I.Lbar_pos.le hh)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hρ0 (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      0 ≤ actualTrackerAtBoundary P I 0 z :=
    actualTrackerAtBoundary_nonneg P I 0 z
  have hρmeas (t : ℕ) (ht : t ≤ P.T) :
      Measurable (actualTrackerAtBoundary P I t) :=
    measurable_actualTrackerAtBoundary P I t
  have hstep (t : ℕ) (ht : t < P.T)
      (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      actualTrackerAtBoundary P I (t + 1) z ≤
        actualTrackerAtBoundary P I t z + C := by
    have hinc := actualTrackerAtBoundary_increment_abs_le P I
      (⟨t, ht⟩ : Fin P.T) z hbeta hh
    have hle := le_abs_self
      (actualTrackerAtBoundary P I (t + 1) z -
        actualTrackerAtBoundary P I t z)
    linarith
  have hInt (t : ℕ) (ht : t ≤ P.T) :
      Integrable
        (shiftedTrackerWeight (actualTrackerAtBoundary P I) b C lam t)
        ((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw I.oracle (responseCount P))) :=
    actualTrackerShiftedWeight_integrable P I b lam hlam hbeta hh t ht
  have hcontract (t : ℕ) (ht : t < P.T) :=
    actualTracker_shiftedStep_contract P I
      (⟨t, ht⟩ : Fin P.T)
      hbeta hbeta_le hh hscale hmove lam hlam
  exact shiftedTrackerWeight_integral_uniform
    ((algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw I.oracle (responseCount P)))
    (actualTrackerAtBoundary P I) b C lam r K P.T
    hb hC hlam hr hKbase hKstep hρ0 hρmeas hstep hInt hcontract

/-- Uniform exponential tail for the actual adaptive tracker above its
heavy-tailed initial value plus the deterministic overshoot scale. -/
theorem actualTracker_shifted_tail
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hbeta : 0 ≤ P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hscale : 12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8)
    (lam K : ℝ) (hlam : 0 ≤ lam)
    (hKbase : 1 ≤ K)
    (hKstep : trackerMGFContraction P Lbar lam * K + 1 ≤ K)
    (t : ℕ) (ht : t ≤ P.T) (x : ℝ) :
    (((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))).real
      {z | x ≤ actualTrackerAtBoundary P I t z -
        actualTrackerAtBoundary P I 0 z -
          (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ +
            (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h))}) ≤
      Real.exp (-lam * x) * K := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle (responseCount P)) :=
    freshSeedLaw_probability I.oracle (responseCount P)
  have hInt := actualTrackerShiftedWeight_integrable P I
    (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    lam hlam hbeta hh t ht
  have hbound := actualTracker_shiftedWeight_uniform P I
    hbeta hbeta_le hh hscale hmove lam K hlam hKbase hKstep t ht
  exact shiftedTrackerWeight_tail
    ((algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw I.oracle (responseCount P)))
    (actualTrackerAtBoundary P I)
    (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h)
    lam K x t hlam hInt hbound

end

end HeavyTailedNoise.UpperK1
