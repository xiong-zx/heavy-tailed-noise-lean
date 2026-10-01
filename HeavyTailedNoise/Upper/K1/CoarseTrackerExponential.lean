import HeavyTailedNoise.Upper.K1.CoarseTrackerBoundedDriftMGF
import HeavyTailedNoise.Upper.K1.BatchPastProduct
import HeavyTailedNoise.Upper.K1.CoarseTrackerIncrement
import HeavyTailedNoise.Upper.Foundations.MeasurableFixedArgument
import HeavyTailedNoise.Upper.Foundations.CoarseTrackerIncrementCompositionMeasurable
import HeavyTailedNoise.Upper.Foundations.PredictableMGFIntegral

/-! Exponential tracker bounds on the actual shared-batch path. -/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- The scalar Hoeffding contraction factor of the coarse tracker. -/
def trackerMGFContraction (Lbar lam : ℝ) : ℝ :=
  Real.exp
    (((((‖(P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h) -
            -(P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h)‖₊ /
          2) ^ 2 : ℝ≥0) : ℝ) * lam ^ 2 / 2) -
      lam * ((1 / 8 : ℝ) *
        (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)))

/-- Integrate a nonnegative predictable weight against the fresh batch.  This
is the stopped-interval contraction used when the weight records that all
previous tracker errors since a chosen start remained above threshold. -/
theorem tracker_stoppedWeight_exponential_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T)
    (hbeta : 0 ≤ P.beta) (hbeta_le : P.beta ≤ 1 / 4)
    (hh : 0 ≤ P.h)
    (hscale : 12 * σ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    (hmove : Lbar * P.h ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ / 8)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (f : BatchHistory P d u → ℝ)
    (hf_nonneg : ∀ H, 0 ≤ f H)
    (hf_large : ∀ H, f H ≠ 0 →
      2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ ≤
        trackerError I (batchDecision P u H) (batchCenter P u H))
    (hf_int : Integrable f (batchPastHistoryLaw P I.oracle u))
    (hweighted_int : Integrable
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        f z.1 * Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2))
      ((batchPastHistoryLaw P I.oracle u).prod
        (freshSeedLaw I.oracle P.n))) :
    (∫ z : BatchHistory P d u × (Fin P.n → Seed),
      f z.1 * Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2)
      ∂(batchPastHistoryLaw P I.oracle u).prod
        (freshSeedLaw I.oracle P.n)) ≤
      trackerMGFContraction P Lbar lam *
        ∫ H, f H ∂batchPastHistoryLaw P I.oracle u := by
  let r := trackerMGFContraction P Lbar lam
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle P.n) :=
    freshSeedLaw_probability I.oracle P.n
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (batchPastHistoryLaw P I.oracle u) := by
    unfold batchPastHistoryLaw
    infer_instance
  have hmgfH (H : BatchHistory P d u) (hf : f H ≠ 0) :
      mgf (trackerIncrementOnHistory P I u H)
        (freshSeedLaw I.oracle P.n) lam ≤ r := by
    let x := batchDecision P u H
    let w := batchCenter P u H
    let estimate : (Fin P.n → Seed) → Point d :=
      batchEstimateOnHistory P I.oracle u H
    let y : (Fin P.n → Seed) → Point d :=
      fun seeds => I.oracle.response x (seeds ⟨0, P.n_pos⟩)
    let χ : (Fin P.n → Seed) → ℝ := fun seeds =>
      trackerError I (x - P.h • direction (estimate seeds))
        (coarseCenter P w (y seeds)) - trackerError I x w
    let C := P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h
    let δ := (1 / 8 : ℝ) *
      (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
    have hestimate : Measurable estimate :=
      measurable_fixed_first_arg
        (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
          batchEstimateOnHistory P I.oracle u z.1 z.2)
        (measurable_batchEstimateOnHistory P I.oracle u) H
    have hfirst : Measurable
        (fun seeds : Fin P.n → Seed => seeds ⟨0, P.n_pos⟩) :=
      measurable_pi_apply (⟨0, P.n_pos⟩ : Fin P.n)
    have hy : Measurable y :=
      I.oracle.measurable_response.comp
        (measurable_const.prodMk hfirst)
    have hχ : Measurable χ :=
      measurable_trackerIncrement_composition P
        (fun a : Point d × Point d => trackerError I a.1 a.2)
        (measurable_trackerError I)
        (fun _ => x) (fun _ => w) estimate y
        measurable_const measurable_const hestimate hy
    have hdrift : (∫ seeds, χ seeds ∂freshSeedLaw I.oracle P.n) ≤ -δ := by
      simpa only [χ, δ, y, neg_mul] using
        (Admissible.tracker_freshBatch_mean_increment_le P I
        x w estimate hestimate hbeta hbeta_le hh hscale hmove
        (hf_large H hf))
    have hbound (seeds : Fin P.n → Seed) : |χ seeds| ≤ C :=
      trackerError_increment_abs_le P I x w (y seeds)
        (estimate seeds) hbeta hh
    have hC : 0 ≤ C :=
      add_nonneg
        (mul_nonneg hbeta (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩).le)
        (mul_nonneg I.Lbar_pos.le hh)
    have hδ : 0 ≤ δ := by
      dsimp [δ]
      exact mul_nonneg (by norm_num)
        (mul_nonneg hbeta (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩).le)
    have hmgf := bounded_negativeDrift_mgf_le
      (freshSeedLaw I.oracle P.n) χ hχ
      C δ lam hC hδ hlam hbound hdrift
    have hfun : trackerIncrementOnHistory P I u H = χ := by
      funext seeds
      rw [trackerIncrementOnHistory]
    rw [hfun]
    exact hmgf
  exact predictable_weighted_mgf_integral_le
    (batchPastHistoryLaw P I.oracle u) (freshSeedLaw I.oracle P.n)
    f (fun H seeds => trackerIncrementOnHistory P I u H seeds)
    lam r hf_nonneg hf_int hweighted_int hmgfH

/-- The weighted exponential integral is exactly the one on the actual
private/seed path.  Future seeds are integrated out, and the first current
seed appears just once in the one completed batch. -/
theorem tracker_stoppedWeight_actual_integral_eq
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar lam : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T) (f : BatchHistory P d u → ℝ) (hf : Measurable f) :
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      f (batchHistoryOfRun P I.oracle u z) *
        Real.exp (lam * trackerIncrementOnHistory P I u
          (batchHistoryOfRun P I.oracle u z)
          (batchSeedBlock P u z.2))
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P)))) =
    ∫ z : BatchHistory P d u × (Fin P.n → Seed),
      f z.1 * Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2)
      ∂(batchPastHistoryLaw P I.oracle u).prod
        (freshSeedLaw I.oracle P.n) := by
  let globalLaw := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  let targetLaw := (batchPastHistoryLaw P I.oracle u).prod
    (freshSeedLaw I.oracle P.n)
  let pathMap : (Fin P.T × (Fin (responseCount P) → Seed)) →
      BatchHistory P d u × (Fin P.n → Seed) := fun z =>
    (batchHistoryOfRun P I.oracle u z, batchSeedBlock P u z.2)
  let g : BatchHistory P d u × (Fin P.n → Seed) → ℝ := fun z =>
    f z.1 * Real.exp (lam * trackerIncrementOnHistory P I u z.1 z.2)
  have hmap : MeasurePreserving pathMap globalLaw targetLaw :=
    measurePreserving_actualHistory_currentBatch P I.oracle u
  have hg : StronglyMeasurable g := by
    let x : BatchHistory P d u × (Fin P.n → Seed) → Point d :=
      fun z => batchDecision P u z.1
    let w : BatchHistory P d u × (Fin P.n → Seed) → Point d :=
      fun z => batchCenter P u z.1
    let estimate : BatchHistory P d u × (Fin P.n → Seed) → Point d :=
      fun z => batchEstimateOnHistory P I.oracle u z.1 z.2
    let y : BatchHistory P d u × (Fin P.n → Seed) → Point d :=
      fun z => I.oracle.response (x z) (z.2 ⟨0, P.n_pos⟩)
    have hx : Measurable x :=
      (measurable_batchDecision P u).comp measurable_fst
    have hw : Measurable w :=
      (measurable_batchCenter P u).comp measurable_fst
    have hestimate : Measurable estimate :=
      measurable_batchEstimateOnHistory P I.oracle u
    have hfirst : Measurable
        (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
          z.2 ⟨0, P.n_pos⟩) :=
      (measurable_pi_apply (⟨0, P.n_pos⟩ : Fin P.n)).comp measurable_snd
    have hy : Measurable y :=
      I.oracle.measurable_response.comp (hx.prodMk hfirst)
    have hexplicit : Measurable (fun z => trackerError I
        (x z - P.h • direction (estimate z))
        (coarseCenter P (w z) (y z)) - trackerError I (x z) (w z)) :=
      measurable_trackerIncrement_composition P
        (fun a : Point d × Point d => trackerError I a.1 a.2)
        (measurable_trackerError I)
        x w estimate y hx hw hestimate hy
    have hfun : (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        trackerIncrementOnHistory P I u z.1 z.2) =
      (fun z => trackerError I
        (x z - P.h • direction (estimate z))
        (coarseCenter P (w z) (y z)) - trackerError I (x z) (w z)) := by
      funext z
      rw [trackerIncrementOnHistory]
    have hχ : Measurable (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        trackerIncrementOnHistory P I u z.1 z.2) := by
      rw [hfun]
      exact hexplicit
    exact ((hf.comp measurable_fst).mul
      (Real.measurable_exp.comp (measurable_const.mul hχ))).stronglyMeasurable
  change (∫ z, g (pathMap z) ∂globalLaw) = (∫ z, g z ∂targetLaw)
  rw [← hmap.map_eq]
  exact (integral_map_of_stronglyMeasurable hmap.measurable hg).symm

end

end HeavyTailedNoise.UpperK1
