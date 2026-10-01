import HeavyTailedNoise.Upper.K1.BatchPastMeasurability
import HeavyTailedNoise.Upper.K1.BatchSeedReindex

/-!
The exact joint product law of the full pre-batch history and one fresh
runtime batch. The initial private output index remains arbitrary and
independent; no current-batch response enters the pre-batch factor.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Forget the future coordinates after the canonical three-way seed split,
and reindex the middle factor as the literal `Fin P.n` fresh batch. -/
def splitPastCurrentSeedPath {Seed : Type*} [MeasurableSpace Seed]
    (u : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    (PastSeedIndex P u → Seed) × (Fin P.n → Seed) :=
  ((splitBatchSeedPath P u seeds).1,
    reindexCurrentSeedBlock P u (splitBatchSeedPath P u seeds).2.1)

theorem measurePreserving_splitPastCurrentSeedPath {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (u : Fin P.T) :
    MeasurePreserving (splitPastCurrentSeedPath (Seed := Seed) P u)
      (freshSeedLaw O (responseCount P))
      ((Measure.pi (fun _ : PastSeedIndex P u => O.law)).prod
        (freshSeedLaw O P.n)) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  let μpast := Measure.pi (fun _ : PastSeedIndex P u => O.law)
  let μcurrent := Measure.pi (fun _ : CurrentSeedIndex P u => O.law)
  let μfuture := Measure.pi (fun _ : FutureSeedIndex P u => O.law)
  letI : IsProbabilityMeasure μpast := by
    dsimp [μpast]
    infer_instance
  letI : IsProbabilityMeasure μcurrent := by
    dsimp [μcurrent]
    infer_instance
  letI : IsProbabilityMeasure μfuture := by
    dsimp [μfuture]
    infer_instance
  letI : IsProbabilityMeasure (freshSeedLaw O (responseCount P)) :=
    freshSeedLaw_probability O (responseCount P)
  have hdrop : MeasurePreserving
      (Prod.map id Prod.fst)
      (μpast.prod (μcurrent.prod μfuture))
      (μpast.prod μcurrent) :=
    (MeasurePreserving.id μpast).prod
      (measurePreserving_fst (μ := μcurrent) (ν := μfuture))
  have hsplit := measurePreserving_splitBatchSeedPath P O u
  have hcurrent := measurePreserving_reindexCurrentSeedBlock P O u
  have hreindex : MeasurePreserving
      (Prod.map id (reindexCurrentSeedBlock P u))
      (μpast.prod μcurrent)
      (μpast.prod (freshSeedLaw O P.n)) :=
    (MeasurePreserving.id μpast).prod hcurrent
  have hfull := hreindex.comp (hdrop.comp hsplit)
  have hfun : ((Prod.map id (reindexCurrentSeedBlock (Seed := Seed) P u)) ∘
      ((Prod.map id Prod.fst) ∘ splitBatchSeedPath (Seed := Seed) P u)) =
      splitPastCurrentSeedPath (Seed := Seed) P u := by
    funext seeds
    rfl
  rw [← hfun]
  exact hfull

/-- The private index and strict past seeds form one factor, while the entire
current batch has its original iid law as the other factor. -/
def splitPrivatePastCurrent {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    (Fin P.T × (PastSeedIndex P u → Seed)) × (Fin P.n → Seed) :=
  ((z.1, (splitPastCurrentSeedPath P u z.2).1),
    (splitPastCurrentSeedPath P u z.2).2)

theorem measurePreserving_splitPrivatePastCurrent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u : Fin P.T) :
    MeasurePreserving (splitPrivatePastCurrent (d := d) (Seed := Seed) P u)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))
      (((algorithm (d := d) P).privateLaw.prod
        (Measure.pi (fun _ : PastSeedIndex P u => O.law))).prod
          (freshSeedLaw O P.n)) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  let μprivate := (algorithm (d := d) P).privateLaw
  let μpast := Measure.pi (fun _ : PastSeedIndex P u => O.law)
  let μbatch := freshSeedLaw O P.n
  letI : IsProbabilityMeasure μprivate := (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure μpast := by
    dsimp [μpast]
    infer_instance
  letI : IsProbabilityMeasure μbatch := freshSeedLaw_probability O P.n
  letI : IsProbabilityMeasure (freshSeedLaw O (responseCount P)) :=
    freshSeedLaw_probability O (responseCount P)
  have hseed := measurePreserving_splitPastCurrentSeedPath P O u
  have hprivate : MeasurePreserving
      (Prod.map id (splitPastCurrentSeedPath P u))
      (μprivate.prod (freshSeedLaw O (responseCount P)))
      (μprivate.prod (μpast.prod μbatch)) :=
    (MeasurePreserving.id μprivate).prod hseed
  have hassoc := measurePreserving_prodAssoc μprivate μpast μbatch
  have hassocInv := MeasurePreserving.symm
    (MeasurableEquiv.prodAssoc :
      ((Fin P.T × (PastSeedIndex P u → Seed)) × (Fin P.n → Seed)) ≃ᵐ
        (Fin P.T × ((PastSeedIndex P u → Seed) × (Fin P.n → Seed)))) hassoc
  have hfull := hassocInv.comp hprivate
  have hfun : ((MeasurableEquiv.prodAssoc.symm :
      (Fin P.T × ((PastSeedIndex P u → Seed) × (Fin P.n → Seed))) ≃ᵐ
        ((Fin P.T × (PastSeedIndex P u → Seed)) × (Fin P.n → Seed))) ∘
      (Prod.map id (splitPastCurrentSeedPath P u))) =
      splitPrivatePastCurrent (d := d) (Seed := Seed) P u := by
    funext z
    rfl
  rw [← hfun]
  exact hfull

/-- Distribution of all information available before runtime batch `u`.
This is a pushforward of the independent private index and strict past seeds. -/
def batchPastHistoryLaw {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u : Fin P.T) :
    Measure (BatchHistory P d u) :=
  Measure.map (batchHistoryFromPast P O u)
    ((algorithm (d := d) P).privateLaw.prod
      (Measure.pi (fun _ : PastSeedIndex P u => O.law)))

/-- The actual pre-batch history and current iid batch jointly have exactly
the product law required by the full-batch conditional-expectation theorems. -/
theorem measurePreserving_actualHistory_currentBatch
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u : Fin P.T) :
    MeasurePreserving
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        (batchHistoryOfRun P O u z, batchSeedBlock P u z.2))
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))
      ((batchPastHistoryLaw P O u).prod (freshSeedLaw O P.n)) := by
  let μpastPrivate := (algorithm (d := d) P).privateLaw.prod
    (Measure.pi (fun _ : PastSeedIndex P u => O.law))
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure μpastPrivate := by
    dsimp [μpastPrivate]
    infer_instance
  letI : IsProbabilityMeasure (freshSeedLaw O P.n) :=
    freshSeedLaw_probability O P.n
  have hhistory : MeasurePreserving (batchHistoryFromPast P O u)
      μpastPrivate (batchPastHistoryLaw P O u) :=
    ⟨measurable_batchHistoryFromPast P O u, rfl⟩
  have hbatch : MeasurePreserving (id : (Fin P.n → Seed) → (Fin P.n → Seed))
      (freshSeedLaw O P.n) (freshSeedLaw O P.n) :=
    MeasurePreserving.id _
  have hproduct := hhistory.prod hbatch
  have hsplit := measurePreserving_splitPrivatePastCurrent P O u
  have hfull := hproduct.comp hsplit
  have hpath (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      (batchHistoryFromPast P O u
          (splitPrivatePastCurrent (d := d) P u z).1,
        (splitPrivatePastCurrent (d := d) P u z).2) =
      (batchHistoryOfRun P O u z, batchSeedBlock P u z.2) := by
    apply Prod.ext
    · simpa only [splitPrivatePastCurrent, splitPastCurrentSeedPath] using
        (batchHistoryOfRun_eq_fromPast P O u z.1 z.2).symm
    · simpa only [splitPrivatePastCurrent, splitPastCurrentSeedPath] using
        (reindex_split_current_eq_batchSeedBlock P u z.2)
  have hfun : ((Prod.map (batchHistoryFromPast P O u) id) ∘
      splitPrivatePastCurrent (d := d) P u) =
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        (batchHistoryOfRun P O u z, batchSeedBlock P u z.2)) := by
    funext z
    exact hpath z
  rw [← hfun]
  exact hfull

end

end HeavyTailedNoise.UpperK1
