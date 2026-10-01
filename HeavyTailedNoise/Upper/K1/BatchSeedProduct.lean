import HeavyTailedNoise.Upper.K1.BatchPathFiltration

/-!
Exact product-law splitting of one global seed path at a runtime batch. The
split is made once at the batch boundary: past, all current-batch seeds, and
future. No current response enters the past sigma-field.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

abbrev PastSeedIndex (u : Fin P.T) :=
  {i : Fin (responseCount P) // i.val < batchStart P u.val}

abbrev LaterSeedIndex (u : Fin P.T) :=
  {i : Fin (responseCount P) // ¬ i.val < batchStart P u.val}

abbrev CurrentSeedIndex (u : Fin P.T) :=
  {i : LaterSeedIndex P u // i.1.val < batchStart P u.val + P.n}

abbrev FutureSeedIndex (u : Fin P.T) :=
  {i : LaterSeedIndex P u // ¬ i.1.val < batchStart P u.val + P.n}

/-- The canonical measurable equivalence splits the seed coordinates at the
two strict batch boundaries. The middle component contains exactly the
current batch; its `Fin P.n` reindexing is established separately below. -/
def splitBatchSeedPath {Seed : Type*} [MeasurableSpace Seed]
    (u : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    (PastSeedIndex P u → Seed) ×
      (CurrentSeedIndex P u → Seed) × (FutureSeedIndex P u → Seed) := by
  classical
  let past := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (responseCount P) => Seed)
    (fun i => i.val < batchStart P u.val)
  let current := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : LaterSeedIndex P u => Seed)
    (fun i => i.1.val < batchStart P u.val + P.n)
  exact ((past seeds).1, current (past seeds).2)

/-- The iid global response seeds factor exactly into independent past,
current-batch, and future blocks. This uses mathlib's finite-`pi` measurable
equivalence twice; no independence is assumed in addition to `freshSeedLaw`. -/
theorem measurePreserving_splitBatchSeedPath {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (u : Fin P.T) :
    MeasurePreserving (splitBatchSeedPath (Seed := Seed) P u)
      (freshSeedLaw O (responseCount P))
      ((Measure.pi (fun _ : PastSeedIndex P u => O.law)).prod
        ((Measure.pi (fun _ : CurrentSeedIndex P u => O.law)).prod
          (Measure.pi (fun _ : FutureSeedIndex P u => O.law)))) := by
  classical
  letI : IsProbabilityMeasure O.law := O.law_probability
  let past := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (responseCount P) => Seed)
    (fun i => i.val < batchStart P u.val)
  let current := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : LaterSeedIndex P u => Seed)
    (fun i => i.1.val < batchStart P u.val + P.n)
  have hpast : MeasurePreserving past
      (freshSeedLaw O (responseCount P))
      ((Measure.pi (fun _ : PastSeedIndex P u => O.law)).prod
        (Measure.pi (fun _ : LaterSeedIndex P u => O.law))) := by
    simpa only [past, freshSeedLaw, PastSeedIndex, LaterSeedIndex] using
      (measurePreserving_piEquivPiSubtypeProd
        (α := fun _ : Fin (responseCount P) => Seed)
        (μ := fun _ : Fin (responseCount P) => O.law)
        (fun i => i.val < batchStart P u.val))
  have hcurrent : MeasurePreserving current
      (Measure.pi (fun _ : LaterSeedIndex P u => O.law))
      ((Measure.pi (fun _ : CurrentSeedIndex P u => O.law)).prod
        (Measure.pi (fun _ : FutureSeedIndex P u => O.law))) := by
    simpa only [current, CurrentSeedIndex, FutureSeedIndex] using
      (measurePreserving_piEquivPiSubtypeProd
        (α := fun _ : LaterSeedIndex P u => Seed)
        (μ := fun _ : LaterSeedIndex P u => O.law)
        (fun i => i.1.val < batchStart P u.val + P.n))
  have hproduct :=
    (MeasurePreserving.id
      (Measure.pi (fun _ : PastSeedIndex P u => O.law))).prod hcurrent
  have hsplit := hproduct.comp hpast
  have hfun : ((Prod.map id current) ∘ past) =
      splitBatchSeedPath (Seed := Seed) P u := by
    funext seeds
    rfl
  rw [← hfun]
  exact hsplit

/-- Each logged response in the current batch is exactly one oracle response
at the fixed pre-batch decision, driven by the corresponding global fresh
seed. All `P.n` coordinates use distinct `batchResponseIndex` values. -/
theorem batch_logged_response_eq_oracle {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (r u : Fin P.T) (seeds : Fin (responseCount P) → Seed) (j : Fin P.n) :
    (runTranscript O (algorithm (d := d) P) r (responseCount P) seeds
      (batchResponseIndex P u j)).2 =
      O.response (batchDecision P u (batchHistoryOfRun P O u (r, seeds)))
        (batchSeedBlock P u seeds j) := by
  let k := batchResponseIndex P u j
  have hk : k.val + 1 ≤ responseCount P := Nat.succ_le_iff.mpr k.isLt
  let seedPrefix : Fin (k.val + 1) → Seed := fun i => seeds (i.castLE hk)
  have hprefix := runTranscript_prefix_le O (algorithm (d := d) P) r
    (k.val + 1) (responseCount P) hk seeds (Fin.last k.val)
  have hindex : (Fin.last k.val).castLE hk = k := Fin.ext rfl
  rw [hindex] at hprefix
  have hpair := hprefix.trans (algorithm_last_response P O r k.val seedPrefix)
  have hx := congrArg Prod.fst hpair
  have hy := congrArg Prod.snd hpair
  dsimp at hx hy
  have hseed : seedPrefix (Fin.last k.val) = seeds k := by
    change seeds ((Fin.last k.val).castLE hk) = seeds k
    congr 1
  rw [hseed, ← hx] at hy
  rw [batch_logged_response_at_prebatch_decision P O r u seeds j] at hy
  simpa only [batchSeedBlock, k] using hy

end

end HeavyTailedNoise.UpperK1
