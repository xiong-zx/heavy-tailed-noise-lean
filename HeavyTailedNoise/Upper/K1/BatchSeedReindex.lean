import HeavyTailedNoise.Upper.K1.BatchSeedProduct

/-!
The current-batch strict seed interval is exactly `Fin P.n`. Reindexing its
independent product measure gives the `freshSeedLaw O P.n` interface used by
the whole-batch conditional expectation lemmas.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Global current-batch coordinate `batchStart + j`, with its strict past and
future boundary proofs. -/
def currentSeedIndexOfFin (u : Fin P.T) (j : Fin P.n) : CurrentSeedIndex P u :=
  ⟨⟨batchResponseIndex P u j,
      Nat.not_lt.mpr (batchResponseIndex_ge_start P u j)⟩,
    batchResponseIndex_lt_end P u j⟩

def currentSeedIndexToFin (u : Fin P.T) (i : CurrentSeedIndex P u) : Fin P.n :=
  ⟨i.1.1.val - batchStart P u.val, by
    have hstart : batchStart P u.val ≤ i.1.1.val :=
      Nat.le_of_not_gt i.1.2
    have hend : i.1.1.val < batchStart P u.val + P.n := i.2
    omega⟩

/-- The middle subtype interval in the three-way product split is neither
larger nor smaller than one runtime batch. -/
def currentSeedIndexEquiv (u : Fin P.T) : Fin P.n ≃ CurrentSeedIndex P u where
  toFun := currentSeedIndexOfFin P u
  invFun := currentSeedIndexToFin P u
  left_inv := by
    intro j
    apply Fin.ext
    dsimp [currentSeedIndexOfFin, currentSeedIndexToFin, batchResponseIndex]
    omega
  right_inv := by
    intro i
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    dsimp [currentSeedIndexOfFin, currentSeedIndexToFin, batchResponseIndex]
    have hstart : batchStart P u.val ≤ i.1.1.val :=
      Nat.le_of_not_gt i.1.2
    omega

/-- Reexpress the current-batch subtype function as the literal `Fin P.n`
fresh-seed block. -/
def reindexCurrentSeedBlock {Seed : Type*} [MeasurableSpace Seed]
    (u : Fin P.T) (block : CurrentSeedIndex P u → Seed) : Fin P.n → Seed :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin P.n => Seed)
    (currentSeedIndexEquiv P u).symm block

/-- No law changes under the finite coordinate bijection: this is exactly the
batch seed measure expected by `ClippedBatch`. -/
theorem measurePreserving_reindexCurrentSeedBlock {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (u : Fin P.T) :
    MeasurePreserving (reindexCurrentSeedBlock (Seed := Seed) P u)
      (Measure.pi (fun _ : CurrentSeedIndex P u => O.law))
      (freshSeedLaw O P.n) := by
  classical
  letI : IsProbabilityMeasure O.law := O.law_probability
  change MeasurePreserving
    (MeasurableEquiv.piCongrLeft (fun _ : Fin P.n => Seed)
      (currentSeedIndexEquiv P u).symm)
    (Measure.pi (fun _ : CurrentSeedIndex P u => O.law))
    (Measure.pi (fun _ : Fin P.n => O.law))
  exact measurePreserving_piCongrLeft
    (α := fun _ : Fin P.n => Seed)
    (μ := fun _ : Fin P.n => O.law)
    (currentSeedIndexEquiv P u).symm

/-- Reindexing the middle factor of the canonical three-way split returns
the same coordinate tuple used in actual logged responses. -/
theorem reindex_split_current_eq_batchSeedBlock {Seed : Type*}
    [MeasurableSpace Seed] (u : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) :
    reindexCurrentSeedBlock P u (splitBatchSeedPath P u seeds).2.1 =
      batchSeedBlock P u seeds := by
  funext j
  have hcoord := MeasurableEquiv.piCongrLeft_apply_apply
    (e := (currentSeedIndexEquiv P u).symm)
    (β := fun _ : Fin P.n => Seed)
    (x := (splitBatchSeedPath P u seeds).2.1)
    (i := currentSeedIndexEquiv P u j)
  simp only [Equiv.symm_apply_apply] at hcoord
  calc
    reindexCurrentSeedBlock P u (splitBatchSeedPath P u seeds).2.1 j =
        (splitBatchSeedPath P u seeds).2.1 (currentSeedIndexEquiv P u j) := by
          simpa only [reindexCurrentSeedBlock] using hcoord
    _ = batchSeedBlock P u seeds j := rfl

end

end HeavyTailedNoise.UpperK1
