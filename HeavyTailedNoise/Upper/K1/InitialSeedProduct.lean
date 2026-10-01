import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialLoggedBatch

/-!
The full fresh tape splits into the first seed, the optional initialization
block, and all runtime seeds. The middle factor is the same `initialSeedBlock`
used by the literal algorithm. Empty initialization is handled by `Fin 0`.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

private def firstRuntimeBatch : Fin P.T := ⟨0, P.T_pos⟩

abbrev FirstPastSeedIndex :=
  {i : PastSeedIndex P (firstRuntimeBatch P) // i.1.val = 0}

abbrev InitialPastSeedIndex :=
  {i : PastSeedIndex P (firstRuntimeBatch P) // i.1.val ≠ 0}

private def firstPastIndex : FirstPastSeedIndex P :=
  ⟨⟨⟨0, responseCount_pos P⟩, by
      dsimp [batchStart]
      omega⟩, rfl⟩

/-- The strict part of the first runtime past after seed zero has exactly
`initialResponses P` coordinates, even when that number is zero. -/
def initialPastIndexEquiv :
    Fin (initialResponses P) ≃ InitialPastSeedIndex P where
  toFun i := ⟨⟨initialSeedIndex P i, by
      dsimp [initialSeedIndex, batchStart]
      omega⟩, by
        dsimp [initialSeedIndex]
        omega⟩
  invFun i := ⟨i.1.1.val - 1, by
    have hbound := i.1.2
    have hnonzero := i.2
    have hstart : batchStart P (firstRuntimeBatch P).val =
        1 + initialResponses P := by
      simp [firstRuntimeBatch, batchStart]
    have hbound' : i.1.1.val < 1 + initialResponses P := by
      calc
        i.1.1.val < batchStart P (firstRuntimeBatch P).val := hbound
        _ = 1 + initialResponses P := hstart
    change i.1.1.val ≠ 0 at hnonzero
    omega⟩
  left_inv := by
    intro i
    apply Fin.ext
    dsimp [initialSeedIndex]
    omega
  right_inv := by
    intro i
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    have hnonzero := i.2
    dsimp [initialSeedIndex]
    omega

/-- The complement of the strict pre-runtime past is precisely the complete
runtime seed tape, not just its first batch. -/
def runtimeSeedIndexEquiv :
    Fin (P.T * P.n) ≃ LaterSeedIndex P (firstRuntimeBatch P) where
  toFun j := ⟨⟨batchStart P 0 + j.val, by
      have hj := j.isLt
      dsimp [batchStart, responseCount]
      omega⟩, by
        change ¬ batchStart P 0 + j.val < batchStart P 0
        omega⟩
  invFun i := ⟨i.1.val - batchStart P 0, by
    have hstart : batchStart P 0 ≤ i.1.val := Nat.le_of_not_gt i.2
    have hend := i.1.isLt
    dsimp [batchStart, responseCount] at hstart hend ⊢
    omega⟩
  left_inv := by
    intro j
    apply Fin.ext
    dsimp
    omega
  right_inv := by
    intro i
    apply Subtype.ext
    apply Fin.ext
    have hstart : batchStart P 0 ≤ i.1.val := Nat.le_of_not_gt i.2
    dsimp
    omega

private def reindexInitialPast {Seed : Type*} [MeasurableSpace Seed]
    (block : InitialPastSeedIndex P → Seed) :
    Fin (initialResponses P) → Seed :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin (initialResponses P) => Seed)
    (initialPastIndexEquiv P).symm block

private def reindexRuntime {Seed : Type*} [MeasurableSpace Seed]
    (block : LaterSeedIndex P (firstRuntimeBatch P) → Seed) :
    Fin (P.T * P.n) → Seed :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin (P.T * P.n) => Seed)
    (runtimeSeedIndexEquiv P).symm block

private def splitFirstPast {Seed : Type*} [MeasurableSpace Seed]
    (past : PastSeedIndex P (firstRuntimeBatch P) → Seed) :
    Seed × (Fin (initialResponses P) → Seed) :=
  let parts := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : PastSeedIndex P (firstRuntimeBatch P) => Seed)
    (fun i => i.1.val = 0) past
  (parts.1 (firstPastIndex P), reindexInitialPast P parts.2)

/-- Canonical three-block reindexing of the single global fresh tape. -/
def splitInitialSeedPath {Seed : Type*} [MeasurableSpace Seed]
    (seeds : Fin (responseCount P) → Seed) :
    (Seed × (Fin (initialResponses P) → Seed)) ×
      (Fin (P.T * P.n) → Seed) :=
  let parts := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (responseCount P) => Seed)
    (fun i => i.val < batchStart P 0) seeds
  (splitFirstPast P parts.1, reindexRuntime P parts.2)

theorem splitInitialSeedPath_first {Seed : Type*} [MeasurableSpace Seed]
    (seeds : Fin (responseCount P) → Seed) :
    (splitInitialSeedPath P seeds).1.1 =
      seeds ⟨0, responseCount_pos P⟩ := rfl

theorem splitInitialSeedPath_initial {Seed : Type*} [MeasurableSpace Seed]
    (seeds : Fin (responseCount P) → Seed) :
    (splitInitialSeedPath P seeds).1.2 = initialSeedBlock P seeds := by
  funext i
  have hcoord := MeasurableEquiv.piCongrLeft_apply_apply
    (e := (initialPastIndexEquiv P).symm)
    (β := fun _ : Fin (initialResponses P) => Seed)
    (x := (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : PastSeedIndex P (firstRuntimeBatch P) => Seed)
      (fun j => j.1.val = 0)
      ((MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : Fin (responseCount P) => Seed)
        (fun j => j.val < batchStart P 0) seeds).1)).2)
    (i := initialPastIndexEquiv P i)
  simp only [Equiv.symm_apply_apply] at hcoord
  calc
    (splitInitialSeedPath P seeds).1.2 i =
        (MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : PastSeedIndex P (firstRuntimeBatch P) => Seed)
          (fun j => j.1.val = 0)
          ((MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : Fin (responseCount P) => Seed)
            (fun j => j.val < batchStart P 0) seeds).1)).2
              (initialPastIndexEquiv P i) := by
                simpa only [splitInitialSeedPath, splitFirstPast,
                  reindexInitialPast] using hcoord
    _ = initialSeedBlock P seeds i := rfl

/-- Runtime coordinate `j` is the global response coordinate immediately
after seed zero and all optional initialization responses. -/
theorem splitInitialSeedPath_runtime {Seed : Type*} [MeasurableSpace Seed]
    (seeds : Fin (responseCount P) → Seed) (j : Fin (P.T * P.n)) :
    (splitInitialSeedPath P seeds).2 j =
      seeds (runtimeSeedIndexEquiv P j).1 := by
  have hcoord := MeasurableEquiv.piCongrLeft_apply_apply
    (e := (runtimeSeedIndexEquiv P).symm)
    (β := fun _ : Fin (P.T * P.n) => Seed)
    (x := (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (responseCount P) => Seed)
      (fun i => i.val < batchStart P 0) seeds).2)
    (i := runtimeSeedIndexEquiv P j)
  simp only [Equiv.symm_apply_apply] at hcoord
  calc
    (splitInitialSeedPath P seeds).2 j =
        (MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : Fin (responseCount P) => Seed)
          (fun i => i.val < batchStart P 0) seeds).2
          (runtimeSeedIndexEquiv P j) := by
            simpa only [splitInitialSeedPath, reindexRuntime] using hcoord
    _ = seeds (runtimeSeedIndexEquiv P j).1 := rfl

theorem measurePreserving_splitInitialSeedPath {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) :
    MeasurePreserving (splitInitialSeedPath (Seed := Seed) P)
      (freshSeedLaw O (responseCount P))
      ((O.law.prod (freshSeedLaw O (initialResponses P))).prod
        (freshSeedLaw O (P.T * P.n))) := by
  classical
  letI : IsProbabilityMeasure O.law := O.law_probability
  let μpast := Measure.pi
    (fun _ : PastSeedIndex P (firstRuntimeBatch P) => O.law)
  let μruntime := Measure.pi
    (fun _ : LaterSeedIndex P (firstRuntimeBatch P) => O.law)
  let μfirst := Measure.pi (fun _ : FirstPastSeedIndex P => O.law)
  let μinitial := Measure.pi (fun _ : InitialPastSeedIndex P => O.law)
  let firstSplit := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : PastSeedIndex P (firstRuntimeBatch P) => Seed)
    (fun i => i.1.val = 0)
  let fullSplit := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (responseCount P) => Seed)
    (fun i => i.val < batchStart P 0)
  have hfull : MeasurePreserving fullSplit
      (freshSeedLaw O (responseCount P)) (μpast.prod μruntime) := by
    change MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : Fin (responseCount P) => Seed)
        (fun i => i.val < batchStart P 0))
      (Measure.pi (fun _ : Fin (responseCount P) => O.law))
      ((Measure.pi (fun _ : {i : Fin (responseCount P) //
        i.val < batchStart P 0} => O.law)).prod
        (Measure.pi (fun _ : {i : Fin (responseCount P) //
          ¬ i.val < batchStart P 0} => O.law)))
    exact measurePreserving_piEquivPiSubtypeProd
      (α := fun _ : Fin (responseCount P) => Seed)
      (μ := fun _ : Fin (responseCount P) => O.law)
      (fun i => i.val < batchStart P 0)
  have hpast : MeasurePreserving firstSplit μpast
      (μfirst.prod μinitial) := by
    change MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : PastSeedIndex P (firstRuntimeBatch P) => Seed)
        (fun i => i.1.val = 0))
      (Measure.pi
        (fun _ : PastSeedIndex P (firstRuntimeBatch P) => O.law))
      ((Measure.pi (fun _ : {i : PastSeedIndex P (firstRuntimeBatch P) //
        i.1.val = 0} => O.law)).prod
        (Measure.pi (fun _ : {i : PastSeedIndex P (firstRuntimeBatch P) //
          ¬ i.1.val = 0} => O.law)))
    exact measurePreserving_piEquivPiSubtypeProd
      (α := fun _ : PastSeedIndex P (firstRuntimeBatch P) => Seed)
      (μ := fun _ : PastSeedIndex P (firstRuntimeBatch P) => O.law)
      (fun i => i.1.val = 0)
  have heval : MeasurePreserving
      (fun block : FirstPastSeedIndex P → Seed => block (firstPastIndex P))
      μfirst O.law := by
    simpa only [μfirst] using
      (measurePreserving_eval
        (fun _ : FirstPastSeedIndex P => O.law) (firstPastIndex P))
  have hinit : MeasurePreserving (reindexInitialPast (Seed := Seed) P)
      μinitial (freshSeedLaw O (initialResponses P)) := by
    change MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (initialResponses P) => Seed)
        (initialPastIndexEquiv P).symm)
      (Measure.pi (fun _ : InitialPastSeedIndex P => O.law))
      (Measure.pi (fun _ : Fin (initialResponses P) => O.law))
    exact measurePreserving_piCongrLeft
      (α := fun _ : Fin (initialResponses P) => Seed)
      (μ := fun _ : Fin (initialResponses P) => O.law)
      (initialPastIndexEquiv P).symm
  have hruntime : MeasurePreserving (reindexRuntime (Seed := Seed) P)
      μruntime (freshSeedLaw O (P.T * P.n)) := by
    change MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (P.T * P.n) => Seed)
        (runtimeSeedIndexEquiv P).symm)
      (Measure.pi
        (fun _ : LaterSeedIndex P (firstRuntimeBatch P) => O.law))
      (Measure.pi (fun _ : Fin (P.T * P.n) => O.law))
    exact measurePreserving_piCongrLeft
      (α := fun _ : Fin (P.T * P.n) => Seed)
      (μ := fun _ : Fin (P.T * P.n) => O.law)
      (runtimeSeedIndexEquiv P).symm
  have hfirstPart := (heval.prod hinit).comp hpast
  have hproduct := hfirstPart.prod hruntime
  have hresult := hproduct.comp hfull
  have hfun : ((Prod.map (splitFirstPast (Seed := Seed) P)
      (reindexRuntime (Seed := Seed) P)) ∘ fullSplit) =
      splitInitialSeedPath (Seed := Seed) P := by
    funext seeds
    rfl
  rw [← hfun]
  exact hresult

/-- The two factors consumed by initialization have their exact original
product law. Runtime seeds are simply marginalized from the three-way split. -/
theorem measurePreserving_first_initialSeedBlock {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) :
    MeasurePreserving
      (fun seeds : Fin (responseCount P) → Seed =>
        (seeds ⟨0, responseCount_pos P⟩, initialSeedBlock P seeds))
      (freshSeedLaw O (responseCount P))
      (O.law.prod (freshSeedLaw O (initialResponses P))) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw O (initialResponses P)) :=
    freshSeedLaw_probability O (initialResponses P)
  letI : IsProbabilityMeasure (freshSeedLaw O (P.T * P.n)) :=
    freshSeedLaw_probability O (P.T * P.n)
  have hdrop : MeasurePreserving
      (Prod.fst :
        ((Seed × (Fin (initialResponses P) → Seed)) ×
          (Fin (P.T * P.n) → Seed)) →
          (Seed × (Fin (initialResponses P) → Seed)))
      ((O.law.prod (freshSeedLaw O (initialResponses P))).prod
        (freshSeedLaw O (P.T * P.n)))
      (O.law.prod (freshSeedLaw O (initialResponses P))) :=
    measurePreserving_fst
  have h := hdrop.comp (measurePreserving_splitInitialSeedPath P O)
  have hfun : (Prod.fst ∘ splitInitialSeedPath (Seed := Seed) P) =
      (fun seeds : Fin (responseCount P) → Seed =>
        (seeds ⟨0, responseCount_pos P⟩, initialSeedBlock P seeds)) := by
    funext seeds
    exact Prod.ext (splitInitialSeedPath_first P seeds)
      (splitInitialSeedPath_initial P seeds)
  rw [← hfun]
  exact h

end

end HeavyTailedNoise.UpperK1
