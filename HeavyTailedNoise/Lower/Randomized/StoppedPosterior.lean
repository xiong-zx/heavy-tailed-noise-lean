import HeavyTailedNoise.Lower.Randomized.StoppedRecord
import HeavyTailedNoise.Lower.Randomized.TailKernel
import HeavyTailedNoise.Lower.Randomized.ReflectionLimits

/-!
Actual conditional kernels of the absorbed Bernoulli record. The prior,
algorithm, private realization and seed tape in every declaration below are
the literal experiment from StoppedRecord, rather than a substitute kernel.

The initial kernel and the first observation update have no stochastic
invariance premise. The general one-step bridge explicitly retains its old
kernel symmetry input; it is not the completed multi-step lift theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

namespace HeavyTailedNoise.RandomizedLift

private theorem observedResidual_snoc_old {d n : ℕ}
    (v : Fin n → Point d) (q a : Point d) :
    observedResidual v (observedResidual (Fin.snoc v q) a) =
      observedResidual (Fin.snoc v q) a := by
  have hspan : Submodule.span ℝ (Set.range v) ≤
      Submodule.span ℝ (Set.range (Fin.snoc v q)) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc, by simp only [Fin.snoc_castSucc]⟩
  rw [observedResidual_eq_starProjection]
  apply Submodule.starProjection_eq_self_iff.mpr
  exact Submodule.orthogonal_le hspan (observedResidual_mem_orthogonal (Fin.snoc v q) a)

section ActualExperiment

variable {d N j k : ℕ} {Private : Type*} [MeasurableSpace Private]
variable (A : RandomAlgorithm d N Private) (r : Private)
variable {R : ℝ} (hR : 0 < R) (η : ℝ) (θ : unitInterval) (tape : ℕ → Bool)
variable (hT : j + k ≤ d)

def actualStoppedRecord {d N j k : ℕ} {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm d N Private) (r : Private) (R η : ℝ)
    (θ : unitInterval) (tape : ℕ → Bool) (t : ℕ)
    (u : {U : Fin (j + k) → Point d // Orthonormal ℝ U}) :
    StoppedRecord d (j + k) j t :=
  absorbedRecord A r R η θ tape (Nat.le_add_right j k) u.1 t

include hR in
@[fun_prop] theorem measurable_actualStoppedRecord (t : ℕ) :
    Measurable (actualStoppedRecord (j := j) (k := k) A r R η θ tape t) :=
  (measurable_absorbedRecord A r η θ tape hR (Nat.le_add_right j k) t).comp
    measurable_subtype_coe

def actualStoppedRecordLaw {d N j k : ℕ} {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm d N Private) (r : Private) {R : ℝ} (hR : 0 < R)
    (η : ℝ) (θ : unitInterval) (tape : ℕ → Bool) (hT : j + k ≤ d)
    (t : ℕ) : Measure (StoppedRecord d (j + k) j t) :=
  (preselectedOrthonormalFrameLaw d (j + k) hT).map
    (actualStoppedRecord A r R η θ tape t)

instance actualStoppedRecordLaw_probability (t : ℕ) :
    IsProbabilityMeasure (actualStoppedRecordLaw A r hR η θ tape hT t) := by
  unfold actualStoppedRecordLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_actualStoppedRecord A r hR η θ tape t).aemeasurable).2 inferInstance

def actualStoppedPosterior {d N j k : ℕ} {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm d N Private) (r : Private) {R : ℝ} (hR : 0 < R)
    (η : ℝ) (θ : unitInterval) (tape : ℕ → Bool) (hT : j + k ≤ d) (t : ℕ) :
    Kernel (StoppedRecord d (j + k) j t) (Fin (j + k) → Point d) :=
  condDistrib Subtype.val (actualStoppedRecord A r R η θ tape t)
    (preselectedOrthonormalFrameLaw d (j + k) hT)

instance actualStoppedPosterior_markov (t : ℕ) :
    IsMarkovKernel (actualStoppedPosterior A r hR η θ tape hT t) := by
  unfold actualStoppedPosterior
  infer_instance

/-- Factorization of the actual record/frame joint law, at every finite time. -/
theorem actualStoppedRecord_joint (t : ℕ) :
    (preselectedOrthonormalFrameLaw d (j + k) hT).map
      (fun u => (actualStoppedRecord A r R η θ tape t u, u.1)) =
      (actualStoppedRecordLaw A r hR η θ tape hT t) ⊗ₘ
        actualStoppedPosterior A r hR η θ tape hT t := by
  exact (compProd_map_condDistrib
    (measurable_actualStoppedRecord A r hR η θ tape t).aemeasurable
    measurable_subtype_coe.aemeasurable).symm

theorem actualStoppedPosterior_orthonormal (t : ℕ) :
    ∀ᵐ c ∂actualStoppedRecordLaw A r hR η θ tape hT t,
      ∀ᵐ U ∂actualStoppedPosterior A r hR η θ tape hT t c, Orthonormal ℝ U := by
  refine Measure.ae_ae_of_ae_compProd
    (μ := actualStoppedRecordLaw A r hR η θ tape hT t)
    (κ := actualStoppedPosterior A r hR η θ tape hT t)
    (p := fun p : StoppedRecord d (j + k) j t × (Fin (j + k) → Point d) =>
      Orthonormal ℝ p.2) ?_
  rw [← actualStoppedRecord_joint A r hR η θ tape hT t]
  apply (ae_map_iff
    ((measurable_actualStoppedRecord A r hR η θ tape t).prodMk
      measurable_subtype_coe).aemeasurable
    (measurable_snd (measurableSet_orthonormal_fin d (j + k)))).2
  exact Filter.Eventually.of_forall (fun u => u.2)

/-- Disintegration places the actual posterior on the recorded consistency
graph. All full hidden-coordinate projections are retained by this graph. -/
theorem actualStoppedPosterior_consistent (t : ℕ) :
    ∀ᵐ c ∂actualStoppedRecordLaw A r hR η θ tape hT t,
      ∀ᵐ U ∂actualStoppedPosterior A r hR η θ tape hT t c,
        recordPrefix t c = framePrefix (Nat.le_add_right j k) U ∧
          recordCoordinates t c = recordedProjections U (recordQueries t c) := by
  refine Measure.ae_ae_of_ae_compProd
    (μ := actualStoppedRecordLaw A r hR η θ tape hT t)
    (κ := actualStoppedPosterior A r hR η θ tape hT t)
    (p := fun p : StoppedRecord d (j + k) j t × (Fin (j + k) → Point d) =>
      recordPrefix t p.1 = framePrefix (Nat.le_add_right j k) p.2 ∧
        recordCoordinates t p.1 = recordedProjections p.2 (recordQueries t p.1)) ?_
  have hm : MeasurableSet
      {p : StoppedRecord d (j + k) j t × (Fin (j + k) → Point d) |
        recordPrefix t p.1 = framePrefix (Nat.le_add_right j k) p.2 ∧
          recordCoordinates t p.1 = recordedProjections p.2 (recordQueries t p.1)} := by
    exact (measurableSet_eq_fun
      ((measurable_recordPrefix d (j + k) j t).comp measurable_fst)
      ((measurable_framePrefix (Nat.le_add_right j k)).comp measurable_snd)).inter
      (measurableSet_eq_fun
        ((measurable_recordCoordinates d (j + k) j t).comp measurable_fst)
        ((measurable_recordedProjections d (j + k) t).comp
          (measurable_snd.prodMk
            ((measurable_recordQueries d (j + k) j t).comp measurable_fst))))
  rw [← actualStoppedRecord_joint A r hR η θ tape hT t]
  apply (ae_map_iff
    ((measurable_actualStoppedRecord A r hR η θ tape t).prodMk
      measurable_subtype_coe).aemeasurable hm).2
  exact Filter.Eventually.of_forall (fun u =>
    ⟨recordPrefix_absorbedRecord A r R η θ tape (Nat.le_add_right j k) u.1 t,
      recordCoordinates_absorbedRecord A r R η θ tape (Nat.le_add_right j k) u.1 t⟩)

/-- The starting actual RCD is the same-prior entire-frame completion kernel. -/
theorem actualStoppedPosterior_zero_ae_eq_completion :
    actualStoppedPosterior A r hR η θ tape hT 0
      =ᵐ[actualStoppedRecordLaw A r hR η θ tape hT 0] frameCompletionKernel d j k := by
  have h := preselectedOrthonormalFrameLaw_completion_hasCondDistrib d j k hT
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (measurable_actualStoppedRecord A r hR η θ tape 0) measurable_subtype_coe h.map_eq

/-- One common conull starting set works for every prefix stabilizer rotation. -/
theorem actualStoppedPosterior_zero_stabilizer :
    ∀ᵐ v ∂actualStoppedRecordLaw A r hR η θ tape hT 0,
      ∀ W : Point d ≃ₗᵢ[ℝ] Point d,
        (∀ i : Fin j, W (v i) = v i) →
        (actualStoppedPosterior A r hR η θ tape hT 0 v).map (frameAction W) =
          actualStoppedPosterior A r hR η θ tape hT 0 v := by
  filter_upwards [actualStoppedPosterior_zero_ae_eq_completion A r hR η θ tape hT]
    with v hv
  intro W hW
  rw [hv]
  exact frameCompletionKernel_stabilizer_invariant d j k W v hW

/-- The actual next joint experiment is the old actual joint law with the
predictable bounded-query observation adjoined. -/
theorem actualStoppedRecord_successor_joint (t : ℕ) :
    ((actualStoppedRecordLaw A r hR η θ tape hT t) ⊗ₘ
      actualStoppedPosterior A r hR η θ tape hT t).map
        (fun p => ((p.1, stoppedObservation A r R η θ tape t p), p.2)) =
      (preselectedOrthonormalFrameLaw d (j + k) hT).map
        (fun u => (actualStoppedRecord A r R η θ tape (t + 1) u, u.1)) := by
  rw [← actualStoppedRecord_joint A r hR η θ tape hT t,
    Measure.map_map]
  · rfl
  · exact (measurable_fst.prodMk
      (measurable_stoppedObservation A r η θ tape hR t)).prodMk measurable_snd
  · exact (measurable_actualStoppedRecord A r hR η θ tape t).prodMk
      measurable_subtype_coe

theorem actualStoppedRecord_successor_marginal (t : ℕ) :
    ((actualStoppedRecordLaw A r hR η θ tape hT t) ⊗ₘ
      actualStoppedPosterior A r hR η θ tape hT t).map
        (fun p => (p.1, stoppedObservation A r R η θ tape t p)) =
      actualStoppedRecordLaw A r hR η θ tape hT (t + 1) := by
  rw [← actualStoppedRecord_joint A r hR η θ tape hT t, Measure.map_map]
  · rfl
  · exact measurable_fst.prodMk (measurable_stoppedObservation A r η θ tape hR t)
  · exact (measurable_actualStoppedRecord A r hR η θ tape t).prodMk
      measurable_subtype_coe

theorem actualStoppedRecord_successor_query (t : ℕ) :
    ∀ᵐ c ∂actualStoppedRecordLaw A r hR η θ tape hT (t + 1),
      c.2.1 = stoppedQuery A r R η θ tape t c.1 := by
  apply (ae_map_iff (measurable_actualStoppedRecord A r hR η θ tape (t + 1)).aemeasurable
    (measurableSet_eq_fun measurable_snd.fst
      ((measurable_stoppedQuery A r η θ tape hR t).comp measurable_fst))).2
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- RCD identification after the genuine predictable observation; no candidate
posterior or replacement prior is used in this identity. -/
theorem actualStoppedPosterior_successor (t : ℕ) :
    let q := actualStoppedRecordLaw A r hR η θ tape hT t
    let κ := actualStoppedPosterior A r hR η θ tape hT t
    let X : StoppedRecord d (j + k) j t × (Fin (j + k) → Point d) →
        StoppedRecord d (j + k) j (t + 1) :=
      fun p => (p.1, stoppedObservation A r R η θ tape t p)
    condDistrib Prod.snd X (q ⊗ₘ κ)
      =ᵐ[actualStoppedRecordLaw A r hR η θ tape hT (t + 1)]
        actualStoppedPosterior A r hR η θ tape hT (t + 1) := by
  dsimp only
  let P := preselectedOrthonormalFrameLaw d (j + k) hT
  let C := actualStoppedRecord (j := j) (k := k) A r R η θ tape t
  let f := fun u : {U : Fin (j + k) → Point d // Orthonormal ℝ U} => (C u, u.1)
  let X := fun p : StoppedRecord d (j + k) j t × (Fin (j + k) → Point d) =>
    (p.1, stoppedObservation A r R η θ tape t p)
  have hf : Measurable f :=
    (measurable_actualStoppedRecord A r hR η θ tape t).prodMk measurable_subtype_coe
  have hX : Measurable X := measurable_fst.prodMk
    (measurable_stoppedObservation A r η θ tape hR t)
  have hmap := condDistrib_map (ν := P) (f := f) (X := X) (Y := Prod.snd)
    hX.aemeasurable measurable_snd.aemeasurable hf.aemeasurable
  have hjoint : P.map f =
      (actualStoppedRecordLaw A r hR η θ tape hT t) ⊗ₘ
        actualStoppedPosterior A r hR η θ tape hT t :=
    actualStoppedRecord_joint A r hR η θ tape hT t
  have hXf : X ∘ f = actualStoppedRecord (j := j) (k := k) A r R η θ tape (t + 1) := by
    funext u
    rfl
  have hYf : Prod.snd ∘ f =
      (Subtype.val : {U : Fin (j + k) → Point d // Orthonormal ℝ U} → _) := rfl
  have hmarg : P.map (actualStoppedRecord (j := j) (k := k) A r R η θ tape (t + 1)) =
      actualStoppedRecordLaw A r hR η θ tape hT (t + 1) := rfl
  simpa only [hjoint, hXf, hYf, hmarg, actualStoppedPosterior, P, X] using hmap

/-- A rotation fixing the bounded query preserves every newly measured
coordinate, even on frames outside the realized observation fiber. -/
theorem stoppedObservation_frameAction_fixed (t : ℕ)
    (c : StoppedRecord d (j + k) j t) (U : Fin (j + k) → Point d)
    (W : Point d ≃ₗᵢ[ℝ] Point d)
    (hq : W (stoppedQuery A r R η θ tape t c) = stoppedQuery A r R η θ tape t c) :
    stoppedObservation A r R η θ tape t (c, frameAction W U) =
      stoppedObservation A r R η θ tape t (c, U) := by
  apply Prod.ext
  · rfl
  · ext i
    change inner ℝ (W (U i)) (stoppedQuery A r R η θ tape t c) =
      inner ℝ (U i) (stoppedQuery A r R η θ tape t c)
    calc
      _ = inner ℝ (W (U i)) (W (stoppedQuery A r R η θ tape t c)) :=
        congrArg (fun x => inner ℝ (W (U i)) x) hq.symm
      _ = _ := W.inner_map_map _ _

/-- Residual reflections form the geometric symmetry needed for covariance. -/
def recordReflection (t : ℕ) (c : StoppedRecord d (j + k) j t) (a : Point d) :
    Point d ≃ₗᵢ[ℝ] Point d :=
  householder (observedResidual (recordObservationList t c) a)

theorem actualStoppedPosterior_zero_reflections :
    ∀ᵐ c ∂actualStoppedRecordLaw A r hR η θ tape hT 0,
      ∀ a : Point d,
        (actualStoppedPosterior A r hR η θ tape hT 0 c).map
          (frameAction (recordReflection (d := d) (j := j) (k := k) 0 c a)) =
            actualStoppedPosterior A r hR η θ tape hT 0 c := by
  filter_upwards [actualStoppedPosterior_zero_stabilizer A r hR η θ tape hT] with c hc
  intro a
  apply hc
  intro i
  apply householder_observedResidual_fixed (recordObservationList 0 c) a
  apply Submodule.subset_span
  exact ⟨i.castAdd 0, Fin.append_left (recordPrefix 0 c) (recordQueries 0 c) i⟩

section ActualPosteriorUpdates

attribute [local irreducible] householder observedResidual actualStoppedRecordLaw
  actualStoppedPosterior stoppedQuery stoppedObservation reconstructedState
  recordReflection recordObservationList

set_option maxHeartbeats 800000 in
/-- A concrete actual RCD update for one residual normal. The old common
conull premise is an induction hypothesis, not an assumption in the eventual
all-time theorem. The new reflection is predictable in the old record. -/
theorem actualStoppedPosterior_reflection_step (t : ℕ) (a : Point d)
    (hold : ∀ᵐ c ∂actualStoppedRecordLaw A r hR η θ tape hT t,
      ∀ b : Point d,
        (actualStoppedPosterior A r hR η θ tape hT t c).map
          (frameAction (recordReflection (d := d) (j := j) (k := k) t c b)) =
          actualStoppedPosterior A r hR η θ tape hT t c) :
    ∀ᵐ c ∂actualStoppedRecordLaw A r hR η θ tape hT (t + 1),
      (actualStoppedPosterior A r hR η θ tape hT (t + 1) c).map
        (frameAction (recordReflection (d := d) (j := j) (k := k) (t + 1) c a)) =
          actualStoppedPosterior A r hR η θ tape hT (t + 1) c := by
  let q := actualStoppedRecordLaw A r hR η θ tape hT t
  let κ := actualStoppedPosterior A r hR η θ tape hT t
  letI : IsProbabilityMeasure q := actualStoppedRecordLaw_probability A r hR η θ tape hT t
  letI : IsMarkovKernel κ := actualStoppedPosterior_markov A r hR η θ tape hT t
  let B := stoppedObservation (T := j + k) (j := j) A r R η θ tape t
  let v : StoppedRecord d (j + k) j t → Fin (j + t + 1) → Point d := fun c =>
    Fin.snoc (recordObservationList t c) (stoppedQuery A r R η θ tape t c)
  let W := fun c : StoppedRecord d (j + k) j t => householder (observedResidual (v c) a)
  let rotate := fun p : StoppedRecord d (j + k) j t × (Fin (j + k) → Point d) =>
    frameAction (W p.1) p.2
  have hv : Measurable v := (measurable_frameSnoc d (j + t)).comp
    ((measurable_recordObservationList d (j + k) j t).prodMk
      (measurable_stoppedQuery A r η θ tape hR t))
  have hrotate : Measurable rotate :=
    (measurable_observedReflection_frameAction d (j + t + 1) (j + k) a).comp
      ((hv.comp measurable_fst).prodMk measurable_snd)
  have hpreserve : ∀ᵐ c ∂q, (κ c).map (fun U => rotate (c, U)) = κ c := by
    filter_upwards [hold] with c hc
    have hn := observedResidual_snoc_old (recordObservationList t c)
      (stoppedQuery A r R η θ tape t c) a
    simpa only [recordReflection, v, hn] using hc (observedResidual (v c) a)
  have hobserve : ∀ c U, B (c, rotate (c, U)) = B (c, U) := by
    intro c U
    apply stoppedObservation_frameAction_fixed A r η θ tape t c U (W c)
    apply householder_observedResidual_fixed (v c) a
    apply Submodule.subset_span
    exact ⟨Fin.last (j + t), Fin.snoc_last _ _⟩
  let X : StoppedRecord d (j + k) j t × (Fin (j + k) → Point d) →
      StoppedRecord d (j + k) j (t + 1) := fun p => (p.1, B p)
  let L : Kernel (StoppedRecord d (j + k) j (t + 1)) (Fin (j + k) → Point d) :=
    condDistrib Prod.snd X (q ⊗ₘ κ)
  let f := fun p : StoppedRecord d (j + k) j (t + 1) × (Fin (j + k) → Point d) =>
    rotate (p.1.1, p.2)
  have hf : Measurable f := hrotate.comp (measurable_fst.fst.prodMk measurable_snd)
  have hgeneric := predictable_observation_condDistrib_invariance q κ B
    (measurable_stoppedObservation A r η θ tape hR t) rotate hrotate hpreserve hobserve
  have hactual := actualStoppedPosterior_successor A r hR η θ tape hT t
  dsimp only at hgeneric hactual
  rw [actualStoppedRecord_successor_marginal A r hR η θ tape hT t] at hgeneric
  filter_upwards [hgeneric, hactual, actualStoppedRecord_successor_query A r hR η θ tape hT t]
    with c hc ha hq
  change ((Kernel.prod (Kernel.deterministic
    (id : StoppedRecord d (j + k) j (t + 1) → _) measurable_id) L).map f) c = L c at hc
  rw [Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.deterministic_apply measurable_id,
    Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left] at hc
  change (L c).map (frameAction (W c.1)) = L c at hc
  rw [ha] at hc
  have heq : recordReflection (d := d) (j := j) (k := k) (t + 1) c a = W c.1 := by
    have hlist : recordObservationList (t + 1) c =
        Fin.snoc (recordObservationList t c.1) c.2.1 :=
      recordObservationList_succ c.1 c.2
    unfold recordReflection
    rw [hlist, hq]
  rw [heq]
  exact hc

/-- Actual all-time posterior reflection invariance, with one common conull
record set at each time. The universal normal is inside the AE quantifier.
The theorem has no stochastic invariance or conditional-law premise. -/
theorem actualStoppedPosterior_residual_reflections (t : ℕ) :
    ∀ᵐ c ∂actualStoppedRecordLaw A r hR η θ tape hT t,
      ∀ a : Point d,
        (actualStoppedPosterior A r hR η θ tape hT t c).map
          (frameAction (recordReflection (d := d) (j := j) (k := k) t c a)) =
          actualStoppedPosterior A r hR η θ tape hT t c := by
  induction t with
  | zero => exact actualStoppedPosterior_zero_reflections A r hR η θ tape hT
  | succ t ih =>
      letI : IsMarkovKernel (actualStoppedPosterior A r hR η θ tape hT (t + 1)) :=
        actualStoppedPosterior_markov A r hR η θ tape hT (t + 1)
      simp only [recordReflection]
      exact ae_residual_householder_invariance_of_denseSeq
        (actualStoppedRecordLaw A r hR η θ tape hT (t + 1))
        (actualStoppedPosterior A r hR η θ tape hT (t + 1))
        (recordObservationList (t + 1))
        (fun m => by
          simpa only [recordReflection] using actualStoppedPosterior_reflection_step
            A r hR η θ tape hT t (TopologicalSpace.denseSeq (Point d) m) ih)

/-- Actual first-measurement posterior symmetry. All premises concern a
measurable geometric rotation section; none assumes a stochastic symmetry. -/
theorem actualStoppedPosterior_first_update
    (W : (Fin j → Point d) → (Point d ≃ₗᵢ[ℝ] Point d))
    (hW : Measurable (fun p : (Fin j → Point d) × (Fin (j + k) → Point d) =>
      frameAction (W p.1) p.2))
    (hprefix : ∀ v : Fin j → Point d, ∀ i, W v (v i) = v i)
    (hquery : ∀ v : Fin j → Point d,
      W v (stoppedQuery (T := j + k) A r R η θ tape 0 v) =
        stoppedQuery (T := j + k) A r R η θ tape 0 v) :
    let L := actualStoppedPosterior A r hR η θ tape hT 1
    let f : StoppedRecord d (j + k) j 1 × (Fin (j + k) → Point d) →
        (Fin (j + k) → Point d) := fun p => frameAction (W p.1.1) p.2
    ((Kernel.prod (Kernel.deterministic
      (id : StoppedRecord d (j + k) j 1 → _) measurable_id) L).map f)
      =ᵐ[actualStoppedRecordLaw A r hR η θ tape hT 1] L := by
  dsimp only
  let q := actualStoppedRecordLaw A r hR η θ tape hT 0
  let κ := actualStoppedPosterior A r hR η θ tape hT 0
  letI : IsProbabilityMeasure q := actualStoppedRecordLaw_probability A r hR η θ tape hT 0
  letI : IsMarkovKernel κ := actualStoppedPosterior_markov A r hR η θ tape hT 0
  letI : IsMarkovKernel (actualStoppedPosterior A r hR η θ tape hT 1) :=
    actualStoppedPosterior_markov A r hR η θ tape hT 1
  let B := stoppedObservation (T := j + k) (j := j) A r R η θ tape 0
  let rotate := fun p : (Fin j → Point d) × (Fin (j + k) → Point d) =>
    frameAction (W p.1) p.2
  have hpreserve : ∀ᵐ v ∂q, (κ v).map (fun U => rotate (v, U)) = κ v := by
    filter_upwards [actualStoppedPosterior_zero_stabilizer A r hR η θ tape hT]
      with v hv
    exact hv (W v) (hprefix v)
  have hobserve : ∀ v U, B (v, rotate (v, U)) = B (v, U) := by
    intro v U
    exact stoppedObservation_frameAction_fixed A r η θ tape 0 v U (W v) (hquery v)
  have hgeneric := predictable_observation_condDistrib_invariance q κ B
    (measurable_stoppedObservation A r η θ tape hR 0) rotate hW hpreserve hobserve
  have hactual := actualStoppedPosterior_successor A r hR η θ tape hT 0
  dsimp only at hgeneric hactual
  have hmarg : (q ⊗ₘ κ).map (fun p => (p.1, B p)) =
      actualStoppedRecordLaw A r hR η θ tape hT 1 :=
    actualStoppedRecord_successor_marginal A r hR η θ tape hT 0
  rw [hmarg] at hgeneric
  let f : StoppedRecord d (j + k) j 1 × (Fin (j + k) → Point d) →
      (Fin (j + k) → Point d) := fun p => frameAction (W p.1.1) p.2
  have hf : Measurable f :=
    hW.comp (measurable_fst.fst.prodMk measurable_snd)
  filter_upwards [hgeneric, hactual] with c hc ha
  let L := condDistrib Prod.snd (fun p => (p.1, B p)) (q ⊗ₘ κ)
  change ((Kernel.prod (Kernel.deterministic
    (id : StoppedRecord d (j + k) j 1 → _) measurable_id) L).map f) c = L c at hc
  rw [Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.deterministic_apply measurable_id,
    Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left] at hc ⊢
  change (L c).map (frameAction (W c.1)) = L c at hc
  change (actualStoppedPosterior A r hR η θ tape hT 1 c).map (frameAction (W c.1)) =
    actualStoppedPosterior A r hR η θ tape hT 1 c
  rw [ha] at hc
  exact hc

end ActualPosteriorUpdates

end ActualExperiment

end HeavyTailedNoise.RandomizedLift
