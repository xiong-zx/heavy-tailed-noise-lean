import HeavyTailedNoise.Lower.Randomized.AdaptiveHaar

/-!
The actual absorbed analysis record for one fixed private realization and
one fixed Bernoulli tape. The prefix length j is zero based: the analysis
knows columns in Fin j, and absorbs before a response with support count > j
is returned. No unknown ambient response is part of the stored transcript.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

namespace HeavyTailedNoise.RandomizedLift

/-- Maximum nonzero coefficient index plus one; the zero vector has count 0. -/
def coefficientProgress {T : ℕ} (g : Point T) : ℕ := by
  classical
  exact Finset.univ.sup (fun i : Fin T => if g i = 0 then 0 else i.val + 1)

theorem coefficientProgress_le_iff {T j : ℕ} (g : Point T) :
    coefficientProgress g ≤ j ↔ ∀ i : Fin T, j ≤ i.val → g i = 0 := by
  classical
  constructor
  · intro h i hi
    by_contra hn
    have hb := (Finset.le_sup (s := Finset.univ)
      (f := fun k : Fin T => if g k = 0 then 0 else k.val + 1)
      (Finset.mem_univ i)).trans h
    simp only [if_neg hn] at hb
    omega
  · intro h
    apply Finset.sup_le
    intro i _
    by_cases hi : g i = 0
    · simp [hi]
    · simp only [if_neg hi]
      have : i.val < j := by
        by_contra hn
        exact hi (h i (Nat.le_of_not_gt hn))
      omega

@[fun_prop] theorem measurable_coefficientProgress (T : ℕ) :
    Measurable (coefficientProgress (T := T)) := by
  classical
  have hsup (s : Finset (Fin T)) :
      Measurable (fun g : Point T =>
        s.sup (fun i => if g i = 0 then 0 else i.val + 1)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (measurable_const : Measurable (fun _ : Point T => (0 : ℕ)))
    | @insert i s hi ih =>
        have he : MeasurableSet {g : Point T | g i = 0} :=
          measurableSet_eq_fun
            (PiLp.continuous_apply 2 (fun _ : Fin T => ℝ) i).measurable measurable_const
        simpa only [Finset.sup_insert] using
          (Measurable.ite he measurable_const measurable_const).max ih
  exact hsup Finset.univ

def baseProgress {T : ℕ} (θ : unitInterval) (z : Point T) (D : Bool) : ℕ :=
  coefficientProgress (Fradin.bernoulliResponse θ z D)

@[fun_prop] theorem measurable_baseProgress (T : ℕ) (θ : unitInterval) (D : Bool) :
    Measurable (fun z : Point T => baseProgress θ z D) := by
  have hg : Continuous (fun z : Point T => Fradin.bernoulliResponse θ z D) :=
    (continuous_carmonChainGradient T).add
      (Fradin.continuous_maskedGradient.const_smul (Fradin.noiseFactor θ D))
  exact (measurable_coefficientProgress T).comp hg.measurable

theorem baseProgress_zero_le_one (T : ℕ) (θ : unitInterval) (D : Bool) :
    baseProgress θ (0 : Point T) D ≤ 1 := by
  apply (coefficientProgress_le_iff _).2
  intro i hi
  exact Fradin.bernoulliResponse_tail_zero θ (0 : Point T)
    (fun k hk => by simp) i hi D

/-- A finite nested product retains the whole old record at each update. -/
@[reducible] def StoppedRecord (d T j : ℕ) : ℕ → Type
  | 0 => Fin j → Point d
  | t + 1 => StoppedRecord d T j t × (Point d × Point T)

@[instance_reducible] def stoppedRecordMeasurableSpace (d T j : ℕ) :
    (t : ℕ) → MeasurableSpace (StoppedRecord d T j t)
  | 0 => inferInstanceAs (MeasurableSpace (Fin j → Point d))
  | t + 1 => (stoppedRecordMeasurableSpace d T j t).prod
      (inferInstanceAs (MeasurableSpace (Point d × Point T)))

instance (d T j t : ℕ) : MeasurableSpace (StoppedRecord d T j t) :=
  stoppedRecordMeasurableSpace d T j t

def recordPrefix {d T j : ℕ} : (t : ℕ) → StoppedRecord d T j t → (Fin j → Point d)
  | 0, c => c
  | t + 1, c => recordPrefix t c.1

def recordQueries {d T j : ℕ} : (t : ℕ) → StoppedRecord d T j t → (Fin t → Point d)
  | 0, _ => fun i => i.elim0
  | t + 1, c => Fin.snoc (recordQueries t c.1) c.2.1

def recordCoordinates {d T j : ℕ} :
    (t : ℕ) → StoppedRecord d T j t → (Fin t → Point T)
  | 0, _ => fun i => i.elim0
  | t + 1, c => Fin.snoc (recordCoordinates t c.1) c.2.2

def recordedProjections {d T t : ℕ} (U : Fin T → Point d)
    (q : Fin t → Point d) : Fin t → Point T :=
  fun i => WithLp.toLp 2 (frameCoordinates U (q i))

@[fun_prop] theorem measurable_recordedProjections (d T t : ℕ) :
    Measurable (fun p : (Fin T → Point d) × (Fin t → Point d) =>
      recordedProjections p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  apply (PiLp.continuous_toLp 2 (fun _ : Fin T => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro a
  exact ((measurable_pi_apply a).comp measurable_fst).inner
    ((measurable_pi_apply i).comp measurable_snd)

@[fun_prop] theorem measurable_recordPrefix (d T j t : ℕ) :
    Measurable (recordPrefix (d := d) (T := T) (j := j) t) := by
  induction t with
  | zero => exact measurable_id
  | succ t ih => exact ih.comp measurable_fst

private theorem measurable_snoc {C E : Type*} [MeasurableSpace C] [MeasurableSpace E]
    {t : ℕ} {f : C → Fin t → E} {g : C → E}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun c => Fin.snoc (α := fun _ : Fin (t + 1) => E) (f c) (g c)) := by
  apply measurable_pi_iff.mpr
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (measurable_pi_apply k).comp hf
  · simpa using hg

@[fun_prop] theorem measurable_recordQueries (d T j t : ℕ) :
    Measurable (recordQueries (d := d) (T := T) (j := j) t) := by
  induction t with
  | zero => exact measurable_pi_iff.mpr (fun i => i.elim0)
  | succ t ih => exact measurable_snoc (ih.comp measurable_fst) measurable_snd.fst

@[fun_prop] theorem measurable_recordCoordinates (d T j t : ℕ) :
    Measurable (recordCoordinates (d := d) (T := T) (j := j) t) := by
  induction t with
  | zero => exact measurable_pi_iff.mpr (fun i => i.elim0)
  | succ t ih => exact measurable_snoc (ih.comp measurable_fst) measurable_snd.snd

/-- The finite generating list of the observed span; dependence is allowed. -/
def recordObservationList {d T j : ℕ} (t : ℕ) (c : StoppedRecord d T j t) :
    Fin (j + t) → Point d :=
  Fin.append (recordPrefix t c) (recordQueries t c)

@[fun_prop] theorem measurable_recordObservationList (d T j t : ℕ) :
    Measurable (recordObservationList (d := d) (T := T) (j := j) t) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa only [recordObservationList, Fin.append_left, Function.comp_def] using
      (measurable_pi_apply a).comp (measurable_recordPrefix d T j t)
  · simpa only [recordObservationList, Fin.append_right, Function.comp_def] using
      (measurable_pi_apply b).comp (measurable_recordQueries d T j t)

theorem recordObservationList_succ {d T j t : ℕ}
    (c : StoppedRecord d T j t) (z : Point d × Point T) :
    recordObservationList (t + 1) (c, z) = Fin.snoc (recordObservationList t c) z.1 := by
  exact Fin.append_snoc (recordPrefix t c) (recordQueries t c) z.1

/-- Prefix-only synthesis uses the full coefficient vector, not a surrogate. -/
def prefixEmbed {d T j : ℕ} (v : Fin j → Point d) (g : Point T) : Point d :=
  ∑ i : Fin T, if hi : i.val < j then g i • v ⟨i.val, hi⟩ else 0

theorem prefixEmbed_eq_frameEmbed {d T j : ℕ} (hj : j ≤ T)
    (U : Fin T → Point d) (g : Point T)
    (hg : coefficientProgress g ≤ j) :
    prefixEmbed (framePrefix hj U) g = frameEmbed U g := by
  classical
  rw [prefixEmbed, frameEmbed_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < j
  · simp only [dif_pos hi, framePrefix]
    congr 1
  · simp [hi, (coefficientProgress_le_iff g).1 hg i (Nat.le_of_not_gt hi)]

def prefixResponse {d T j : ℕ} (v : Fin j → Point d) (R η : ℝ)
    (θ : unitInterval) (x : Point d) (z : Point T) (D : Bool) : Point d :=
  (fderiv ℝ (softProjection R) x).adjoint
    (prefixEmbed v (Fradin.bernoulliResponse θ z D)) + η • x

@[fun_prop] theorem continuous_joint_prefixEmbed (d T j : ℕ) :
    Continuous (fun p : (Fin j → Point d) × Point T => prefixEmbed p.1 p.2) := by
  classical
  unfold prefixEmbed
  apply continuous_finset_sum
  intro i _
  by_cases hi : i.val < j
  · simp only [dif_pos hi]
    exact ((PiLp.continuous_apply 2 (fun _ : Fin T => ℝ) i).comp continuous_snd).smul
      ((continuous_apply (⟨i.val, hi⟩ : Fin j)).comp continuous_fst)
  · simp only [dif_neg hi]
    exact continuous_const

@[fun_prop] theorem measurable_prefixResponse (d T j : ℕ) {R : ℝ} (hR : 0 < R)
    (η : ℝ) (θ : unitInterval) (D : Bool) :
    Measurable (fun p : ((Fin j → Point d) × Point d) × Point T =>
      prefixResponse p.1.1 R η θ p.1.2 p.2 D) := by
  have hz : Continuous (fun p : ((Fin j → Point d) × Point d) × Point T =>
      Fradin.bernoulliResponse θ p.2 D) :=
    ((continuous_carmonChainGradient T).comp continuous_snd).add
      ((Fradin.continuous_maskedGradient.comp continuous_snd).const_smul
        (Fradin.noiseFactor θ D))
  have he := (continuous_joint_prefixEmbed d T j).comp
    (continuous_fst.fst.prodMk hz)
  have hj : Continuous (fun p : ((Fin j → Point d) × Point d) × Point T =>
      (fderiv ℝ (softProjection R) p.1.2).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp
      (((contDiff_softProjection_two hR).fderiv_right (m := 1) (by norm_num)).continuous.comp
        continuous_fst.snd)
  exact ((hj.clm_apply he).add (continuous_fst.snd.const_smul η)).measurable

theorem prefixResponse_eq_response {d T j : ℕ} (hj : j ≤ T)
    (U : Fin T → Point d) (R η : ℝ) (θ : unitInterval) (x : Point d) (D : Bool)
    (hg : baseProgress θ (coordinates U R x) D ≤ j) :
    prefixResponse (framePrefix hj U) R η θ x (coordinates U R x) D =
      response U R η θ x D := by
  unfold prefixResponse response transport
  rw [prefixEmbed_eq_frameEmbed hj U _ hg]
  rfl

section FixedPrivate

variable {d T N j : ℕ} {Private : Type*} [MeasurableSpace Private]
variable (A : RandomAlgorithm d N Private) (r : Private)
variable (R η : ℝ) (θ : unitInterval) (tape : ℕ → Bool)

def stateDecision (t : ℕ) (s : Transcript d t × ℕ) : Point d :=
  if s.2 ≤ j then A.decide t r s.1 else 0

@[fun_prop] theorem measurable_stateDecision (t : ℕ) :
    Measurable (stateDecision (j := j) A r t) := by
  unfold stateDecision
  exact Measurable.ite (measurableSet_le measurable_snd measurable_const)
    ((A.measurable_decide t).comp (measurable_const.prodMk measurable_fst)) measurable_const

/-- Absorption is tested before the returned vector is reconstructed. -/
def advanceState (t : ℕ) (v : Fin j → Point d)
    (s : Transcript d t × ℕ) (z : Point T) : Transcript d (t + 1) × ℕ :=
  let x := stateDecision (j := j) A r t s
  let b := baseProgress θ z (tape t)
  (Fin.snoc s.1 (x,
      if s.2 ≤ j ∧ b ≤ j then prefixResponse v R η θ x z (tape t) else 0),
    if s.2 ≤ j then max s.2 b else s.2)

@[fun_prop] theorem measurable_advanceState {R : ℝ} (hR : 0 < R) (t : ℕ) :
    Measurable (fun p : (Fin j → Point d) × ((Transcript d t × ℕ) × Point T) =>
      advanceState A r R η θ tape t p.1 p.2.1 p.2.2) := by
  have hs : Measurable (fun p : (Fin j → Point d) × ((Transcript d t × ℕ) × Point T) =>
      p.2.1) := measurable_snd.fst
  have hx := (measurable_stateDecision (j := j) A r t).comp hs
  have hb : Measurable
      (fun p : (Fin j → Point d) × ((Transcript d t × ℕ) × Point T) =>
        baseProgress θ p.2.2 (tape t)) :=
    (measurable_baseProgress T θ (tape t)).comp measurable_snd.snd
  have ha := measurableSet_le hs.snd (measurable_const (a := j))
  have hstop := ha.inter (measurableSet_le hb (measurable_const (a := j)))
  have hg := (measurable_prefixResponse d T j hR η θ (tape t)).comp
    ((measurable_fst.prodMk hx).prodMk measurable_snd.snd)
  exact Measurable.prodMk
    (measurable_snoc hs.fst (hx.prodMk (Measurable.ite hstop hg measurable_const)))
    (Measurable.ite ha (hs.snd.max hb) hs.snd)

def reconstructedState : (t : ℕ) → StoppedRecord d T j t → Transcript d t × ℕ
  | 0, _ => (fun i => i.elim0, 0)
  | t + 1, c => advanceState A r R η θ tape t (recordPrefix t c.1)
      (reconstructedState t c.1) c.2.2

@[fun_prop] theorem measurable_reconstructedState {R : ℝ} (hR : 0 < R) (t : ℕ) :
    Measurable (reconstructedState (T := T) (j := j) A r R η θ tape t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (measurable_advanceState A r η θ tape hR t).comp
        (((measurable_recordPrefix d T j t).comp measurable_fst).prodMk
          ((ih.comp measurable_fst).prodMk measurable_snd.snd))

def stoppedDecision (t : ℕ) (c : StoppedRecord d T j t) : Point d :=
  stateDecision (j := j) A r t (reconstructedState A r R η θ tape t c)

@[fun_prop] theorem measurable_stoppedDecision {R : ℝ} (hR : 0 < R) (t : ℕ) :
    Measurable (stoppedDecision (T := T) (j := j) A r R η θ tape t) :=
  (measurable_stateDecision (j := j) A r t).comp
    (measurable_reconstructedState (T := T) (j := j) A r η θ tape hR t)

def stoppedQuery (t : ℕ) (c : StoppedRecord d T j t) : Point d :=
  if (reconstructedState A r R η θ tape t c).2 ≤ j
    then softProjection R (stoppedDecision A r R η θ tape t c) else 0

@[fun_prop] theorem measurable_stoppedQuery {R : ℝ} (hR : 0 < R) (t : ℕ) :
    Measurable (stoppedQuery (T := T) (j := j) A r R η θ tape t) := by
  have hs := measurable_reconstructedState (T := T) (j := j) A r η θ tape hR t
  exact Measurable.ite (measurableSet_le hs.snd measurable_const)
    ((contDiff_softProjection_two hR).continuous.measurable.comp
      (measurable_stoppedDecision (T := T) (j := j) A r η θ tape hR t)) measurable_const

/-- The measured coordinates are all U^T q; no column is discarded. -/
def stoppedObservation (t : ℕ)
    (p : StoppedRecord d T j t × (Fin T → Point d)) : Point d × Point T :=
  let q := stoppedQuery A r R η θ tape t p.1
  (q, WithLp.toLp 2 (frameCoordinates p.2 q))

@[fun_prop] theorem measurable_stoppedObservation {R : ℝ} (hR : 0 < R) (t : ℕ) :
    Measurable (stoppedObservation (T := T) (j := j) A r R η θ tape t) := by
  have hq : Measurable
      (fun p : StoppedRecord d T j t × (Fin T → Point d) =>
        stoppedQuery A r R η θ tape t p.1) :=
    (measurable_stoppedQuery (T := T) (j := j) A r η θ tape hR t).comp measurable_fst
  apply hq.prodMk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin T => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd).inner hq

def absorbedRecord (hj : j ≤ T) (U : Fin T → Point d) :
    (t : ℕ) → StoppedRecord d T j t
  | 0 => framePrefix hj U
  | t + 1 =>
      let c := absorbedRecord hj U t
      (c, stoppedObservation A r R η θ tape t (c, U))

@[fun_prop] theorem measurable_absorbedRecord {R : ℝ} (hR : 0 < R)
    (hj : j ≤ T) (t : ℕ) :
    Measurable (fun U : Fin T → Point d => absorbedRecord A r R η θ tape hj U t) := by
  induction t with
  | zero => exact measurable_framePrefix hj
  | succ t ih =>
      exact ih.prodMk ((measurable_stoppedObservation A r η θ tape hR t).comp
        (ih.prodMk measurable_id))

theorem recordPrefix_absorbedRecord (hj : j ≤ T) (U : Fin T → Point d) (t : ℕ) :
    recordPrefix t (absorbedRecord A r R η θ tape hj U t) = framePrefix hj U := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

/-- Every old recorded projection is the exact full-frame projection of the
corresponding stored bounded query, including absorbed zero decisions. -/
theorem recordCoordinates_absorbedRecord (hj : j ≤ T) (U : Fin T → Point d) (t : ℕ) :
    recordCoordinates t (absorbedRecord A r R η θ tape hj U t) =
      fun i => WithLp.toLp 2 (frameCoordinates U
        (recordQueries t (absorbedRecord A r R η θ tape hj U t) i)) := by
  induction t with
  | zero => funext i; exact i.elim0
  | succ t ih =>
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
      · simpa only [absorbedRecord, recordCoordinates, recordQueries,
          Fin.snoc_castSucc] using congrFun ih a
      · simp only [absorbedRecord, recordCoordinates, recordQueries, Fin.snoc_last,
          stoppedObservation]

theorem stoppedQuery_eq_zero_of_absorbed (t : ℕ) (c : StoppedRecord d T j t)
    (h : j < (reconstructedState A r R η θ tape t c).2) :
    stoppedQuery A r R η θ tape t c = 0 := by
  exact if_neg (Nat.not_le_of_gt h)

/-- On the actual record gamma is the cumulative maximum of base support
counts. After absorption the newly measured vector is zero and has count at
most one, already dominated by the absorbed gamma. -/
theorem reconstructedState_progress_successor (hj : j ≤ T)
    (U : Fin T → Point d) (t : ℕ) :
    (reconstructedState A r R η θ tape (t + 1)
      (absorbedRecord A r R η θ tape hj U (t + 1))).2 =
      max (reconstructedState A r R η θ tape t
        (absorbedRecord A r R η θ tape hj U t)).2
        (baseProgress θ
          (stoppedObservation A r R η θ tape t
            (absorbedRecord A r R η θ tape hj U t, U)).2 (tape t)) := by
  classical
  let c := absorbedRecord A r R η θ tape hj U t
  let s := reconstructedState A r R η θ tape t c
  let z := (stoppedObservation A r R η θ tape t (c, U)).2
  change (if s.2 ≤ j then max s.2 (baseProgress θ z (tape t)) else s.2) =
    max s.2 (baseProgress θ z (tape t))
  by_cases h : s.2 ≤ j
  · simp [h]
  · have hq : stoppedQuery A r R η θ tape t c = 0 :=
      stoppedQuery_eq_zero_of_absorbed A r R η θ tape t c (Nat.lt_of_not_ge h)
    have hz : (stoppedObservation A r R η θ tape t (c, U)).2 = 0 := by
      ext i
      simp [stoppedObservation, hq, frameCoordinates]
    have hb : baseProgress θ
        (stoppedObservation A r R η θ tape t (c, U)).2 (tape t) ≤ s.2 := by
      rw [hz]
      exact (baseProgress_zero_le_one T θ (tape t)).trans (by omega)
    simpa only [if_neg h, z, max_eq_left hb]

theorem advanceState_progress_mono (t : ℕ) (v : Fin j → Point d)
    (s : Transcript d t × ℕ) (z : Point T) :
    s.2 ≤ (advanceState A r R η θ tape t v s z).2 := by
  classical
  simp only [advanceState]
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem advanceState_alive_iff (t : ℕ) (v : Fin j → Point d)
    (s : Transcript d t × ℕ) (z : Point T) :
    (advanceState A r R η θ tape t v s z).2 ≤ j ↔
      s.2 ≤ j ∧ baseProgress θ z (tape t) ≤ j := by
  classical
  simp only [advanceState]
  by_cases h : s.2 ≤ j
  · simp [h, max_le_iff]
  · simp [h]

theorem reconstructedState_alive_eq_runTranscript (hj : j ≤ T)
    {R : ℝ} (hR : 0 < R) (U : Fin T → Point d) (t : ℕ)
    (halive : (reconstructedState A r R η θ tape t
      (absorbedRecord A r R η θ tape hj U t)).2 ≤ j) :
    (reconstructedState A r R η θ tape t
      (absorbedRecord A r R η θ tape hj U t)).1 =
      runTranscript (oracle U hR η θ) A r t (fun i => tape i.val) := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
      let c := absorbedRecord A r R η θ tape hj U t
      let s := reconstructedState A r R η θ tape t c
      let x := A.decide t r s.1
      have hstep : (advanceState A r R η θ tape t (recordPrefix t c) s
          (stoppedObservation A r R η θ tape t (c, U)).2).2 ≤ j := halive
      have hs := (advanceState_alive_iff A r R η θ tape t (recordPrefix t c) s _).1 hstep
      have hh : s.1 = runTranscript (oracle U hR η θ) A r t (fun i => tape i.val) :=
        ih hs.1
      have hq : stoppedQuery A r R η θ tape t c = softProjection R x := by
        simp [stoppedQuery, stoppedDecision, stateDecision, s, x, hs.1]
      have hz : (stoppedObservation A r R η θ tape t (c, U)).2 =
          coordinates U R x := by
        simp only [stoppedObservation, hq]
        rfl
      have hb : baseProgress θ (coordinates U R x) (tape t) ≤ j := by
        simpa only [hz] using hs.2
      have hp : recordPrefix t c = framePrefix hj U :=
        recordPrefix_absorbedRecord A r R η θ tape hj U t
      change (advanceState A r R η θ tape t (recordPrefix t c) s
        (stoppedObservation A r R η θ tape t (c, U)).2).1 = _
      simp only [advanceState, hz, hs.1, hb, and_self, if_true, stateDecision]
      rw [hp, prefixResponse_eq_response hj U R η θ x (tape t) hb]
      change (Fin.snoc s.1 (x, response U R η θ x (tape t)) : Transcript d (t + 1)) = _
      simp only [runTranscript]
      dsimp only [x]
      rw [hh]
      rfl

/-- The N+1st analysis decision adds only the output projection. -/
def stoppedOutputQuery (c : StoppedRecord d T j N) : Point d :=
  if (reconstructedState A r R η θ tape N c).2 ≤ j
    then softProjection R (A.output r (reconstructedState A r R η θ tape N c).1)
    else 0

@[fun_prop] theorem measurable_stoppedOutputQuery {R : ℝ} (hR : 0 < R) :
    Measurable (stoppedOutputQuery (T := T) (j := j) A r R η θ tape) := by
  have hs := measurable_reconstructedState (T := T) (j := j) A r η θ tape hR N
  exact Measurable.ite (measurableSet_le hs.snd measurable_const)
    ((contDiff_softProjection_two hR).continuous.measurable.comp
      (A.measurable_output.comp (measurable_const.prodMk hs.fst))) measurable_const

def stoppedOutputObservation
    (p : StoppedRecord d T j N × (Fin T → Point d)) : Point d × Point T :=
  let q := stoppedOutputQuery A r R η θ tape p.1
  (q, WithLp.toLp 2 (frameCoordinates p.2 q))

@[fun_prop] theorem measurable_stoppedOutputObservation {R : ℝ} (hR : 0 < R) :
    Measurable (stoppedOutputObservation (T := T) (j := j) A r R η θ tape) := by
  have hq : Measurable
      (fun p : StoppedRecord d T j N × (Fin T → Point d) =>
        stoppedOutputQuery A r R η θ tape p.1) :=
    (measurable_stoppedOutputQuery (T := T) (j := j) A r η θ tape hR).comp measurable_fst
  apply hq.prodMk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin T => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd).inner hq

/-- The analysis-only final append is not advanceState: gamma, seeds and
the response history remain exactly those of the N-response run. -/
def absorbedOutputRecord (hj : j ≤ T) (U : Fin T → Point d) :
    StoppedRecord d T j (N + 1) :=
  let c := absorbedRecord A r R η θ tape hj U N
  (c, stoppedOutputObservation A r R η θ tape (c, U))

@[fun_prop] theorem measurable_absorbedOutputRecord {R : ℝ} (hR : 0 < R)
    (hj : j ≤ T) :
    Measurable (fun U : Fin T → Point d => absorbedOutputRecord A r R η θ tape hj U) :=
  (measurable_absorbedRecord A r η θ tape hR hj N).prodMk
    ((measurable_stoppedOutputObservation A r η θ tape hR).comp
      ((measurable_absorbedRecord A r η θ tape hR hj N).prodMk measurable_id))

theorem stoppedOutputQuery_eq_actual (hj : j ≤ T) {R : ℝ} (hR : 0 < R)
    (U : Fin T → Point d)
    (halive : (reconstructedState A r R η θ tape N
      (absorbedRecord A r R η θ tape hj U N)).2 ≤ j) :
    stoppedOutputQuery A r R η θ tape (absorbedRecord A r R η θ tape hj U N) =
      softProjection R (A.output r
        (runTranscript (oracle U hR η θ) A r N (fun i => tape i.val))) := by
  rw [stoppedOutputQuery, if_pos halive,
    reconstructedState_alive_eq_runTranscript A r η θ tape hj hR U N halive]

end FixedPrivate

/-- Fixed finite tapes can be extended harmlessly beyond their response budget. -/
def finiteTape {N : ℕ} (seeds : Fin N → Bool) (t : ℕ) : Bool :=
  if h : t < N then seeds ⟨t, h⟩ else false

@[simp] theorem finiteTape_apply {N : ℕ} (seeds : Fin N → Bool) (i : Fin N) :
    finiteTape seeds i.val = seeds i := by
  simp [finiteTape, i.isLt]

theorem reconstructedState_alive_eq_runTranscript_finite
    {d T N j : ℕ} {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm d N Private) (r : Private) (η : ℝ) (θ : unitInterval)
    (hj : j ≤ T) {R : ℝ} (hR : 0 < R) (U : Fin T → Point d) (seeds : Fin N → Bool)
    (halive : (reconstructedState A r R η θ (finiteTape seeds) N
      (absorbedRecord A r R η θ (finiteTape seeds) hj U N)).2 ≤ j) :
    (reconstructedState A r R η θ (finiteTape seeds) N
      (absorbedRecord A r R η θ (finiteTape seeds) hj U N)).1 =
      runTranscript (oracle U hR η θ) A r N seeds := by
  simpa only [finiteTape_apply] using
    reconstructedState_alive_eq_runTranscript A r η θ (finiteTape seeds) hj hR U N halive

theorem stoppedOutputQuery_eq_actual_finite
    {d T N j : ℕ} {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm d N Private) (r : Private) (η : ℝ) (θ : unitInterval)
    (hj : j ≤ T) {R : ℝ} (hR : 0 < R) (U : Fin T → Point d) (seeds : Fin N → Bool)
    (halive : (reconstructedState A r R η θ (finiteTape seeds) N
      (absorbedRecord A r R η θ (finiteTape seeds) hj U N)).2 ≤ j) :
    stoppedOutputQuery A r R η θ (finiteTape seeds)
      (absorbedRecord A r R η θ (finiteTape seeds) hj U N) =
      softProjection R (A.output r (runTranscript (oracle U hR η θ) A r N seeds)) := by
  simpa only [finiteTape_apply] using
    stoppedOutputQuery_eq_actual A r η θ (finiteTape seeds) hj hR U halive

end HeavyTailedNoise.RandomizedLift
