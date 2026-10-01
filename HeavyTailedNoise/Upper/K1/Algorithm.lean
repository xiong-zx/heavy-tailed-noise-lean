import HeavyTailedNoise.Upper.K1.Parameters
import HeavyTailedNoise.Upper.Foundations.ClipGeometry
import HeavyTailedNoise.Model.Protocol

/-!
The literal query protocol of the shared-batch exponential-memory method. A
runtime batch occupies `n` consecutive one-response decisions at one frozen
point. Its first response is reused locally to update the next coarse center.
The independent private index selects an already queried runtime point.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Manuscript band `j+1`, applied to one already returned residual. -/
def highBand {d : ℕ} (j : Fin P.J) (z : Point d) : Point d :=
  upperShell (P.tau j.succ) (P.tau j.castSucc) z

@[fun_prop] theorem measurable_highBand {d : ℕ} (j : Fin P.J) :
    Measurable (highBand (d := d) P j) :=
  measurable_upperShell (P.tau_pos j.succ) (P.tau_pos j.castSucc)

def lowBand {d : ℕ} (z : Point d) : Point d :=
  upperClip (P.tau ⟨0, Nat.zero_lt_succ P.J⟩) z

@[fun_prop] theorem measurable_lowBand {d : ℕ} :
    Measurable (lowBand (d := d) P) :=
  measurable_upperClip (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩)

/-- The sole coarse-center update. The batch's first returned vector is used
after the current batch has been processed. -/
def coarseCenter {d : ℕ} (w y : Point d) : Point d :=
  w + P.beta • lowBand P (y - w)

@[fun_prop] theorem measurable_coarseCenter {d : ℕ} {α : Type*}
    [MeasurableSpace α] {w y : α → Point d}
    (hw : Measurable w) (hy : Measurable y) :
    Measurable (fun z => coarseCenter P (w z) (y z)) := by
  change Measurable (fun z => w z + P.beta • lowBand P (y z - w z))
  have hresidual : Measurable (fun z => y z - w z) := hy.sub hw
  have hlow : Measurable (fun z => lowBand P (y z - w z)) :=
    (measurable_lowBand P).comp hresidual
  have hbeta : Measurable (fun _ : α => P.beta) := measurable_const
  exact hw.add (hbeta.smul hlow)

/-- The zero-estimate branch is included by the total inverse `0⁻¹ = 0`. -/
def direction {d : ℕ} (z : Point d) : Point d := ‖z‖⁻¹ • z

@[fun_prop] theorem measurable_direction {d : ℕ} :
    Measurable (direction (d := d)) := by
  exact (measurable_norm.inv).smul measurable_id

@[simp] theorem direction_zero {d : ℕ} : direction (0 : Point d) = 0 := by
  simp [direction]

theorem direction_norm_le_one {d : ℕ} (z : Point d) :
    ‖direction z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp [direction, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), hnorm]

/-- `(point, center, high memories, low accumulator, high accumulators,
first response of the current batch)`. The product type retains its standard
measurable structure. -/
abbrev State (d J : ℕ) :=
  Point d × Point d × (Fin J → Point d) × Point d × (Fin J → Point d) × Point d

def initialState (d : ℕ) : State d P.J :=
  (0, 0, (fun _ => 0), 0, (fun _ => 0), 0)

def point {d : ℕ} (s : State d P.J) : Point d := s.1
def center {d : ℕ} (s : State d P.J) : Point d := s.2.1
def memories {d : ℕ} (s : State d P.J) : Fin P.J → Point d := s.2.2.1
def lowSum {d : ℕ} (s : State d P.J) : Point d := s.2.2.2.1
def highSums {d : ℕ} (s : State d P.J) : Fin P.J → Point d := s.2.2.2.2.1
def firstResponse {d : ℕ} (s : State d P.J) : Point d := s.2.2.2.2.2

/-- Accumulate one returned vector at the center fixed before this batch. -/
def accumulateResponse {d : ℕ} (s : State d P.J) (y : Point d) :
    Point d × (Fin P.J → Point d) :=
  (lowSum P s + lowBand P (y - center P s),
    fun j => highSums P s j + highBand P j (y - center P s))

/-- The manuscript's high-band EMA after the last current-batch response. -/
def updatedBands {d : ℕ} (s : State d P.J)
    (highs : Fin P.J → Point d) : Fin P.J → Point d :=
  fun j => (1 - P.alpha j) • memories P s j +
    P.alpha j • ((P.n : ℝ)⁻¹ • highs j)

@[fun_prop] theorem measurable_updatedBands {d : ℕ} {α : Type*}
    [MeasurableSpace α] {s : α → State d P.J}
    {highs : α → Fin P.J → Point d}
    (hs : Measurable s) (hhighs : Measurable highs) :
    Measurable (fun z => updatedBands P (s z) (highs z)) := by
  apply measurable_pi_iff.mpr
  intro j
  have hmem : Measurable (fun z => memories P (s z) j) := by
    dsimp [memories]
    fun_prop
  have hhigh : Measurable (fun z => highs z j) :=
    (measurable_pi_apply j).comp hhighs
  have hc1 : Measurable (fun _ : α => 1 - P.alpha j) := measurable_const
  have hc2 : Measurable (fun _ : α => P.alpha j) := measurable_const
  have hcn : Measurable (fun _ : α => (P.n : ℝ)⁻¹) := measurable_const
  change Measurable (fun z =>
    (1 - P.alpha j) • memories P (s z) j +
      P.alpha j • ((P.n : ℝ)⁻¹ • highs z j))
  exact (hc1.smul hmem).add (hc2.smul (hcn.smul hhigh))

/-- The single completed-batch direction estimate used by `step`. -/
def completedBatchEstimate {d : ℕ} (s : State d P.J)
    (low : Point d) (updated : Fin P.J → Point d) : Point d :=
  center P s + (P.n : ℝ)⁻¹ • low + ∑ j, updated j

/-- A pure transcript update. The natural index is the zero-based response
number. Only the completed batch changes the decision point and center. -/
def step {d : ℕ} (t : ℕ) (s : State d P.J) (y : Point d) : State d P.J :=
  if t = 0 then
    (0, y, (fun _ => 0), 0, (fun _ => 0), 0)
  else if t < 1 + initialResponses P then
    let sums := fun j => highSums P s j + highBand P j (y - center P s)
    if t + 1 = 1 + initialResponses P then
      (point P s, center P s,
        (fun j => (initialResponses P : ℝ)⁻¹ • sums j), 0,
        (fun _ => 0), 0)
    else
      (point P s, center P s, memories P s, 0, sums, 0)
  else if t < responseCount P then
    let k := t - (1 + initialResponses P)
    let first := if k % P.n = 0 then y else firstResponse P s
    let accumulated := accumulateResponse P s y
    if (k + 1) % P.n = 0 then
      let updated := updatedBands P s accumulated.2
      let estimate := completedBatchEstimate P s accumulated.1 updated
      (point P s - P.h • direction estimate,
        coarseCenter P (center P s) first,
        updated, 0, (fun _ => 0), 0)
    else
      (point P s, center P s, memories P s, accumulated.1, accumulated.2, first)
  else s

theorem point_step_initial {d : ℕ} (t : ℕ) (s : State d P.J) (y : Point d)
    (ht0 : t ≠ 0) (ht : t < 1 + initialResponses P) :
    point P (step P t s y) = point P s := by
  simp only [step, if_neg ht0, if_pos ht]
  split_ifs <;> rfl

theorem point_step_runtime_nonterminal {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d)
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hnonterminal : (t - (1 + initialResponses P) + 1) % P.n ≠ 0) :
    point P (step P t s y) = point P s := by
  have ht0 : t ≠ 0 := by omega
  have hnotinit : ¬t < 1 + initialResponses P := Nat.not_lt.mpr hstart
  simp [step, ht0, hnotinit, hend, hnonterminal, point]

theorem center_step_runtime_nonterminal {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d)
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hnonterminal : (t - (1 + initialResponses P) + 1) % P.n ≠ 0) :
    center P (step P t s y) = center P s := by
  have ht0 : t ≠ 0 := by omega
  have hnotinit : ¬t < 1 + initialResponses P := Nat.not_lt.mpr hstart
  simp [step, ht0, hnotinit, hend, hnonterminal, center]

theorem measurable_step {d : ℕ} (t : ℕ) :
    Measurable (fun z : State d P.J × Point d => step P t z.1 z.2) := by
  classical
  by_cases h0 : t = 0
  · simp [step, h0, point, center, memories, lowSum, highSums, firstResponse] <;>
      fun_prop
  by_cases hI : t < 1 + initialResponses P
  · by_cases hIlast : t + 1 = 1 + initialResponses P
    · simp [step, h0, hI, hIlast, point, center, memories, lowSum,
        highSums, firstResponse] <;> fun_prop
    · simp [step, h0, hI, hIlast, point, center, memories, lowSum,
        highSums, firstResponse] <;> fun_prop
  by_cases hR : t < responseCount P
  · by_cases hfirst : (t - (1 + initialResponses P)) % P.n = 0 <;>
      by_cases hlast : (t - (1 + initialResponses P) + 1) % P.n = 0 <;>
      (simp [step, accumulateResponse, updatedBands, completedBatchEstimate,
        h0, hI, hR, hfirst, hlast, point, center, memories,
        lowSum, highSums, firstResponse] <;> fun_prop)
  · simp [step, h0, hI, hR] <;> fun_prop

/-- Reconstruct the complete state from observed query-response pairs. The
update reads only the returned vector; it never evaluates an oracle again. -/
def stateAt {d : ℕ} : (t : ℕ) → Transcript d t → State d P.J
  | 0, _ => initialState P d
  | t + 1, H =>
    step P t (stateAt t (fun i => H i.castSucc)) (H (Fin.last t)).2

theorem measurable_stateAt {d : ℕ} (t : ℕ) :
    Measurable (stateAt (d := d) P t) := by
  induction t with
  | zero =>
      exact measurable_const
  | succ t ih =>
      have hprefix : Measurable (fun H : Transcript d (t + 1) =>
          (fun i : Fin t => H i.castSucc : Transcript d t)) := by
        apply measurable_pi_iff.mpr
        intro i
        exact measurable_pi_apply i.castSucc
      have hlast : Measurable (fun H : Transcript d (t + 1) =>
          (H (Fin.last t)).2) :=
        measurable_snd.comp (measurable_pi_apply (Fin.last t))
      change Measurable (fun H : Transcript d (t + 1) =>
        step P t (stateAt P t (fun i => H i.castSucc)) (H (Fin.last t)).2)
      simpa only [Function.comp_def] using
        (measurable_step P t).comp ((ih.comp hprefix).prodMk hlast)

/-- The scheduled decision rule is independent of the oracle and private
output index. Every response in a batch is queried at the current state point. -/
def query {d : ℕ} (t : ℕ) (H : Transcript d t) : Point d :=
  point P (stateAt P t H)

@[simp] theorem query_zero {d : ℕ} (H : Transcript d 0) : query P 0 H = 0 := by
  rfl

/-- Before the last response in a runtime batch, the next decision remains
at the batch's pre-response point, regardless of the observed vector. -/
theorem query_next_of_runtime_nonterminal {d : ℕ} (t : ℕ)
    (H : Transcript d (t + 1))
    (hstart : 1 + initialResponses P ≤ t)
    (hend : t < responseCount P)
    (hnonterminal : (t - (1 + initialResponses P) + 1) % P.n ≠ 0) :
    query P (t + 1) H = query P t (fun i => H i.castSucc) := by
  exact point_step_runtime_nonterminal P t
    (stateAt P t (fun i => H i.castSucc)) (H (Fin.last t)).2
    hstart hend hnonterminal

/-- Every decision inside a runtime batch is fixed by the transcript before
that batch. The statement allows arbitrary, even inconsistent, later entries
in `H`: no response from the current batch can move its query point. -/
theorem batch_query_fixed_nat {d : ℕ} (r : Fin P.T) (k : ℕ)
    (hk : k < P.n)
    (H : Transcript d (batchStart P r.val + k)) :
    query P (batchStart P r.val + k) H =
      query P (batchStart P r.val)
        (fun j : Fin (batchStart P r.val) =>
          H ⟨j.val, by omega⟩) := by
  revert hk H
  induction k with
  | zero =>
      intro hk H
      simp only [Nat.add_zero]
      congr 1
  | succ k ih =>
      intro hk H
      let a := batchStart P r.val
      let t := a + k
      have hkprev : k < P.n := Nat.lt_of_succ_lt hk
      have hstart : 1 + initialResponses P ≤ t := by
        dsimp [t, a, batchStart]
        omega
      have hr : r.val + 1 ≤ P.T := Nat.succ_le_iff.mpr r.isLt
      have hmul : (r.val + 1) * P.n ≤ P.T * P.n :=
        Nat.mul_le_mul_right P.n hr
      have hprefix : r.val * P.n + k < (r.val + 1) * P.n := by
        rw [Nat.succ_mul]
        omega
      have hend : t < responseCount P := by
        dsimp [t, a, batchStart, responseCount]
        omega
      have hsub : t - (1 + initialResponses P) = r.val * P.n + k := by
        dsimp [t, a, batchStart]
        omega
      have hmod : (r.val * P.n + k + 1) % P.n = k + 1 := by
        calc
          _ = (r.val * P.n + (k + 1)) % P.n := by rw [Nat.add_assoc]
          _ = (k + 1) % P.n := by simp [Nat.add_mod]
          _ = k + 1 := Nat.mod_eq_of_lt hk
      have hnonterminal :
          (t - (1 + initialResponses P) + 1) % P.n ≠ 0 := by
        rw [hsub, hmod]
        omega
      have hnext := query_next_of_runtime_nonterminal P t H
        hstart hend hnonterminal
      have hprev := ih hkprev (fun j : Fin (a + k) => H j.castSucc)
      exact hnext.trans (by simpa only [t, a, Fin.castSucc_mk] using hprev)

/-- Fin-indexed batch form used by the stochastic analysis. -/
theorem batch_query_fixed {d : ℕ} (r : Fin P.T) (i : Fin P.n)
    (H : Transcript d (batchStart P r.val + i.val)) :
    query P (batchStart P r.val + i.val) H =
      query P (batchStart P r.val)
        (fun j : Fin (batchStart P r.val) => H ⟨j.val, by omega⟩) :=
  batch_query_fixed_nat P r i.val i.isLt H

theorem measurable_query {d : ℕ} (t : ℕ) :
    Measurable (query (d := d) P t) := by
  exact measurable_fst.comp (measurable_stateAt P t)

/-- Runtime batch `r` starts strictly before the response cap. -/
def outputIndex (r : Fin P.T) : Fin (responseCount P) :=
  ⟨batchStart P r.val, by
    have h := Nat.mul_lt_mul_of_pos_right r.isLt P.n_pos
    exact Nat.add_lt_add_left h (1 + initialResponses P)⟩

/-- The output is a previously queried runtime point and costs no response. -/
def selectedPoint {d : ℕ} (r : Fin P.T)
    (H : Transcript d (responseCount P)) : Point d :=
  (H (outputIndex P r)).1

theorem measurable_selectedPoint {d : ℕ} :
    Measurable (fun z : Fin P.T × Transcript d (responseCount P) =>
      selectedPoint P z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro r
  exact measurable_fst.comp (measurable_pi_apply (outputIndex P r))

/-- The only private randomness is the independent uniform output index. -/
def algorithm {d : ℕ} : RandomAlgorithm d (responseCount P) (Fin P.T) where
  privateLaw := uniformOn Set.univ
  private_probability := by
    letI : Nonempty (Fin P.T) := ⟨⟨0, P.T_pos⟩⟩
    infer_instance
  decide := fun t _ H => query P t H
  measurable_decide := by
    intro t
    exact (measurable_query P t).comp measurable_snd
  output := fun r H => selectedPoint P r H
  measurable_output := measurable_selectedPoint P

theorem algorithm_decide {d : ℕ} (t : ℕ) (r : Fin P.T)
    (H : Transcript d t) :
    (algorithm (d := d) P).decide t r H = query P t H := rfl

theorem algorithm_output_is_query {d : ℕ} (r : Fin P.T)
    (H : Transcript d (responseCount P)) :
    (algorithm (d := d) P).output r H = (H (outputIndex P r)).1 := rfl

/-- One coordinate of the independent seed vector supplies exactly the next
gradient response, after the query is fixed by the earlier transcript. -/
theorem algorithm_last_response {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (r : Fin P.T) (t : ℕ)
    (seeds : Fin (t + 1) → Seed) :
    runTranscript O (algorithm (d := d) P) r (t + 1) seeds (Fin.last t) =
      let history := runTranscript O (algorithm (d := d) P) r t
        (fun i => seeds i.castSucc)
      let x := query P t history
      (x, O.response x (seeds (Fin.last t))) := by
  simpa only [algorithm_decide] using
    runTranscript_last O (algorithm (d := d) P) r t seeds

/-- The response log really records the decision at each index, as a function
of exactly the earlier seeds. This applies to arbitrary oracle seed spaces. -/
theorem algorithm_logged_query {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (r : Fin P.T) (n : ℕ)
    (seeds : Fin n → Seed) (i : Fin n) :
    (runTranscript O (algorithm (d := d) P) r n seeds i).1 =
      query P i.val
        (runTranscript O (algorithm (d := d) P) r i.val
          (fun j : Fin i.val => seeds ⟨j.val, lt_trans j.isLt i.isLt⟩)) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [runTranscript_last]
        change query P n
            (runTranscript O (algorithm (d := d) P) r n
              (fun j => seeds j.castSucc)) = _
        congr 1
      · rw [runTranscript_prefix]
        simpa only [Fin.val_castSucc, Fin.castSucc_mk] using
          ih (fun j => seeds j.castSucc) j

/-- On an actual run, the returned point is the batch-start decision
computed from the preceding transcript, with no extra oracle response. -/
theorem algorithm_output_actual_query {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    (algorithm (d := d) P).output r
      (runTranscript O (algorithm (d := d) P) r (responseCount P) seeds) =
      query P (batchStart P r.val)
        (runTranscript O (algorithm (d := d) P) r (batchStart P r.val)
          (fun j : Fin (batchStart P r.val) =>
            seeds ⟨j.val, lt_trans j.isLt (outputIndex P r).isLt⟩)) := by
  simpa only [algorithm_output_is_query, selectedPoint, outputIndex] using
    algorithm_logged_query P O r (responseCount P) seeds (outputIndex P r)

end

end HeavyTailedNoise.UpperK1
