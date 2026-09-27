import HeavyTailedNoise.Lower.Randomized.GeometricEnergy
import HeavyTailedNoise.Lower.Randomized.Stationarity

/-!
Literal N-query-plus-output alignment and the actual stopped geometric
accident bound. The preselected frame law and public dimension precede the
arbitrary full-history algorithm. No conditional covariance premise occurs.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace HeavyTailedNoise.RandomizedLift

theorem ennreal_ofReal_nat_div (a b : ℕ) (hb : 0 < b) :
    ENNReal.ofReal ((a : ℝ) / (b : ℝ)) = (a : ℝ≥0∞) / (b : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb : (0 : ℝ) < b)]
  simp only [ENNReal.ofReal_natCast]

section LiteralQueries

variable {d T N j : ℕ} {Private : Type*} [MeasurableSpace Private]
variable (A : RandomAlgorithm d N Private) (r : Private)
variable (R η : ℝ) (θ : unitInterval) (tape : ℕ → Bool) (hj : j ≤ T)

theorem recordQueries_absorbedRecord_apply (U : Fin T → Point d) (t : ℕ) (i : Fin t) :
    recordQueries t (absorbedRecord A r R η θ tape hj U t) i =
      stoppedQuery A r R η θ tape i.val (absorbedRecord A r R η θ tape hj U i.val) := by
  induction t with
  | zero => exact i.elim0
  | succ t ih =>
      rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
      · simpa only [absorbedRecord, recordQueries, Fin.snoc_castSucc, Fin.val_castSucc] using ih a
      · simp only [absorbedRecord, recordQueries, Fin.snoc_last, Fin.val_last, stoppedObservation]

/-- The literal final list appends output, not another decide or advanceState. -/
def stoppedBoundedQueries (U : Fin T → Point d) : Fin (N + 1) → Point d :=
  recordQueries (N + 1) (absorbedOutputRecord A r R η θ tape hj U)

theorem measurable_stoppedBoundedQueries {R : ℝ} (hR : 0 < R) :
    Measurable (stoppedBoundedQueries A r R η θ tape hj) :=
  (measurable_recordQueries d T j (N + 1)).comp
    (measurable_absorbedOutputRecord A r η θ tape hR hj)

theorem stoppedBoundedQueries_query (U : Fin T → Point d) (i : Fin N) :
    stoppedBoundedQueries A r R η θ tape hj U i.castSucc =
      stoppedQuery A r R η θ tape i.val (absorbedRecord A r R η θ tape hj U i.val) := by
  simpa only [stoppedBoundedQueries, absorbedOutputRecord, recordQueries, Fin.snoc_castSucc] using
    recordQueries_absorbedRecord_apply A r R η θ tape hj U N i

theorem stoppedBoundedQueries_output (U : Fin T → Point d) :
    stoppedBoundedQueries A r R η θ tape hj U (Fin.last N) =
      stoppedOutputQuery A r R η θ tape (absorbedRecord A r R η θ tape hj U N) := by
  simp only [stoppedBoundedQueries, absorbedOutputRecord, recordQueries,
    Fin.snoc_last, stoppedOutputObservation]

/-- Total extension is used only for the finite deterministic telescope. -/
def stoppedQuerySequence (U : Fin T → Point d) (t : ℕ) : Point d :=
  if h : t < N + 1 then stoppedBoundedQueries A r R η θ tape hj U ⟨t, h⟩ else 0

theorem stoppedQuerySequence_query (U : Fin T → Point d) (t : ℕ) (ht : t < N) :
    stoppedQuerySequence A r R η θ tape hj U t =
      stoppedQuery A r R η θ tape t (absorbedRecord A r R η θ tape hj U t) := by
  have hi : (⟨t, Nat.lt_succ_of_lt ht⟩ : Fin (N + 1)) = (⟨t, ht⟩ : Fin N).castSucc := rfl
  rw [stoppedQuerySequence, dif_pos (Nat.lt_succ_of_lt ht), hi]
  exact stoppedBoundedQueries_query A r R η θ tape hj U ⟨t, ht⟩

theorem stoppedQuerySequence_output (U : Fin T → Point d) :
    stoppedQuerySequence A r R η θ tape hj U N =
      stoppedOutputQuery A r R η θ tape (absorbedRecord A r R η θ tape hj U N) := by
  rw [stoppedQuerySequence, dif_pos (Nat.lt_succ_self N)]
  exact stoppedBoundedQueries_output A r R η θ tape hj U

theorem growingList_eq_absorbed_list (U : Fin T → Point d) (t : ℕ) (ht : t ≤ N) :
    growingObservationList (framePrefix hj U) (stoppedQuerySequence A r R η θ tape hj U) t =
      recordObservationList t (absorbedRecord A r R η θ tape hj U t) := by
  induction t with
  | zero =>
      simp only [growingObservationList, absorbedRecord, recordObservationList,
        recordPrefix, recordQueries]
      simpa using (Fin.append_elim0 (framePrefix hj U)).symm
  | succ t ih =>
      have htn : t < N := by omega
      rw [growingObservationList, ih (by omega), stoppedQuerySequence_query A r R η θ tape hj U t htn]
      simpa only [absorbedRecord, stoppedObservation] using
        (recordObservationList_succ (absorbedRecord A r R η θ tape hj U t)
          (stoppedObservation A r R η θ tape t (absorbedRecord A r R η θ tape hj U t, U))).symm

theorem growingList_eq_output_list (U : Fin T → Point d) :
    growingObservationList (framePrefix hj U) (stoppedQuerySequence A r R η θ tape hj U) (N + 1) =
      recordObservationList (N + 1) (absorbedOutputRecord A r R η θ tape hj U) := by
  rw [growingObservationList, growingList_eq_absorbed_list A r R η θ tape hj U N le_rfl,
    stoppedQuerySequence_output A r R η θ tape hj U]
  simpa only [absorbedOutputRecord, stoppedOutputObservation] using
    (recordObservationList_succ (absorbedRecord A r R η θ tape hj U N)
      (stoppedOutputObservation A r R η θ tape (absorbedRecord A r R η θ tape hj U N, U))).symm

def stoppedColumnEnergy (U : Fin T → Point d) (i : Fin T) : ℝ :=
  (∑ t : Fin N, (inner ℝ (U i)
    (observedDirection
      (recordObservationList t.val (absorbedRecord A r R η θ tape hj U t.val))
      (stoppedQuery A r R η θ tape t.val (absorbedRecord A r R η θ tape hj U t.val)))) ^ 2) +
  (inner ℝ (U i)
    (observedDirection
      (recordObservationList N (absorbedRecord A r R η θ tape hj U N))
      (stoppedOutputQuery A r R η θ tape (absorbedRecord A r R η θ tape hj U N)))) ^ 2

theorem stoppedColumnEnergy_nonneg (U : Fin T → Point d) (i : Fin T) :
    0 ≤ stoppedColumnEnergy A r R η θ tape hj U i := by
  unfold stoppedColumnEnergy
  positivity

theorem stoppedColumnEnergy_eq_telescope (U : Fin T → Point d) (i : Fin T) :
    stoppedColumnEnergy A r R η θ tape hj U i =
      (∑ t ∈ Finset.range (N + 1),
        (inner ℝ (U i) (observedDirection
          (growingObservationList (framePrefix hj U) (stoppedQuerySequence A r R η θ tape hj U) t)
          (stoppedQuerySequence A r R η θ tape hj U t))) ^ 2) := by
  rw [Finset.sum_range_succ]
  have hs : (∑ t : Fin N, (inner ℝ (U i)
      (observedDirection
        (recordObservationList t.val (absorbedRecord A r R η θ tape hj U t.val))
        (stoppedQuery A r R η θ tape t.val (absorbedRecord A r R η θ tape hj U t.val)))) ^ 2) =
      ∑ t ∈ Finset.range N,
        (inner ℝ (U i) (observedDirection
          (growingObservationList (framePrefix hj U) (stoppedQuerySequence A r R η θ tape hj U) t)
          (stoppedQuerySequence A r R η θ tape hj U t))) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t _
    rw [growingList_eq_absorbed_list A r R η θ tape hj U t.val t.isLt.le,
      stoppedQuerySequence_query A r R η θ tape hj U t.val t.isLt]
  unfold stoppedColumnEnergy
  rw [hs, growingList_eq_absorbed_list A r R η θ tape hj U N le_rfl,
    stoppedQuerySequence_output A r R η θ tape hj U]

theorem norm_stoppedBoundedQueries_le {R : ℝ} (hR : 0 < R)
    (U : Fin T → Point d) (t : Fin (N + 1)) :
    ‖stoppedBoundedQueries A r R η θ tape hj U t‖ ≤ R := by
  rcases Fin.eq_castSucc_or_eq_last t with ⟨i, rfl⟩ | rfl
  · rw [stoppedBoundedQueries_query]
    exact norm_stoppedQuery_le (T := T) (j := j) A r hR η θ tape _ _
  · rw [stoppedBoundedQueries_output]
    exact norm_stoppedOutputQuery_le (T := T) (j := j) A r hR η θ tape _

theorem stoppedQuery_correlation_sq_le_energy {R : ℝ} (hR : 0 < R)
    (U : Fin T → Point d) (i : Fin T) (hi : j ≤ i.val) (hU : Orthonormal ℝ U)
    (t : Fin (N + 1)) :
    (inner ℝ (U i) (stoppedBoundedQueries A r R η θ tape hj U t)) ^ 2 ≤
      R ^ 2 * stoppedColumnEnergy A r R η θ tape hj U i := by
  have hu : U i ∈ (observationSpan (framePrefix hj U))ᗮ := by
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro z hz
    have hspan : observationSpan (framePrefix hj U) ≤ (innerSL ℝ (U i)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      change inner ℝ (U i) (U (Fin.castLE hj a)) = 0
      apply hU.inner_eq_zero
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castLE] at hv
      omega
    exact hspan hz
  have hq : stoppedQuerySequence A r R η θ tape hj U t.val =
      stoppedBoundedQueries A r R η θ tape hj U t := by
    simp only [stoppedQuerySequence, dif_pos t.isLt]
  rw [stoppedColumnEnergy_eq_telescope]
  rw [← hq]
  exact query_correlation_sq_le_energy (framePrefix hj U)
    (stoppedQuerySequence A r R η θ tape hj U) (U i) (N + 1) t.val t.isLt hu hR.le
    (by rw [hq]; exact norm_stoppedBoundedQueries_le A r η θ tape hj hR U t)

end LiteralQueries

/-- The deliberately conservative dimension is public before the algorithm. -/
def geometricDimension (R : ℝ) (T N : ℕ) : ℕ :=
  (N + 1) + T + 1 + ⌈128 * R ^ 2 * (N + 1 : ℕ) ^ 2 * T⌉₊

theorem geometricDimension_gt (R : ℝ) (T N : ℕ) : T + N < geometricDimension R T N := by
  unfold geometricDimension
  omega

theorem geometricDimension_residual_gt {R : ℝ} (T N : ℕ) :
    128 * R ^ 2 * (N + 1 : ℕ) ^ 2 * T <
      ((geometricDimension R T N - (T + (N + 1)) : ℕ) : ℝ) := by
  have hc := Nat.le_ceil (128 * R ^ 2 * (N + 1 : ℕ) ^ 2 * T)
  have heq : geometricDimension R T N - (T + (N + 1)) =
      1 + ⌈128 * R ^ 2 * (N + 1 : ℕ) ^ 2 * T⌉₊ := by
    unfold geometricDimension
    omega
  simp only [heq, Nat.cast_add, Nat.cast_one] at ⊢
  simp only [Nat.cast_add, Nat.cast_one] at hc
  linarith

section ActualProbability

variable {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
variable (A : RandomAlgorithm d N Private) (r : Private)
variable {R : ℝ} (hR : 0 < R) (η : ℝ) (θ : unitInterval) (tape : ℕ → Bool)
variable (hTd : T ≤ d)

def singleColumnAccident (i : Fin T) : Set {U : Fin T → Point d // Orthonormal ℝ U} :=
  {u | ∃ t : Fin (N + 1), (1 / 4 : ℝ) ≤
    |inner ℝ (u.1 i) (stoppedBoundedQueries A r R η θ tape i.isLt.le u.1 t)|}

def geometricAccident : Set {U : Fin T → Point d // Orthonormal ℝ U} :=
  ⋃ i : Fin T, singleColumnAccident A r (R := R) η θ tape i

section AccidentMeasurability

attribute [local irreducible] stoppedBoundedQueries singleColumnAccident

include hR in
theorem measurableSet_singleColumnAccident (i : Fin T) :
    MeasurableSet (singleColumnAccident A r (R := R) η θ tape i) := by
  have hq : Measurable (fun u : {U : Fin T → Point d // Orthonormal ℝ U} =>
      stoppedBoundedQueries A r R η θ tape i.isLt.le u.1) :=
    (measurable_stoppedBoundedQueries A r η θ tape i.isLt.le hR).comp measurable_subtype_coe
  have hi : Measurable (fun u : {U : Fin T → Point d // Orthonormal ℝ U} => u.1 i) :=
    (measurable_pi_apply i).comp measurable_subtype_coe
  simp only [singleColumnAccident]
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro t
  exact measurableSet_le measurable_const (hi.inner ((measurable_pi_apply t).comp hq)).abs

include hR in
theorem measurableSet_geometricAccident :
    MeasurableSet (geometricAccident A r (T := T) (R := R) η θ tape) :=
  MeasurableSet.iUnion (measurableSet_singleColumnAccident A r (R := R) hR η θ tape)

end AccidentMeasurability

theorem stoppedColumnEnergy_eq_actualTotalEnergy {j k : ℕ} (hT : j + k ≤ d)
    (u : {U : Fin (j + k) → Point d // Orthonormal ℝ U}) (i : Fin (j + k)) :
    ENNReal.ofReal (stoppedColumnEnergy A r R η θ tape (Nat.le_add_right j k) u.1 i) =
      actualStoppedTotalEnergy A r (R := R) η θ tape i u := by
  rw [stoppedColumnEnergy, ENNReal.ofReal_add (by positivity) (sq_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [actualStoppedTotalEnergy, actualStoppedResponseEnergy, actualStoppedOutputEnergy,
    actualStoppedRecord]

include hR in
theorem measurable_stoppedColumnEnergy {j k : ℕ} (hT : j + k ≤ d)
    (i : Fin (j + k)) :
    Measurable (fun u : {U : Fin (j + k) → Point d // Orthonormal ℝ U} =>
      ENNReal.ofReal (stoppedColumnEnergy A r R η θ tape (Nat.le_add_right j k) u.1 i)) := by
  have heq : (fun u : {U : Fin (j + k) → Point d // Orthonormal ℝ U} =>
      ENNReal.ofReal (stoppedColumnEnergy A r R η θ tape (Nat.le_add_right j k) u.1 i)) =
      actualStoppedTotalEnergy A r (R := R) η θ tape i := by
    funext u
    exact stoppedColumnEnergy_eq_actualTotalEnergy A r η θ tape hT u i
  rw [heq]
  exact measurable_actualStoppedTotalEnergy A r (R := R) hR η θ tape i

include hR in
theorem singleColumnAccident_probability_le_sum (hd : T + N < d) (i : Fin T)
    {j k : ℕ} (hsum : T = j + k) (hi : i.val = j) :
    preselectedOrthonormalFrameLaw d T hTd (singleColumnAccident A r (R := R) η θ tape i) ≤
      ENNReal.ofReal (16 * R ^ 2 * (N + 1 : ℕ) / ((d - (T + N) : ℕ) : ℝ)) := by
  subst T
  let E := fun u : {U : Fin (j + k) → Point d // Orthonormal ℝ U} =>
    ENNReal.ofReal (stoppedColumnEnergy A r R η θ tape (Nat.le_add_right j k) u.1 i)
  have hE : Measurable E := measurable_stoppedColumnEnergy A r hR η θ tape hTd i
  have hsub : singleColumnAccident A r (R := R) η θ tape i ⊆
      {u | (1 : ℝ≥0∞) ≤ ENNReal.ofReal (16 * R ^ 2) * E u} := by
    intro u hu
    obtain ⟨t, ht⟩ := hu
    have hc := stoppedQuery_correlation_sq_le_energy A r η θ tape i.isLt.le hR u.1 i
      (by simpa only [hi] using le_rfl) u.2 t
    have hs : (1 / 16 : ℝ) ≤
        (inner ℝ (u.1 i) (stoppedBoundedQueries A r R η θ tape i.isLt.le u.1 t)) ^ 2 := by
      have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) (abs_nonneg _)).mpr ht
      norm_num only [sq_abs] at hh
      exact hh
    have hb : (1 : ℝ) ≤ 16 * R ^ 2 *
        stoppedColumnEnergy A r R η θ tape i.isLt.le u.1 i := by nlinarith
    change 1 ≤ ENNReal.ofReal (16 * R ^ 2) * E u
    rw [← ENNReal.ofReal_mul (by positivity)]
    simpa only [E, hi, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hb
  have hweighted : Measurable
      (fun u : {U : Fin (j + k) → Point d // Orthonormal ℝ U} =>
        ENNReal.ofReal (16 * R ^ 2) * E u) := measurable_const.mul hE
  have hmarkov : (preselectedOrthonormalFrameLaw d (j + k) hTd)
      {u | (1 : ℝ≥0∞) ≤ ENNReal.ofReal (16 * R ^ 2) * E u} ≤
      ∫⁻ u, ENNReal.ofReal (16 * R ^ 2) * E u
        ∂preselectedOrthonormalFrameLaw d (j + k) hTd := by
    simpa only [one_mul] using mul_meas_ge_le_lintegral
      (μ := preselectedOrthonormalFrameLaw d (j + k) hTd) hweighted (1 : ℝ≥0∞)
  have hbudget := actualStoppedTotalEnergy_expectation A r hR η θ tape hTd
    (show j + N < d by omega) i
  have heq : E = actualStoppedTotalEnergy A r (R := R) η θ tape i := by
    funext u
    exact stoppedColumnEnergy_eq_actualTotalEnergy A r η θ tape hTd u i
  calc
    _ ≤ (preselectedOrthonormalFrameLaw d (j + k) hTd)
        {u | 1 ≤ ENNReal.ofReal (16 * R ^ 2) * E u} := measure_mono hsub
    _ ≤ ∫⁻ u, ENNReal.ofReal (16 * R ^ 2) * E u
        ∂preselectedOrthonormalFrameLaw d (j + k) hTd := hmarkov
    _ = ENNReal.ofReal (16 * R ^ 2) *
        ∫⁻ u, actualStoppedTotalEnergy A r (R := R) η θ tape i u
          ∂preselectedOrthonormalFrameLaw d (j + k) hTd := by
      rw [heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (16 * R ^ 2) *
        (((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / ((d - (j + N) : ℕ) : ℝ))) :=
      mul_le_mul' le_rfl hbudget
    _ ≤ _ := by
      have hp : (0 : ℝ) < ((d - ((j + k) + N) : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt hd
      have hden : ((d - ((j + k) + N) : ℕ) : ℝ) ≤ ((d - (j + N) : ℕ) : ℝ) := by
        exact_mod_cast (show d - ((j + k) + N) ≤ d - (j + N) by omega)
      have hm := ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hp hden)
      have hh := mul_le_mul' (le_refl (ENNReal.ofReal (16 * R ^ 2)))
        (mul_le_mul' (le_refl ((N + 1 : ℕ) : ℝ≥0∞)) hm)
      convert hh using 1
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1 <;> ring

include hR in
theorem singleColumnAccident_probability_le (hd : T + N < d) (i : Fin T) :
    preselectedOrthonormalFrameLaw d T hTd (singleColumnAccident A r (R := R) η θ tape i) ≤
      ENNReal.ofReal (16 * R ^ 2 * (N + 1 : ℕ) / ((d - (T + N) : ℕ) : ℝ)) :=
  singleColumnAccident_probability_le_sum (j := i.val) (k := T - i.val) A r hR η θ tape hTd hd i
    (Nat.add_sub_of_le i.isLt.le).symm rfl

include hR in
theorem geometricAccident_probability_le (hd : T + N < d) :
    preselectedOrthonormalFrameLaw d T hTd (geometricAccident A r (T := T) (R := R) η θ tape) ≤
      ENNReal.ofReal (16 * R ^ 2 * (N + 1 : ℕ) * T / ((d - (T + N) : ℕ) : ℝ)) := by
  calc
    _ ≤ ∑ i : Fin T, preselectedOrthonormalFrameLaw d T hTd
        (singleColumnAccident A r (R := R) η θ tape i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin T,
        ENNReal.ofReal (16 * R ^ 2 * (N + 1 : ℕ) / ((d - (T + N) : ℕ) : ℝ)) :=
      Finset.sum_le_sum (fun i _ => singleColumnAccident_probability_le A r hR η θ tape hTd hd i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1 <;> ring

include hR in
/-- The actual geometry estimate: public dimension and no stochastic premises. -/
theorem geometricAccident_probability_eighth (hT : 0 < T)
    (hd : geometricDimension R T N ≤ d) :
    preselectedOrthonormalFrameLaw d T hTd (geometricAccident A r (T := T) (R := R) η θ tape) ≤ (1/8 : ℝ≥0∞) := by
  have hdn : T + N < d := (geometricDimension_gt R T N).trans_le hd
  apply (geometricAccident_probability_le A r hR η θ tape hTd hdn).trans
  have hpos : (0 : ℝ) < ((d - (T + N) : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hdn
  have hres := geometricDimension_residual_gt (R := R) T N
  have hden : ((geometricDimension R T N - (T + (N + 1)) : ℕ) : ℝ) ≤
      ((d - (T + N) : ℕ) : ℝ) := by
    exact_mod_cast (show geometricDimension R T N - (T + (N + 1)) ≤ d - (T + N) by omega)
  have hn : (1 : ℝ) ≤ N + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hm : (N + 1 : ℝ) ≤ (N + 1 : ℝ) ^ 2 := by nlinarith
  simp only [Nat.cast_add, Nat.cast_one] at hres
  have hb : 16 * R ^ 2 * (N + 1 : ℕ) * T / ((d - (T + N) : ℕ) : ℝ) ≤ (1/8 : ℝ) := by
    apply (div_le_iff₀ hpos).mpr
    have hc : 128 * R ^ 2 * (N + 1 : ℝ) * T ≤ 128 * R ^ 2 * (N + 1 : ℝ) ^ 2 * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) (Nat.cast_nonneg T)
    have hlo := hc.trans (hres.trans_le hden).le
    simp only [Nat.cast_add, Nat.cast_one] at ⊢
    nlinarith [hlo]
  have he : ENNReal.ofReal (1/8 : ℝ) = (1/8 : ℝ≥0∞) := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using ennreal_ofReal_nat_div 1 8 (by decide)
  rw [← he]
  exact ENNReal.ofReal_le_ofReal hb

end ActualProbability

theorem probability_compl_ge_seven_eighths {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) (hs : MeasurableSet s)
    (hbad : μ s ≤ (1/8 : ℝ≥0∞)) : (7/8 : ℝ≥0∞) ≤ μ sᶜ := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (measure_ne_top μ sᶜ)).mp
  have heq := congrArg ENNReal.toReal (measure_add_measure_compl (μ := μ) hs)
  rw [ENNReal.toReal_add (measure_ne_top μ s) (measure_ne_top μ sᶜ), measure_univ] at heq
  have hb := (ENNReal.toReal_le_toReal (measure_ne_top μ s) (by finiteness)).mpr hbad
  norm_num [ENNReal.toReal_div] at hb heq ⊢
  linarith

end HeavyTailedNoise.RandomizedLift
