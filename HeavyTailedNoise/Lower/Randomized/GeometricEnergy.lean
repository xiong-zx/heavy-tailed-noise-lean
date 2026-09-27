import HeavyTailedNoise.Lower.Randomized.ConditionalMoments

/-!
Nested observed-span projections: exact rank-one updates, orthogonal
increments, telescoping energy, and bounded-query correlations. Zero
residuals contribute zero. These are deterministic Euclidean identities.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace HeavyTailedNoise.RandomizedLift

def observedProjection {d n : ℕ} (v : Fin n → Point d) : Point d →L[ℝ] Point d :=
  (observationSpan v).starProjection

theorem observedResidual_eq_sub_projection {d n : ℕ} (v : Fin n → Point d)
    (x : Point d) : observedResidual v x = x - observedProjection v x := by
  rw [observedResidual_eq_starProjection, Submodule.starProjection_orthogonal_val]
  rfl

theorem observationSpan_le_snoc {d n : ℕ} (v : Fin n → Point d) (q : Point d) :
    observationSpan v ≤ observationSpan (Fin.snoc v q) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i.castSucc, by simp only [Fin.snoc_castSucc]⟩

theorem observedDirection_mem_snoc {d n : ℕ} (v : Fin n → Point d) (q : Point d) :
    observedDirection v q ∈ observationSpan (Fin.snoc v q) := by
  apply Submodule.smul_mem
  rw [observedResidual_eq_sub_projection]
  apply Submodule.sub_mem
  · exact Submodule.subset_span ⟨Fin.last n, Fin.snoc_last _ _⟩
  · exact observationSpan_le_snoc v q ((observationSpan v).starProjection_apply_mem q)

theorem norm_smul_observedDirection {d n : ℕ} (v : Fin n → Point d) (q : Point d) :
    ‖observedResidual v q‖ • observedDirection v q = observedResidual v q := by
  by_cases h : observedResidual v q = 0
  · simp [h, observedDirection_zero v q h]
  · rw [observedDirection, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]

theorem query_eq_projection_add_direction {d n : ℕ} (v : Fin n → Point d)
    (q : Point d) :
    q = observedProjection v q + ‖observedResidual v q‖ • observedDirection v q := by
  rw [norm_smul_observedDirection, observedResidual_eq_sub_projection]
  abel

theorem projection_inner_direction_eq_zero {d n : ℕ} (v : Fin n → Point d)
    (q u : Point d) : inner ℝ (observedProjection v u) (observedDirection v q) = 0 :=
  Submodule.inner_right_of_mem_orthogonal
    ((observationSpan v).starProjection_apply_mem u) (observedDirection_mem_orthogonal v q)

/-- The actual span extension is rank one; a dependent query has zero update. -/
theorem observedProjection_snoc_apply {d n : ℕ} (v : Fin n → Point d)
    (q u : Point d) :
    observedProjection (Fin.snoc v q) u = observedProjection v u +
      (inner ℝ u (observedDirection v q)) • observedDirection v q := by
  classical
  let S := observationSpan v
  let V := observationSpan (Fin.snoc v q)
  let e := observedDirection v q
  let c := inner ℝ u e
  let y := observedProjection v u + c • e
  have hy : y ∈ V := V.add_mem
    (observationSpan_le_snoc v q (S.starProjection_apply_mem u))
    (V.smul_mem c (observedDirection_mem_snoc v q))
  have horthS : ∀ z ∈ S, inner ℝ (u - y) z = 0 := by
    intro z hz
    have hp := S.starProjection_inner_eq_zero u z hz
    have he : inner ℝ e z = 0 := by
      rw [real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal hz (observedDirection_mem_orthogonal v q)
    dsimp [y, observedProjection] at *
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, he, mul_zero, add_zero] at *
    exact hp
  have he : inner ℝ (u - y) e = 0 := by
    by_cases hr : observedResidual v q = 0
    · have hz : e = 0 := observedDirection_zero v q hr
      simp [hz]
    · have hunit : ‖e‖ = 1 := norm_observedDirection v q hr
      have hself : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, hunit]; norm_num
      have hp : inner ℝ (observedProjection v u) e = 0 := projection_inner_direction_eq_zero v q u
      dsimp [y, c]
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hp, hself, mul_one,
        zero_add, sub_self]
  have hq : inner ℝ (u - y) q = 0 := by
    rw [query_eq_projection_add_direction v q, inner_add_right, real_inner_smul_right]
    change inner ℝ (u - y) (S.starProjection q) +
      ‖observedResidual v q‖ * inner ℝ (u - y) e = 0
    rw [horthS _ (S.starProjection_apply_mem q), he]
    ring
  have hker : V ≤ (innerSL ℝ (u - y)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
    · change inner ℝ (u - y) ((Fin.snoc v q : Fin (n + 1) → Point d) i.castSucc) = 0
      simpa only [Fin.snoc_castSucc] using horthS (v i) (Submodule.subset_span ⟨i, rfl⟩)
    · change inner ℝ (u - y) ((Fin.snoc v q : Fin (n + 1) → Point d) (Fin.last n)) = 0
      simpa only [Fin.snoc_last] using hq
  exact V.eq_starProjection_of_mem_of_inner_eq_zero hy
    (fun z hz => hker hz)

theorem observedProjection_snoc_sub {d n : ℕ} (v : Fin n → Point d)
    (q u : Point d) :
    observedProjection (Fin.snoc v q) u - observedProjection v u =
      (inner ℝ u (observedDirection v q)) • observedDirection v q := by
  rw [observedProjection_snoc_apply]
  abel

theorem observedProjection_snoc_energy {d n : ℕ} (v : Fin n → Point d)
    (q u : Point d) :
    ‖observedProjection (Fin.snoc v q) u‖ ^ 2 =
      ‖observedProjection v u‖ ^ 2 + (inner ℝ u (observedDirection v q)) ^ 2 := by
  rw [observedProjection_snoc_apply, norm_add_sq_real]
  have hcross : inner ℝ (observedProjection v u)
      ((inner ℝ u (observedDirection v q)) • observedDirection v q) = 0 := by
    rw [real_inner_smul_right, projection_inner_direction_eq_zero, mul_zero]
  rw [hcross, mul_zero, add_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  by_cases hr : observedResidual v q = 0
  · simp [observedDirection_zero v q hr]
  · rw [norm_observedDirection v q hr]
    ring

/-- A varying list with one appended observation at each time. -/
def growingObservationList {d j : ℕ} (v : Fin j → Point d) (q : ℕ → Point d) :
    (t : ℕ) → Fin (j + t) → Point d
  | 0 => v
  | t + 1 => Fin.snoc (growingObservationList v q t) (q t)

def growingObservationSpan {d j : ℕ} (v : Fin j → Point d)
    (q : ℕ → Point d) (t : ℕ) : Submodule ℝ (Point d) :=
  observationSpan (growingObservationList v q t)

theorem growingObservationSpan_mono {d j : ℕ} (v : Fin j → Point d)
    (q : ℕ → Point d) : Monotone (growingObservationSpan v q) := by
  apply monotone_nat_of_le_succ
  intro t
  exact observationSpan_le_snoc _ _

theorem growingObservationSpan_query_mem {d j : ℕ} (v : Fin j → Point d)
    (q : ℕ → Point d) (t : ℕ) : q t ∈ growingObservationSpan v q (t + 1) :=
  Submodule.subset_span ⟨Fin.last (j + t), Fin.snoc_last _ _⟩

def projectionIncrement {d j : ℕ} (v : Fin j → Point d) (q : ℕ → Point d)
    (u : Point d) (t : ℕ) : Point d :=
  observedProjection (growingObservationList v q (t + 1)) u -
    observedProjection (growingObservationList v q t) u

theorem projectionIncrement_mem_next {d j : ℕ} (v : Fin j → Point d)
    (q : ℕ → Point d) (u : Point d) (t : ℕ) :
    projectionIncrement v q u t ∈ growingObservationSpan v q (t + 1) := by
  exact Submodule.sub_mem _ ((growingObservationSpan v q (t + 1)).starProjection_apply_mem u)
    (growingObservationSpan_mono v q (Nat.le_succ t)
      ((growingObservationSpan v q t).starProjection_apply_mem u))

theorem projectionIncrement_mem_old_orthogonal {d j : ℕ} (v : Fin j → Point d)
    (q : ℕ → Point d) (u : Point d) (t : ℕ) :
    projectionIncrement v q u t ∈ (growingObservationSpan v q t)ᗮ := by
  rw [projectionIncrement, growingObservationList, observedProjection_snoc_sub]
  exact Submodule.smul_mem _ _ (observedDirection_mem_orthogonal _ _)

/-- Different-time increments are orthogonal, even for dependent queries. -/
theorem projectionIncrement_inner_eq_zero {d j : ℕ} (v : Fin j → Point d)
    (q : ℕ → Point d) (u : Point d) {s t : ℕ} (hst : s < t) :
    inner ℝ (projectionIncrement v q u s) (projectionIncrement v q u t) = 0 := by
  exact Submodule.inner_right_of_mem_orthogonal
    (growingObservationSpan_mono v q (Nat.succ_le_of_lt hst)
      (projectionIncrement_mem_next v q u s))
    (projectionIncrement_mem_old_orthogonal v q u t)

/-- Exact energy telescoping; the prefix projection is retained explicitly. -/
theorem observed_energy_telescope {d j : ℕ} (v : Fin j → Point d)
    (q : ℕ → Point d) (u : Point d) (n : ℕ) :
    (∑ t ∈ Finset.range n,
      (inner ℝ u (observedDirection (growingObservationList v q t) (q t))) ^ 2) =
      ‖observedProjection (growingObservationList v q n) u‖ ^ 2 -
        ‖observedProjection v u‖ ^ 2 := by
  induction n with
  | zero => simp [growingObservationList]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hs := observedProjection_snoc_energy (growingObservationList v q n) (q n) u
      change _ = ‖observedProjection (Fin.snoc (growingObservationList v q n) (q n)) u‖ ^ 2 - _
      linarith

theorem observed_energy_le_norm_sq {d j : ℕ} (v : Fin j → Point d)
    (q : ℕ → Point d) (u : Point d) (n : ℕ) :
    (∑ t ∈ Finset.range n,
      (inner ℝ u (observedDirection (growingObservationList v q t) (q t))) ^ 2) ≤ ‖u‖ ^ 2 := by
  rw [observed_energy_telescope]
  have hn := (observationSpan (growingObservationList v q n)).norm_starProjection_apply_le u
  change ‖observedProjection (growingObservationList v q n) u‖ ≤ ‖u‖ at hn
  nlinarith [norm_nonneg u, norm_nonneg (observedProjection (growingObservationList v q n) u),
    sq_nonneg ‖observedProjection v u‖]

theorem observed_projection_zero_of_orthogonal {d j : ℕ}
    (v : Fin j → Point d) (u : Point d) (hu : u ∈ (observationSpan v)ᗮ) :
    observedProjection v u = 0 := by
  exact (observationSpan v).starProjection_apply_eq_zero_iff.mpr hu

/-- Every old query correlation is controlled by the final observation energy. -/
theorem query_correlation_sq_le_energy {d j : ℕ} (v : Fin j → Point d)
    (q : ℕ → Point d) (u : Point d) (n t : ℕ) (ht : t < n)
    (hu : u ∈ (observationSpan v)ᗮ) {R : ℝ} (hR : 0 ≤ R) (hq : ‖q t‖ ≤ R) :
    (inner ℝ u (q t)) ^ 2 ≤ R ^ 2 *
      (∑ s ∈ Finset.range n,
        (inner ℝ u (observedDirection (growingObservationList v q s) (q s))) ^ 2) := by
  let S := growingObservationSpan v q n
  have hmem : q t ∈ S := growingObservationSpan_mono v q (Nat.succ_le_of_lt ht)
    (growingObservationSpan_query_mem v q t)
  have hp : inner ℝ u (q t) = inner ℝ (S.starProjection u) (q t) := by
    have h := S.starProjection_inner_eq_zero u (q t) hmem
    rw [inner_sub_left] at h
    exact sub_eq_zero.mp h
  have hi : |inner ℝ u (q t)| ≤ ‖S.starProjection u‖ * R := by
    rw [hp]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) hR)).mpr hi
  rw [sq_abs, mul_pow] at hs
  rw [observed_energy_telescope, observed_projection_zero_of_orthogonal v u hu,
    norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
  simpa only [S, growingObservationSpan, observedProjection, mul_comm] using hs

section ActualExperiment

variable {d N j k : ℕ} {Private : Type*} [MeasurableSpace Private]
variable (A : RandomAlgorithm d N Private) (r : Private)
variable {R : ℝ} (hR : 0 < R) (η : ℝ) (θ : unitInterval) (tape : ℕ → Bool)
variable (hT : j + k ≤ d)

/-- One directional energy of the literal stopped responsive query. -/
def actualStoppedResponseEnergy (i : Fin (j + k)) (t : Fin N)
    (u : {U : Fin (j + k) → Point d // Orthonormal ℝ U}) : ℝ≥0∞ :=
  let c : StoppedRecord d (j + k) j t.val :=
    actualStoppedRecord (j := j) (k := k) A r R η θ tape t.val u
  ENNReal.ofReal ((inner ℝ (u.1 i)
    (observedDirection (recordObservationList t.val c)
      (stoppedQuery A r R η θ tape t.val c))) ^ 2)

/-- The last analysis energy uses A.output and consumes no new response. -/
def actualStoppedOutputEnergy (i : Fin (j + k))
    (u : {U : Fin (j + k) → Point d // Orthonormal ℝ U}) : ℝ≥0∞ :=
  let c : StoppedRecord d (j + k) j N :=
    actualStoppedRecord (j := j) (k := k) A r R η θ tape N u
  ENNReal.ofReal ((inner ℝ (u.1 i)
    (observedDirection (recordObservationList N c)
      (stoppedOutputQuery A r R η θ tape c))) ^ 2)

def actualStoppedTotalEnergy (i : Fin (j + k))
    (u : {U : Fin (j + k) → Point d // Orthonormal ℝ U}) : ℝ≥0∞ :=
  (∑ t : Fin N, actualStoppedResponseEnergy A r (R := R) η θ tape i t u) +
    actualStoppedOutputEnergy A r (R := R) η θ tape i u

include hR in
@[fun_prop] theorem measurable_actualStoppedResponseEnergy (i : Fin (j + k)) (t : Fin N) :
    Measurable (actualStoppedResponseEnergy A r (R := R) η θ tape i t) := by
  let c : {U : Fin (j + k) → Point d // Orthonormal ℝ U} → StoppedRecord d (j + k) j t.val :=
    actualStoppedRecord (j := j) (k := k) A r R η θ tape t.val
  have hc : Measurable c := measurable_actualStoppedRecord A r hR η θ tape t.val
  have hv := (measurable_recordObservationList d (j + k) j t.val).comp hc
  have hq := (measurable_stoppedQuery A r η θ tape hR t.val).comp hc
  have he := (measurable_observedDirection d (j + t.val)).comp (hv.prodMk hq)
  exact ENNReal.measurable_ofReal.comp
    ((((measurable_pi_apply i).comp measurable_subtype_coe).inner he).pow_const 2)

include hR in
@[fun_prop] theorem measurable_actualStoppedOutputEnergy (i : Fin (j + k)) :
    Measurable (actualStoppedOutputEnergy A r (R := R) η θ tape i) := by
  let c : {U : Fin (j + k) → Point d // Orthonormal ℝ U} → StoppedRecord d (j + k) j N :=
    actualStoppedRecord (j := j) (k := k) A r R η θ tape N
  have hc : Measurable c := measurable_actualStoppedRecord A r hR η θ tape N
  have hv := (measurable_recordObservationList d (j + k) j N).comp hc
  have hq := (measurable_stoppedOutputQuery A r η θ tape hR).comp hc
  have he := (measurable_observedDirection d (j + N)).comp (hv.prodMk hq)
  exact ENNReal.measurable_ofReal.comp
    ((((measurable_pi_apply i).comp measurable_subtype_coe).inner he).pow_const 2)

include hR in
@[fun_prop] theorem measurable_actualStoppedTotalEnergy (i : Fin (j + k)) :
    Measurable (actualStoppedTotalEnergy A r (R := R) η θ tape i) := by
  exact (Finset.measurable_sum Finset.univ
    (fun t _ => measurable_actualStoppedResponseEnergy A r (R := R) hR η θ tape i t)).add
    (measurable_actualStoppedOutputEnergy A r (R := R) hR η θ tape i)

include hR in
/-- Actual prior response-direction expectation, including absorbed zero
queries. This theorem uses the discharged actual conditional-moment result. -/
theorem actualStoppedResponseEnergy_expectation (hd : j + N < d)
    (i : Fin (j + k)) (t : Fin N) :
    (∫⁻ u, actualStoppedResponseEnergy A r (R := R) η θ tape i t u
      ∂preselectedOrthonormalFrameLaw d (j + k) hT) ≤
        ENNReal.ofReal (1 / ((d - (j + N) : ℕ) : ℝ)) := by
  have ht : j + t.val < d := by omega
  have h := actualStopped_observedDirection_moment A r hR η θ tape hT t.val ht
    (stoppedQuery A r R η θ tape t.val)
    (measurable_stoppedQuery A r η θ tape hR t.val) i
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hpos : (0 : ℝ) < ((d - (j + N) : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hd
  have hle : ((d - (j + N) : ℕ) : ℝ) ≤ ((d - (j + t.val) : ℕ) : ℝ) := by
    exact_mod_cast (show d - (j + N) ≤ d - (j + t.val) by omega)
  exact one_div_le_one_div_of_le hpos hle

include hR in
/-- No posterior update, seed or response at time N is required for output. -/
theorem actualStoppedOutputEnergy_expectation (hd : j + N < d)
    (i : Fin (j + k)) :
    (∫⁻ u, actualStoppedOutputEnergy A r (R := R) η θ tape i u
      ∂preselectedOrthonormalFrameLaw d (j + k) hT) ≤
        ENNReal.ofReal (1 / ((d - (j + N) : ℕ) : ℝ)) :=
  actualStopped_observedDirection_moment A r hR η θ tape hT N hd
    (stoppedOutputQuery A r R η θ tape)
    (measurable_stoppedOutputQuery A r η θ tape hR) i

include hR in
/-- N responsive observations plus the true response-free output. Every
stochastic moment input is proved from the actual preselected experiment. -/
theorem actualStoppedTotalEnergy_expectation (hd : j + N < d)
    (i : Fin (j + k)) :
    (∫⁻ u, actualStoppedTotalEnergy A r (R := R) η θ tape i u
      ∂preselectedOrthonormalFrameLaw d (j + k) hT) ≤
        ((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / ((d - (j + N) : ℕ) : ℝ)) := by
  change (∫⁻ u, (∑ t : Fin N, actualStoppedResponseEnergy A r (R := R) η θ tape i t u) +
    actualStoppedOutputEnergy A r (R := R) η θ tape i u
    ∂preselectedOrthonormalFrameLaw d (j + k) hT) ≤ _
  rw [lintegral_add_left
      (Finset.measurable_sum Finset.univ
        (fun t _ => measurable_actualStoppedResponseEnergy A r (R := R) hR η θ tape i t)),
    lintegral_finsetSum Finset.univ
      (fun t _ => measurable_actualStoppedResponseEnergy A r (R := R) hR η θ tape i t)]
  calc
    _ ≤ (∑ _t : Fin N, ENNReal.ofReal (1 / ((d - (j + N) : ℕ) : ℝ))) +
        ENNReal.ofReal (1 / ((d - (j + N) : ℕ) : ℝ)) :=
      add_le_add (Finset.sum_le_sum (fun t _ =>
        actualStoppedResponseEnergy_expectation A r hR η θ tape hT hd i t))
        (actualStoppedOutputEnergy_expectation A r hR η θ tape hT hd i)
    _ = _ := by simp [Nat.cast_add, add_mul]

include hR in
theorem norm_stoppedQuery_le {T : ℕ} (t : ℕ) (c : StoppedRecord d T j t) :
    ‖stoppedQuery A r R η θ tape t c‖ ≤ R := by
  unfold stoppedQuery
  split_ifs
  · exact (norm_softProjection_lt_radius hR _).le
  · simpa using hR.le

include hR in
theorem norm_stoppedOutputQuery_le {T : ℕ} (c : StoppedRecord d T j N) :
    ‖stoppedOutputQuery A r R η θ tape c‖ ≤ R := by
  unfold stoppedOutputQuery
  split_ifs
  · exact (norm_softProjection_lt_radius hR _).le
  · simpa using hR.le

end ActualExperiment

end HeavyTailedNoise.RandomizedLift
