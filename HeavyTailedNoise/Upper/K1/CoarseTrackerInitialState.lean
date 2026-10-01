import HeavyTailedNoise.Upper.K1.CoarseTrackerBoundaryProcess

/-!
The optional independent high-band initialization changes memories only.
Across the first raw response and every optional initialization response,
the actual algorithm keeps point zero and the raw first response as center.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem center_step_initial {d : ℕ} (t : ℕ)
    (s : State d P.J) (y : Point d)
    (ht0 : t ≠ 0) (ht : t < 1 + initialResponses P) :
    center P (step P t s y) = center P s := by
  simp only [step, if_neg ht0, if_pos ht]
  split_ifs <;> rfl

theorem foldResponses_initial_point_center {d : ℕ}
    (s : State d P.J) (k : ℕ) (hk : k ≤ initialResponses P)
    (ys : Fin k → Point d) :
    point P (foldResponses P 1 s k ys) = point P s ∧
      center P (foldResponses P 1 s k ys) = center P s := by
  induction k with
  | zero => simp [foldResponses]
  | succ k ih =>
      have hkprev : k ≤ initialResponses P := by omega
      have hprev := ih hkprev (fun i => ys i.castSucc)
      have hindex : 1 + k ≠ 0 := by omega
      have hinitial : 1 + k < 1 + initialResponses P := by omega
      constructor
      · rw [foldResponses_succ,
          point_step_initial P (1 + k)
            (foldResponses P 1 s k (fun i => ys i.castSucc))
            (ys (Fin.last k)) hindex hinitial]
        exact hprev.1
      · rw [foldResponses_succ,
          center_step_initial P (1 + k)
            (foldResponses P 1 s k (fun i => ys i.castSucc))
            (ys (Fin.last k)) hindex hinitial]
        exact hprev.2

theorem stateAt_firstResponse_point_center {d : ℕ}
    (H : Transcript d 1) :
    point P (stateAt P 1 H) = 0 ∧
      center P (stateAt P 1 H) = (H ⟨0, by norm_num⟩).2 := by
  constructor <;> simp [stateAt, step, initialState, point, center]

/-- The real first runtime-batch state has its initial point and center
exactly as specified in `alg:k1`, independently of whether `nI` was used. -/
theorem stateAt_firstRuntime_point_center {d : ℕ}
    (H : Transcript d (batchStart P 0)) :
    point P (stateAt P (batchStart P 0) H) = 0 ∧
      center P (stateAt P (batchStart P 0) H) =
        (H ⟨0, by dsimp [batchStart]; omega⟩).2 := by
  have htime : batchStart P 0 = 1 + initialResponses P := by
    simp [batchStart]
  let H' : Transcript d (1 + initialResponses P) :=
    fun i => H (i.cast htime.symm)
  have hstate : stateAt P (batchStart P 0) H =
      stateAt P (1 + initialResponses P) H' :=
    (stateAt_transcript_cast P htime H).symm
  have hfold := stateAt_eq_foldResponses P 1 (initialResponses P) H'
  have hinit := foldResponses_initial_point_center P
    (stateAt P 1 (transcriptPrefix 1 (initialResponses P) H'))
    (initialResponses P) (le_refl _)
    (transcriptBlockResponses 1 (initialResponses P) H')
  have hfirst := stateAt_firstResponse_point_center P
    (transcriptPrefix 1 (initialResponses P) H')
  constructor
  · rw [hstate, hfold]
    exact hinit.1.trans hfirst.1
  · rw [hstate, hfold]
    rw [hinit.2, hfirst.2]
    congr 1

/-- The actual initial tracker error is the original centered oracle error
of the *single* first fresh response.  Optional `nI` responses do not enter
its point or center. -/
theorem actualTrackerAtBoundary_zero_eq_firstResponse
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    actualTrackerAtBoundary P I 0 z =
      trackerError I 0
        (I.oracle.response 0 (z.2 ⟨0, responseCount_pos P⟩)) := by
  have hzero : 0 ≤ P.T := Nat.zero_le _
  let H := boundaryTranscript P I.oracle 0 hzero z
  have hstate := stateAt_firstRuntime_point_center P H
  have hOne : 1 ≤ responseCount P :=
    Nat.succ_le_iff.mpr (responseCount_pos P)
  let seeds1 : Fin 1 → Seed := fun i =>
    z.2 (i.castLE hOne)
  have hprefix := runTranscript_prefix_le I.oracle (algorithm (d := d) P)
    z.1 1 (responseCount P) hOne
    z.2 (⟨0, by norm_num⟩ : Fin 1)
  have hfirstLog := algorithm_last_response P I.oracle z.1 0 seeds1
  have hfirstIndex : (⟨0, by norm_num⟩ : Fin 1) = Fin.last 0 :=
    Fin.ext rfl
  rw [hfirstIndex] at hprefix
  have hseed : seeds1 (Fin.last 0) =
      z.2 ⟨0, responseCount_pos P⟩ := by
    exact congrArg z.2 (Fin.ext rfl)
  have hfirst :
      (H ⟨0, by dsimp [batchStart]; omega⟩).2 =
        I.oracle.response 0 (z.2 ⟨0, responseCount_pos P⟩) := by
    have hpair := hprefix.trans hfirstLog
    have hresp := congrArg Prod.snd hpair
    have hindex :
        (H ⟨0, by dsimp [batchStart]; omega⟩).2 =
        (runTranscript I.oracle (algorithm (d := d) P) z.1
          (responseCount P) z.2
          ((Fin.last 0).castLE hOne)).2 := by
      change (runTranscript I.oracle (algorithm (d := d) P) z.1
        (responseCount P) z.2
        ((⟨0, by dsimp [batchStart]; omega⟩ : Fin (batchStart P 0)).castLE
          (batchStart_le_responseCount_of_le P 0 hzero))).2 = _
      exact congrArg Prod.snd (congrArg
        (runTranscript I.oracle (algorithm (d := d) P) z.1
          (responseCount P) z.2) (Fin.ext rfl))
    rw [hindex]
    rw [hseed] at hresp
    simpa only [query_zero] using hresp
  simp only [actualTrackerAtBoundary, dif_pos hzero]
  rw [hstate.1, hstate.2, hfirst]

/-- The original centered oracle `p`-moment controls the actual algorithm's
initial tracker error, with the private output index and all later seeds
integrated out.  There is no residual-moment hypothesis. -/
theorem actualTrackerAtBoundary_initial_p_moment
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar) :
    (∫⁻ z : Fin P.T × (Fin (responseCount P) → Seed),
      ENNReal.ofReal ((actualTrackerAtBoundary P I 0 z) ^ p)
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P)))) ≤
      ENNReal.ofReal (σ ^ p) := by
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle (responseCount P)) :=
    freshSeedLaw_probability I.oracle (responseCount P)
  have hmoment := I.predictable_freshBatch_coordinate_centered_moment
    ((algorithm (d := d) P).privateLaw)
    (fun _ : Fin P.T => (0 : Point d)) measurable_const
    (responseCount P) (⟨0, responseCount_pos P⟩ : Fin (responseCount P))
  let i₀ : Fin (responseCount P) := ⟨0, responseCount_pos P⟩
  let g : Fin P.T × (Fin (responseCount P) → Seed) → ENNReal := fun z =>
    ENNReal.ofReal
      (‖I.oracle.response 0 (z.2 i₀) - I.objective.grad 0‖ ^ p)
  have hseed : Measurable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) => z.2 i₀) :=
    (measurable_pi_apply i₀).comp measurable_snd
  have hresponse : Measurable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        I.oracle.response 0 (z.2 i₀)) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk hseed)
  have hg : Measurable g :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_rpow_const
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) I.p_range.1.le)).measurable.comp
        (hresponse.sub measurable_const).norm)
  have heq :
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        ENNReal.ofReal ((actualTrackerAtBoundary P I 0 z) ^ p)) = g := by
    funext z
    rw [actualTrackerAtBoundary_zero_eq_firstResponse P I z]
    rfl
  rw [heq, lintegral_prod _ hg.aemeasurable]
  simpa only [g, i₀] using hmoment

/-- Real-valued form of the same first-response `p`-moment bound, used in
the shifted Lyapunov moment decomposition. -/
theorem actualTrackerAtBoundary_initial_p_integrable_bound
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar) :
    Integrable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        (actualTrackerAtBoundary P I 0 z) ^ p)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))) ∧
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      (actualTrackerAtBoundary P I 0 z) ^ p
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P)))) ≤ σ ^ p := by
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  let f : (Fin P.T × (Fin (responseCount P) → Seed)) → ℝ :=
    fun z => (actualTrackerAtBoundary P I 0 z) ^ p
  have hmeas : Measurable f := by
    exact (Real.continuous_rpow_const
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) I.p_range.1.le)).measurable.comp
      (measurable_actualTrackerAtBoundary P I 0)
  have hnonneg (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      0 ≤ f z :=
    Real.rpow_nonneg (actualTrackerAtBoundary_nonneg P I 0 z) _
  have hmoment :
      (∫⁻ z, ENNReal.ofReal (f z) ∂μ) ≤ ENNReal.ofReal (σ ^ p) :=
    actualTrackerAtBoundary_initial_p_moment P I
  have hfinite : (∫⁻ z, ENNReal.ofReal (f z) ∂μ) < ∞ :=
    lt_of_le_of_lt hmoment (by finiteness)
  have hint : Integrable f μ :=
    ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall hnonneg)).2 hfinite⟩
  have hEq : (∫ z, f z ∂μ) =
      (∫⁻ z, ENNReal.ofReal (f z) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall hnonneg) hmeas.aestronglyMeasurable
  refine ⟨hint, ?_⟩
  rw [hEq]
  have hreal := ENNReal.toReal_mono (by finiteness) hmoment
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg I.sigma_nonneg p)] using hreal

end

end HeavyTailedNoise.UpperK1
