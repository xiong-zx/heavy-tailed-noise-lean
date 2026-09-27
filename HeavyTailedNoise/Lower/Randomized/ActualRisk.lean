import HeavyTailedNoise.Lower.Randomized.AccidentProbability
import HeavyTailedNoise.Probability.BernoulliCounting
import HeavyTailedNoise.Model.ParametricProtocol
import HeavyTailedNoise.Probability.RiskJointTonelli

/-!
Actual support progress, response-free output barrier and the fixed-prior
average risk of arbitrary randomized full-history algorithms. The geometry,
conditional law and Bernoulli count inputs are discharged in the final entry.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace HeavyTailedNoise.RandomizedLift

section ActualProgress

variable {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
variable (A : RandomAlgorithm d N Private) (r : Private)
variable {R : ℝ} (hR : 0 < R) (η : ℝ) (θ : unitInterval) (tape : ℕ → Bool)

def tapeHistory (U : Fin T → Point d) (t : ℕ) : Transcript d t :=
  runTranscript (oracle U hR η θ) A r t (fun i => tape i.val)

def tapeDecision (U : Fin T → Point d) (t : ℕ) : Point d :=
  A.decide t r (tapeHistory A r hR η θ tape U t)

/-- Analysis-only cumulative support in the literal response history. -/
def actualProgress (U : Fin T → Point d) : ℕ → ℕ
  | 0 => 0
  | t + 1 => max (actualProgress U t)
      (baseProgress θ (coordinates U R (tapeDecision A r hR η θ tape U t)) (tape t))

theorem actualProgress_le_next (U : Fin T → Point d) (t : ℕ) :
    actualProgress A r hR η θ tape U t ≤ actualProgress A r hR η θ tape U (t + 1) :=
  le_max_left _ _

/-- Whenever the real support has not exceeded a threshold, the literal
stopped record has the same cumulative support; its canonical transcript
coupling therefore applies to the arbitrary actual full history. -/
theorem stoppedProgress_eq_actual_of_le {j : ℕ} (hj : j ≤ T)
    (U : Fin T → Point d) (t : ℕ)
    (halive : actualProgress A r hR η θ tape U t ≤ j) :
    (reconstructedState A r R η θ tape t
      (absorbedRecord A r R η θ tape hj U t)).2 =
        actualProgress A r hR η θ tape U t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hpre : actualProgress A r hR η θ tape U t ≤ j :=
        (actualProgress_le_next A r hR η θ tape U t).trans halive
      have heq := ih hpre
      have hs : (reconstructedState A r R η θ tape t
          (absorbedRecord A r R η θ tape hj U t)).2 ≤ j := by rw [heq]; exact hpre
      have hh := reconstructedState_alive_eq_runTranscript A r η θ tape hj hR U t hs
      have hq : stoppedQuery A r R η θ tape t (absorbedRecord A r R η θ tape hj U t) =
          softProjection R (tapeDecision A r hR η θ tape U t) := by
        simp only [stoppedQuery, hs, if_true, stoppedDecision, stateDecision, hh,
          tapeDecision, tapeHistory]
      rw [reconstructedState_progress_successor A r R η θ tape hj U t, heq]
      change max _ (baseProgress θ
        (WithLp.toLp 2 (frameCoordinates U
          (stoppedQuery A r R η θ tape t (absorbedRecord A r R η θ tape hj U t)))) (tape t)) = _
      rw [hq]
      rfl

theorem stoppedQuery_eq_actual_of_progress {j : ℕ} (hj : j ≤ T)
    (U : Fin T → Point d) (t : ℕ)
    (halive : actualProgress A r hR η θ tape U t ≤ j) :
    stoppedQuery A r R η θ tape t (absorbedRecord A r R η θ tape hj U t) =
      softProjection R (tapeDecision A r hR η θ tape U t) := by
  have heq := stoppedProgress_eq_actual_of_le A r hR η θ tape hj U t halive
  have hs : (reconstructedState A r R η θ tape t
      (absorbedRecord A r R η θ tape hj U t)).2 ≤ j := by rw [heq]; exact halive
  have hh := reconstructedState_alive_eq_runTranscript A r η θ tape hj hR U t hs
  simp only [stoppedQuery, hs, if_true, stoppedDecision, stateDecision, hh,
    tapeDecision, tapeHistory]

theorem stoppedOutput_eq_actual_of_progress {j : ℕ} (hj : j ≤ T)
    (U : Fin T → Point d)
    (halive : actualProgress A r hR η θ tape U N ≤ j) :
    stoppedOutputQuery A r R η θ tape (absorbedRecord A r R η θ tape hj U N) =
      softProjection R (A.output r (tapeHistory A r hR η θ tape U N)) := by
  have heq := stoppedProgress_eq_actual_of_le A r hR η θ tape hj U N halive
  have hs : (reconstructedState A r R η θ tape N
      (absorbedRecord A r R η θ tape hj U N)).2 ≤ j := by rw [heq]; exact halive
  exact stoppedOutputQuery_eq_actual A r η θ tape hj hR U hs

theorem quiet_query_coordinate_lt_quarter
    (u : {U : Fin T → Point d // Orthonormal ℝ U})
    (hquiet : u ∉ geometricAccident A r (T := T) (R := R) η θ tape) (t : Fin N) (i : Fin T)
    (hi : actualProgress A r hR η θ tape u.1 t.val ≤ i.val) :
    |coordinates u.1 R (tapeDecision A r hR η θ tape u.1 t.val) i| < 1/4 := by
  have hq := stoppedQuery_eq_actual_of_progress A r hR η θ tape i.isLt.le u.1 t.val hi
  have hn : ¬ (1/4 : ℝ) ≤ |inner ℝ (u.1 i)
      (stoppedBoundedQueries A r R η θ tape i.isLt.le u.1 t.castSucc)| := by
    intro h
    apply hquiet
    change u ∈ ⋃ a : Fin T, singleColumnAccident A r (R := R) η θ tape a
    apply Set.mem_iUnion.mpr
    exact ⟨i, ⟨t.castSucc, h⟩⟩
  rw [stoppedBoundedQueries_query A r R η θ tape i.isLt.le u.1 t, hq] at hn
  exact lt_of_not_ge hn

theorem quiet_output_coordinate_lt_quarter
    (u : {U : Fin T → Point d // Orthonormal ℝ U})
    (hquiet : u ∉ geometricAccident A r (T := T) (R := R) η θ tape) (i : Fin T)
    (hi : actualProgress A r hR η θ tape u.1 N ≤ i.val) :
    |coordinates u.1 R (A.output r (tapeHistory A r hR η θ tape u.1 N)) i| < 1/4 := by
  have hq := stoppedOutput_eq_actual_of_progress A r hR η θ tape i.isLt.le u.1 hi
  have hn : ¬ (1/4 : ℝ) ≤ |inner ℝ (u.1 i)
      (stoppedBoundedQueries A r R η θ tape i.isLt.le u.1 (Fin.last N))| := by
    intro h
    apply hquiet
    change u ∈ ⋃ a : Fin T, singleColumnAccident A r (R := R) η θ tape a
    apply Set.mem_iUnion.mpr
    exact ⟨i, ⟨Fin.last N, h⟩⟩
  rw [stoppedBoundedQueries_output A r R η θ tape i.isLt.le u.1, hq] at hn
  exact lt_of_not_ge hn

theorem quiet_support_progress_le
    (u : {U : Fin T → Point d // Orthonormal ℝ U})
    (hquiet : u ∉ geometricAccident A r (T := T) (R := R) η θ tape) (t : Fin N) :
    baseProgress θ (coordinates u.1 R (tapeDecision A r hR η θ tape u.1 t.val)) (tape t.val) ≤
      actualProgress A r hR η θ tape u.1 t.val + (if tape t.val then 1 else 0) := by
  have hx : ∀ i : Fin T, actualProgress A r hR η θ tape u.1 t.val ≤ i.val →
      |coordinates u.1 R (tapeDecision A r hR η θ tape u.1 t.val) i| ≤ 1/4 := by
    intro i hi
    exact (quiet_query_coordinate_lt_quarter A r hR η θ tape u hquiet t i hi).le
  cases hD : tape t.val with
  | false =>
      simp only [hD, Bool.false_eq_true, ↓reduceIte, add_zero]
      apply (coefficientProgress_le_iff _).mpr
      intro i hi
      exact Fradin.bernoulliResponse_false_frontier_zero θ _ hx i hi
  | true =>
      simp only [hD, ↓reduceIte]
      apply (coefficientProgress_le_iff _).mpr
      intro i hi
      exact Fradin.bernoulliResponse_tail_zero θ _
        (fun a ha => (hx a ha).trans (by norm_num)) i hi true

theorem quiet_actualProgress_le_revealCount
    (u : {U : Fin T → Point d // Orthonormal ℝ U})
    (hquiet : u ∉ geometricAccident A r (T := T) (R := R) η θ tape) (t : ℕ) (ht : t ≤ N) :
    actualProgress A r hR η θ tape u.1 t ≤
      revealCount (fun i : Fin t => tape i.val) := by
  induction t with
  | zero => simp [actualProgress, revealCount]
  | succ t ih =>
      have htn : t < N := by omega
      have hb := quiet_support_progress_le A r hR η θ tape u hquiet ⟨t, htn⟩
      have hp := ih (by omega)
      rw [actualProgress, revealCount_succ]
      simp only [Fin.val_castSucc, Fin.val_last]
      apply max_le
      · exact hp.trans (Nat.le_add_right _ _)
      · exact hb.trans (Nat.add_le_add_right hp _)

end ActualProgress

section Risk

variable {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
variable (hT : 0 < T) (hTd : T ≤ d) (θ : unitInterval)
variable (A : RandomAlgorithm d N Private)

abbrev liftSeedLaw (θ : unitInterval) (N : ℕ) : Measure (Fin N → Bool) :=
  Measure.pi (fun _ => Fradin.bernoulliLaw θ)

def unscaledLoss
    (u : {U : Fin T → Point d // Orthonormal ℝ U}) (r : Private) (seeds : Fin N → Bool) : ℝ≥0∞ :=
  ENNReal.ofReal ‖populationGradient u.1 (liftRadius T) (1/5)
    (A.output r (runTranscript (oracle u.1 (liftRadius_pos hT) (1/5) θ) A r N seeds))‖

section UnscaledMeasurability

attribute [local irreducible] response populationGradient oracle runTranscript

theorem measurable_unscaledFrame_response :
    Measurable (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Point d × Bool) =>
      (oracle z.1.1 (liftRadius_pos hT) (1/5) θ).response z.2.1 z.2.2) := by
  let input : {U : Fin T → Point d // Orthonormal ℝ U} × (Point d × Bool) →
      ((Fin T → Point d) × Point d) × Bool := fun z => ((z.1.1, z.2.1), z.2.2)
  have hinput : Measurable input :=
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have hcomposed := (measurable_joint_response (d := d) (T := T)
    (liftRadius_pos hT) (1/5) θ).comp hinput
  simpa only [input, Function.comp_def, oracle] using hcomposed

theorem measurable_unscaledLoss :
    Measurable (fun z : {U : Fin T → Point d // Orthonormal ℝ U} ×
      (Private × (Fin N → Bool)) => unscaledLoss hT θ A z.1 z.2.1 z.2.2) := by
  have hresponse : Measurable
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Point d × Bool) =>
        (oracle z.1.1 (liftRadius_pos hT) (1/5) θ).response z.2.1 z.2.2) :=
    measurable_unscaledFrame_response hT θ
  have hout : Measurable
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Private × (Fin N → Bool)) =>
        A.output z.2.1
          (runTranscript (oracle z.1.1 (liftRadius_pos hT) (1/5) θ) A z.2.1 N z.2.2)) :=
    measurable_parametric_runOutput
      (fun u : {U : Fin T → Point d // Orthonormal ℝ U} => oracle u.1 (liftRadius_pos hT) (1/5) θ)
      A hresponse
  let gradientInput : {U : Fin T → Point d // Orthonormal ℝ U} × (Private × (Fin N → Bool)) →
      (Fin T → Point d) × Point d := fun z =>
    (z.1.1, A.output z.2.1
      (runTranscript (oracle z.1.1 (liftRadius_pos hT) (1/5) θ) A z.2.1 N z.2.2))
  have hinput : Measurable gradientInput :=
    (measurable_subtype_coe.comp measurable_fst).prodMk hout
  have hgradient := (measurable_joint_populationGradient (d := d) (T := T)
    (liftRadius_pos hT) (1/5)).comp hinput
  have hloss := ENNReal.measurable_ofReal.comp hgradient.norm
  simpa only [unscaledLoss, gradientInput, Function.comp_def] using hloss

end UnscaledMeasurability

theorem quiet_small_count_output_barrier (r : Private) (seeds : Fin N → Bool)
    (u : {U : Fin T → Point d // Orthonormal ℝ U})
    (hquiet : u ∉ geometricAccident A r (T := T) (R := liftRadius T) (1/5) θ (finiteTape seeds))
    (hcount : revealCount seeds < T) :
    (1/2 : ℝ) ≤ ‖populationGradient u.1 (liftRadius T) (1/5)
      (A.output r (runTranscript (oracle u.1 (liftRadius_pos hT) (1/5) θ) A r N seeds))‖ := by
  have hp := quiet_actualProgress_le_revealCount A r (liftRadius_pos hT) (1/5) θ
    (finiteTape seeds) u hquiet N le_rfl
  simp only [finiteTape_apply] at hp
  let i : Fin T := ⟨actualProgress A r (liftRadius_pos hT) (1/5) θ (finiteTape seeds) u.1 N,
    hp.trans_lt hcount⟩
  have hx := quiet_output_coordinate_lt_quarter A r (liftRadius_pos hT) (1/5) θ
    (finiteTape seeds) u hquiet i le_rfl
  have hhist : tapeHistory A r (liftRadius_pos hT) (1/5) θ (finiteTape seeds) u.1 N =
      runTranscript (oracle u.1 (liftRadius_pos hT) (1/5) θ) A r N seeds := by
    simp only [tapeHistory, finiteTape_apply]
  rw [hhist] at hx
  exact lift_stationarity_barrier u.2 hT _ ⟨i, hx.trans (by norm_num)⟩

include hT in
theorem revealCount_bad_probability_eighth
    (hbudget : 8 * (N : ℝ) * (θ : ℝ) ≤ (T : ℝ)) :
    liftSeedLaw θ N {seeds | (T : ℝ) ≤ (revealCount seeds : ℝ)} ≤ (1/8 : ℝ≥0∞) := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hb := revealCount_tail_le N θ hTp
  have hnum : (N : ℝ) * (θ : ℝ) / (T : ℝ) ≤ (1/8 : ℝ) := by
    apply (div_le_iff₀ hTp).mpr
    linarith
  have hr := hb.trans hnum
  have hc := ENNReal.ofReal_le_ofReal hr
  rw [ofReal_measureReal (measure_ne_top _ _)] at hc
  have he : ENNReal.ofReal (1/8 : ℝ) = (1/8 : ℝ≥0∞) := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using ennreal_ofReal_nat_div 1 8 (by decide)
  rw [he] at hc
  exact hc

include hT in
theorem revealCount_good_probability_seven_eighths
    (hbudget : 8 * (N : ℝ) * (θ : ℝ) ≤ (T : ℝ)) :
    (7/8 : ℝ≥0∞) ≤ liftSeedLaw θ N {seeds | revealCount seeds < T} := by
  have hm : MeasurableSet {seeds : Fin N → Bool | (T : ℝ) ≤ (revealCount seeds : ℝ)} :=
    measurableSet_le measurable_const (measurable_of_finite _)
  have hset : {seeds : Fin N → Bool | revealCount seeds < T} =
      {seeds : Fin N → Bool | (T : ℝ) ≤ (revealCount seeds : ℝ)}ᶜ := by
    ext seeds
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, Nat.cast_lt]
  rw [hset]
  exact probability_compl_ge_seven_eighths (liftSeedLaw θ N) _ hm
    (revealCount_bad_probability_eighth hT θ hbudget)

section RiskExpectations

attribute [local irreducible] unscaledLoss populationGradient runTranscript

theorem fixed_private_tape_frame_risk_ge (r : Private) (seeds : Fin N → Bool)
    (hd : geometricDimension (liftRadius T) T N ≤ d) (hcount : revealCount seeds < T) :
    (7/16 : ℝ≥0∞) ≤ ∫⁻ u, unscaledLoss hT θ A u r seeds
      ∂preselectedOrthonormalFrameLaw d T hTd := by
  let μ : Measure {U : Fin T → Point d // Orthonormal ℝ U} := preselectedOrthonormalFrameLaw d T hTd
  let bad : Set {U : Fin T → Point d // Orthonormal ℝ U} :=
    geometricAccident A r (T := T) (R := liftRadius T) (1/5) θ (finiteTape seeds)
  have hbad : μ bad ≤ (1/8 : ℝ≥0∞) :=
    geometricAccident_probability_eighth A r (liftRadius_pos hT) (1/5) θ
      (finiteTape seeds) hTd hT hd
  have hquiet : (7/8 : ℝ≥0∞) ≤ μ badᶜ :=
    probability_compl_ge_seven_eighths μ bad
      (measurableSet_geometricAccident A r (T := T) (R := liftRadius T)
        (liftRadius_pos hT) (1/5) θ (finiteTape seeds)) hbad
  have hsub : badᶜ ⊆ {u | (1/2 : ℝ≥0∞) ≤ unscaledLoss hT θ A u r seeds} := by
    intro u hu
    have hb := quiet_small_count_output_barrier hT θ A r seeds u hu hcount
    have hc := ENNReal.ofReal_le_ofReal hb
    have he : ENNReal.ofReal (1/2 : ℝ) = (1/2 : ℝ≥0∞) := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using ennreal_ofReal_nat_div 1 2 (by decide)
    simpa only [Set.mem_setOf_eq, unscaledLoss, he] using hc
  have hloss : Measurable (fun u : {U : Fin T → Point d // Orthonormal ℝ U} =>
      unscaledLoss hT θ A u r seeds) :=
    (measurable_unscaledLoss hT θ A).comp
      (measurable_id.prodMk (measurable_const.prodMk measurable_const))
  have hm := mul_meas_ge_le_lintegral (μ := μ) hloss (1/2 : ℝ≥0∞)
  calc
    (7/16 : ℝ≥0∞) = (1/2 : ℝ≥0∞) * (7/8 : ℝ≥0∞) := by
      have h7 : ENNReal.ofReal (7/16 : ℝ) = (7/16 : ℝ≥0∞) := by
        simpa only [Nat.cast_one, Nat.cast_ofNat] using ennreal_ofReal_nat_div 7 16 (by decide)
      have h1 : ENNReal.ofReal (1/2 : ℝ) = (1/2 : ℝ≥0∞) := by
        simpa only [Nat.cast_one, Nat.cast_ofNat] using ennreal_ofReal_nat_div 1 2 (by decide)
      have h8 : ENNReal.ofReal (7/8 : ℝ) = (7/8 : ℝ≥0∞) := by
        simpa only [Nat.cast_one, Nat.cast_ofNat] using ennreal_ofReal_nat_div 7 8 (by decide)
      rw [← h7, ← h1, ← h8,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
      congr 1 <;> norm_num
    _ ≤ (1/2 : ℝ≥0∞) * μ {u | (1/2 : ℝ≥0∞) ≤ unscaledLoss hT θ A u r seeds} :=
      mul_le_mul' le_rfl (hquiet.trans (measure_mono hsub))
    _ ≤ _ := hm

theorem fixed_private_seed_frame_risk_ge (r : Private)
    (hd : geometricDimension (liftRadius T) T N ≤ d)
    (hbudget : 8 * (N : ℝ) * (θ : ℝ) ≤ (T : ℝ)) :
    (49/128 : ℝ≥0∞) ≤ ∫⁻ seeds, ∫⁻ u, unscaledLoss hT θ A u r seeds
      ∂preselectedOrthonormalFrameLaw d T hTd ∂liftSeedLaw θ N := by
  let good : Set (Fin N → Bool) := {seeds | revealCount seeds < T}
  have hgood : MeasurableSet good := measurableSet_lt (measurable_of_finite _) measurable_const
  have hprob := revealCount_good_probability_seven_eighths hT θ hbudget
  calc
    (49/128 : ℝ≥0∞) = (7/16 : ℝ≥0∞) * (7/8 : ℝ≥0∞) := by
      have h49 : ENNReal.ofReal (49/128 : ℝ) = (49/128 : ℝ≥0∞) := by
        simpa only [Nat.cast_one, Nat.cast_ofNat] using ennreal_ofReal_nat_div 49 128 (by decide)
      have h7 : ENNReal.ofReal (7/16 : ℝ) = (7/16 : ℝ≥0∞) := by
        simpa only [Nat.cast_one, Nat.cast_ofNat] using ennreal_ofReal_nat_div 7 16 (by decide)
      have h8 : ENNReal.ofReal (7/8 : ℝ) = (7/8 : ℝ≥0∞) := by
        simpa only [Nat.cast_one, Nat.cast_ofNat] using ennreal_ofReal_nat_div 7 8 (by decide)
      rw [← h49, ← h7, ← h8,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7/16)]
      congr 1 <;> norm_num
    _ ≤ (7/16 : ℝ≥0∞) * liftSeedLaw θ N good := mul_le_mul' le_rfl hprob
    _ = ∫⁻ seeds, good.indicator (fun _ => (7/16 : ℝ≥0∞)) seeds ∂liftSeedLaw θ N := by
      rw [lintegral_indicator hgood]
      simp
    _ ≤ _ := by
      apply lintegral_mono
      intro seeds
      by_cases hs : seeds ∈ good
      · rw [Set.indicator_of_mem hs]
        exact fixed_private_tape_frame_risk_ge hT hTd θ A r seeds hd hs
      · simp only [Set.indicator_of_notMem hs]
        exact bot_le

/-- One same preselected Haar prior, followed by all private and seed laws.
No conditional-law, covariance, geometry or progress-probability premise is
left in this entry; N is the response budget and output consumes no response. -/
theorem unscaledHaar_averageRisk_ge
    (hd : geometricDimension (liftRadius T) T N ≤ d)
    (hbudget : 8 * (N : ℝ) * (θ : ℝ) ≤ (T : ℝ)) :
    (49/128 : ℝ≥0∞) ≤
      ∫⁻ u, ∫⁻ r, ∫⁻ seeds, unscaledLoss hT θ A u r seeds
        ∂freshSeedLaw (oracle u.1 (liftRadius_pos hT) (1/5) θ) N
        ∂A.privateLaw ∂preselectedOrthonormalFrameLaw d T hTd := by
  haveI : IsProbabilityMeasure A.privateLaw := A.private_probability
  have hloss := measurable_unscaledLoss hT θ A
  have hg : Measurable
      (fun p : {U : Fin T → Point d // Orthonormal ℝ U} × Private =>
        ∫⁻ seeds, unscaledLoss hT θ A p.1 p.2 seeds ∂liftSeedLaw θ N) :=
    (hloss.comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right'
  have horder :
      (∫⁻ u, ∫⁻ r, ∫⁻ seeds, unscaledLoss hT θ A u r seeds
        ∂liftSeedLaw θ N ∂A.privateLaw ∂preselectedOrthonormalFrameLaw d T hTd) =
      ∫⁻ r, ∫⁻ seeds, ∫⁻ u, unscaledLoss hT θ A u r seeds
        ∂preselectedOrthonormalFrameLaw d T hTd ∂liftSeedLaw θ N ∂A.privateLaw := by
    rw [lintegral_lintegral_swap hg.aemeasurable]
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall (fun r =>
      lintegral_lintegral_swap
        ((hloss.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).aemeasurable))
  change (49/128 : ℝ≥0∞) ≤
    ∫⁻ u, ∫⁻ r, ∫⁻ seeds, unscaledLoss hT θ A u r seeds
      ∂liftSeedLaw θ N ∂A.privateLaw ∂preselectedOrthonormalFrameLaw d T hTd
  rw [horder]
  calc
    (49/128 : ℝ≥0∞) = ∫⁻ _r : Private, (49/128 : ℝ≥0∞) ∂A.privateLaw := by simp
    _ ≤ _ := lintegral_mono (fun r => fixed_private_seed_frame_risk_ge hT hTd θ A r hd hbudget)

theorem unscaledHaar_averageRisk_gt_eighth
    (hd : geometricDimension (liftRadius T) T N ≤ d)
    (hbudget : 8 * (N : ℝ) * (θ : ℝ) ≤ (T : ℝ)) :
    ENNReal.ofReal (1/8 : ℝ) <
      ∫⁻ u, ∫⁻ r, ∫⁻ seeds, ENNReal.ofReal ‖populationGradient u.1
        (liftRadius T) (1/5)
        (A.output r (runTranscript (oracle u.1 (liftRadius_pos hT) (1/5) θ) A r N seeds))‖
        ∂freshSeedLaw (oracle u.1 (liftRadius_pos hT) (1/5) θ) N
        ∂A.privateLaw ∂preselectedOrthonormalFrameLaw d T hTd := by
  have hstrict : ENNReal.ofReal (1/8 : ℝ) < (49/128 : ℝ≥0∞) := by
    have h49 : ENNReal.ofReal (49/128 : ℝ) = (49/128 : ℝ≥0∞) := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using ennreal_ofReal_nat_div 49 128 (by decide)
    rw [← h49]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/8)).mpr (by norm_num)
  simpa only [unscaledLoss] using hstrict.trans_le
    (unscaledHaar_averageRisk_ge hT hTd θ A hd hbudget)

include hTd in
/-- A deterministic frame is extracted only after its entire private and
fresh-seed risk has been integrated. Physical legality is supplied by the
existing PhysicalParameters/Model.Distributional assembly. -/
theorem unscaledHaar_bad_frame
    (hd : geometricDimension (liftRadius T) T N ≤ d)
    (hbudget : 8 * (N : ℝ) * (θ : ℝ) ≤ (T : ℝ)) :
    ∃ u : {U : Fin T → Point d // Orthonormal ℝ U},
      ENNReal.ofReal (1/8 : ℝ) <
        ∫⁻ r, ∫⁻ seeds, unscaledLoss hT θ A u r seeds
          ∂freshSeedLaw (oracle u.1 (liftRadius_pos hT) (1/5) θ) N ∂A.privateLaw := by
  have h : ENNReal.ofReal (1/8 : ℝ) <
      ∫⁻ u, ∫⁻ r, ∫⁻ seeds, unscaledLoss hT θ A u r seeds
        ∂freshSeedLaw (oracle u.1 (liftRadius_pos hT) (1/5) θ) N
        ∂A.privateLaw ∂preselectedOrthonormalFrameLaw d T hTd := by
    simpa only [unscaledLoss] using unscaledHaar_averageRisk_gt_eighth hT hTd θ A hd hbudget
  by_contra hn
  have hp : ∀ u : {U : Fin T → Point d // Orthonormal ℝ U},
      (∫⁻ r, ∫⁻ seeds, unscaledLoss hT θ A u r seeds
        ∂freshSeedLaw (oracle u.1 (liftRadius_pos hT) (1/5) θ) N ∂A.privateLaw) ≤
          ENNReal.ofReal (1/8 : ℝ) := by
    intro u
    exact le_of_not_gt (fun hu => hn ⟨u, hu⟩)
  have hb := lintegral_mono (μ := preselectedOrthonormalFrameLaw d T hTd) hp
  simp only [lintegral_const, measure_univ, mul_one] at hb
  exact not_lt_of_ge hb h

end RiskExpectations

end Risk

end HeavyTailedNoise.RandomizedLift
