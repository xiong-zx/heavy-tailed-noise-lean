import HeavyTailedNoise.Lower.Gated.IdealFrozenCapEventInclusion
import HeavyTailedNoise.Probability.StageCounting
import HeavyTailedNoise.Probability.StageAzumaAE

/-!
Concrete stage counting for the full-history ideal strict-K=1 process.

Stage zero begins virtually at decision zero.  The stage lengths telescope
to the decision that completes stage T, which may be the arbitrary output
at time N.  Only N responses are used.  Short completed stages force the
already checked frozen cap events; no conditional-law identification or
single-stage probability bound is asserted here.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Elapsed decisions between consecutive ideal stage starts.  The virtual
stage-zero length can be zero when the first query immediately hits its cap. -/
def idealStageLength
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (j : Fin T) : ℕ :=
  idealStageStart hT U A r ξ a (j.val + 1) -
    idealStageStart hT U A r ξ a j.val

/-- The completion condition includes the final response-free decision. -/
def idealCompleted
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) : Prop :=
  idealStageStart hT U A r ξ a T ≤ N

/-- Never-started sentinel stages are excluded, even though their clock
differences can be zero. -/
def idealShortCompletedStage
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (m : ℕ) (j : Fin T) : Prop :=
  idealStageStart hT U A r ξ a (j.val + 1) ≤ N ∧
    idealStageLength hT U A r ξ a j ≤ m

/-- One frozen cap event per stage, using the true stopped snapshot and
the auxiliary random-start future tape.  Stage zero uses its virtual start. -/
def idealFrozenStageCap
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (Ξ : Fin (N + m) → Point d) (a : ℝ) (j : Fin T) : Prop := by
  classical
  exact if hj : j.val = 0 then
    frozenPrefixCapHitWithin hT U j A r
      (idealPreHistoryAtTime hT U A r (idealExtendedNoiseTake Ξ) a 0) a
      (idealExtendedNoiseTail 0 (Nat.zero_le N) Ξ)
  else
    let k : Fin T := ⟨j.val - 1, by omega⟩
    frozenPrefixCapHitWithin hT U j A r
      (idealStoppedPreHistory hT U k A r (idealExtendedNoiseTake Ξ) a) a
      (idealRandomStartTail hT U k A r a Ξ)

theorem idealStageLength_sum
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) :
    (∑ j : Fin T, idealStageLength hT U A r ξ a j) =
      idealStageStart hT U A r ξ a T := by
  have hmono : Monotone (idealStageStart hT U A r ξ a) :=
    fun j k hjk => idealStageStart_mono_target hT U A r ξ a j k hjk
  change (∑ j : Fin T, (idealStageStart hT U A r ξ a (j.val + 1) -
    idealStageStart hT U A r ξ a j.val)) = idealStageStart hT U A r ξ a T
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    idealStageStart hT U A r ξ a (i + 1) - idealStageStart hT U A r ξ a i) T]
  simpa only [idealStageStart_zero, Nat.sub_zero] using
    (Finset.sum_range_tsub hmono T)

theorem idealCompleted_iff_final_stage_reached
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) :
    idealCompleted hT U A r ξ a ↔ T ≤ idealAfterAt hT U A r ξ a N := by
  constructor
  · intro hcomplete
    exact (idealStageStart_hit hT U A r ξ a T hcomplete).trans
      (idealAfterAt_mono_of_le hT U A r ξ a _ N hcomplete le_rfl)
  · intro hfinal
    exact idealStageStart_le_of_hit hT U A r ξ a T N le_rfl hfinal

theorem idealShortCompletedStage_implies_frozenCap
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (Ξ : Fin (N + m) → Point d) (a : ℝ) (j : Fin T)
    (hshort : idealShortCompletedStage hT U A r
      (idealExtendedNoiseTake Ξ) a m j) :
    idealFrozenStageCap hT U A r Ξ a j := by
  classical
  obtain ⟨hnext, hlength⟩ := hshort
  by_cases hj : j.val = 0
  · have hjEq : j = ⟨0, hT⟩ := Fin.ext hj
    subst j
    have hshort0 : idealStageStart hT U A r
        (idealExtendedNoiseTake Ξ) a 1 ≤ m := by
      simpa [idealStageLength, idealStageStart_zero] using hlength
    simpa [idealFrozenStageCap] using
      (zeroShortStage_implies_frozenCapHit hT U A r Ξ a hnext hshort0)
  · let k : Fin T := ⟨j.val - 1, by omega⟩
    have hjk : j.val = k.val + 1 := by dsimp [k]; omega
    have hshort' : idealStageStart hT U A r
        (idealExtendedNoiseTake Ξ) a (j.val + 1) -
      idealStageStart hT U A r
        (idealExtendedNoiseTake Ξ) a (k.val + 1) ≤ m := by
      simpa only [idealStageLength, ← hjk] using hlength
    simpa only [idealFrozenStageCap, dite_eq_right hj] using
      (positiveShortStage_implies_frozenCapHit
        hT U k j hjk A r Ξ a hnext hshort')

theorem idealCompleted_forces_many_short_stages
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (m : ℕ) (hm : 0 < m) (hbudget : 4 * N ≤ T * m)
    (hcomplete : idealCompleted hT U A r ξ a) :
    3 * T ≤ 4 * (Finset.univ.filter fun j : Fin T =>
      idealShortCompletedStage hT U A r ξ a m j).card := by
  classical
  have hlengthBudget :
      4 * (∑ j : Fin T, idealStageLength hT U A r ξ a j) ≤ T * m := by
    rw [idealStageLength_sum]
    exact (Nat.mul_le_mul_left 4 hcomplete).trans hbudget
  have hnext (j : Fin T) : idealStageStart hT U A r ξ a (j.val + 1) ≤ N :=
    (idealStageStart_mono_target hT U A r ξ a
      (j.val + 1) T (by omega)).trans hcomplete
  simpa only [idealShortCompletedStage, hnext, true_and] using
    (many_short_stages_of_budget hm
      (idealStageLength hT U A r ξ a) hlengthBudget)

/-- Pathwise completion-to-frozen-event counting.  The frozen events are
not asserted to be adapted martingale increments. -/
theorem idealCompleted_forces_many_frozen_caps
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (Ξ : Fin (N + m) → Point d) (a : ℝ)
    (hm : 0 < m) (hbudget : 4 * N ≤ T * m)
    (hcomplete : idealCompleted hT U A r (idealExtendedNoiseTake Ξ) a) :
    3 * T ≤ 4 * (Finset.univ.filter fun j : Fin T =>
      idealFrozenStageCap hT U A r Ξ a j).card := by
  classical
  have hsubset : (Finset.univ.filter fun j : Fin T =>
      idealShortCompletedStage hT U A r (idealExtendedNoiseTake Ξ) a m j) ⊆
      Finset.univ.filter fun j : Fin T => idealFrozenStageCap hT U A r Ξ a j := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
      idealShortCompletedStage_implies_frozenCap hT U A r Ξ a j
        (Finset.mem_filter.mp hj).2⟩
  exact (idealCompleted_forces_many_short_stages hT U A r
    (idealExtendedNoiseTake Ξ) a m hm hbudget hcomplete).trans
    (Nat.mul_le_mul_left 4 (Finset.card_le_card hsubset))

/-- The actual short-completed-stage indicator, extended by zero past T.
These are the indicators to center for Azuma, rather than the auxiliary
frozen cap events that may use seeds after the actual stage exit. -/
def idealShortStageIndicator
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (m i : ℕ) : ℝ := by
  classical
  exact if hi : i < T then
    if idealShortCompletedStage hT U A r ξ a m ⟨i, hi⟩ then 1 else 0
  else 0

theorem idealShortStageIndicator_sum
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range T, idealShortStageIndicator hT U A r ξ a m i) =
      ((Finset.univ.filter fun j : Fin T =>
        idealShortCompletedStage hT U A r ξ a m j).card : ℝ) := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  simp [idealShortStageIndicator]

/-- Concrete completion tail under explicit centered-increment premises.
The actual stopped conditional law, the resulting half-probability bound,
and adaptation/centering still have to supply these premises.  Private r is
fixed; this theorem imposes no standard-Borel condition on Private. -/
theorem idealCompleted_tail_of_short_stage_domination_ae
    {d T N : ℕ} {Private Ω : Type*} [MeasurableSpace Private]
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ)
    (hT : 0 < T) (U : Ω → Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Ω → Fin N → Point d) (a : ℝ)
    (m : ℕ) (hm : 0 < m) (hbudget : 4 * N ≤ T * m)
    (Y : ℕ → Ω → ℝ)
    (h_adapted : StronglyAdapted ℱ Y)
    (h₀ : HasSubgaussianMGF (Y 0) 1 μ)
    (h_cond : ∀ i < T - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) 1 μ)
    (h_dom : ∀ i < T, ∀ᵐ ω ∂μ,
      idealShortStageIndicator hT (U ω) A r (ξ ω) a m i ≤
        (1 : ℝ) / 2 + Y i ω) :
    μ.real {ω | idealCompleted hT (U ω) A r (ξ ω) a} ≤
      Real.exp (-(T : ℝ) / 32) := by
  let X : ℕ → Ω → ℝ := fun i ω =>
    idealShortStageIndicator hT (U ω) A r (ξ ω) a m i
  have hsubset : {ω | idealCompleted hT (U ω) A r (ξ ω) a} ⊆
      {ω | 3 * (T : ℝ) / 4 ≤ ∑ i ∈ Finset.range T, X i ω} := by
    intro ω hcomplete
    have hcount := idealCompleted_forces_many_short_stages
      hT (U ω) A r (ξ ω) a m hm hbudget hcomplete
    have hcountReal : 3 * (T : ℝ) ≤
        4 * ((Finset.univ.filter fun j : Fin T =>
          idealShortCompletedStage hT (U ω) A r (ξ ω) a m j).card : ℝ) := by
      exact_mod_cast hcount
    change 3 * (T : ℝ) / 4 ≤
      ∑ i ∈ Finset.range T, idealShortStageIndicator hT (U ω) A r (ξ ω) a m i
    rw [idealShortStageIndicator_sum]
    linarith
  exact (measureReal_mono hsubset).trans
    (stage_count_tail_of_subgaussian_domination_ae μ ℱ X Y T
      h_adapted h₀ h_cond h_dom)

end

end HeavyTailedNoise
