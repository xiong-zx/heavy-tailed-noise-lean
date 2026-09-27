import HeavyTailedNoise.Lower.Gated.LowerBoundCouplingAssembly
import HeavyTailedNoise.Probability.StageBernoulliCentering
import HeavyTailedNoise.Lower.Gated.JointPrefixGradientMeas

/-!
The cumulative analysis filtration for the actual ideal stage indicators.

Level i retains every pre-response stopped record for stages at most i+1,
and the revealed frame prefix through column i (clamped at the last column).
Mathlib's product-coordinate filtration stores the whole observation path, rather than
assuming that a latest never-started zero snapshot recovers earlier records.
These are analysis data and are never supplied to the algorithm.

The initial X_0 is centered unconditionally; X_(i+1) is centered conditional
on this cumulative filtration at level i.  The actual conditional half bound
and selected fresh-tail law under cumulative history remain application
obligations.  A law conditioned only on the latest record does not discharge
those obligations.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory MeasurableSpace

noncomputable section

set_option autoImplicit false

abbrev IdealStageAnalysisData (d T N : ℕ) :=
  (Fin T → Point d) × (Bool × ℕ × Transcript d N × Point d)

def idealStageObservation
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (i : ℕ) : IdealStageAnalysisData d T N :=
  let j := idealPrefixIndex hT i
  (prefixFrame U j, idealPreResponseTuple (idealStoppedPreHistory hT U j A r ξ a))

theorem measurable_joint_idealStageObservation
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (a : ℝ) (i : ℕ) :
    Measurable (fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      idealStageObservation hT z.1 A z.2.1 z.2.2 a i) := by
  classical
  let j := idealPrefixIndex hT i
  have hf : Measurable (fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      prefixFrame z.1 j) := by
    apply measurable_pi_iff.mpr
    intro k
    by_cases hk : k ≤ j
    · simpa only [prefixFrame, ite_eq_left hk, Function.comp_def] using
        ((measurable_pi_apply k).comp measurable_fst)
    · simpa only [prefixFrame, ite_eq_right hk] using
        (measurable_const : Measurable (fun _ :
          (Fin T → Point d) × (Private × (Fin N → Point d)) => (0 : Point d)))
  have hp : Measurable (fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      (framePrefix (Nat.succ_le_iff.mpr j.isLt) z.1, z.2)) :=
    ((measurable_framePrefix (Nat.succ_le_iff.mpr j.isLt)).comp measurable_fst).prodMk
      measurable_snd
  have hs : Measurable (fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      idealPreResponseTuple (idealStoppedPreHistory hT z.1 j A z.2.1 z.2.2 a)) := by
    convert (measurable_idealStoppedPreHistoryFromPrefix hT j A a).comp hp using 1
    funext z
    exact idealStoppedPreHistoryFromPrefix_eq hT z.1 j A z.2.1 z.2.2 a
  exact hf.prodMk hs

def idealStageCumulativeData
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (i : ℕ) : Set.Iic i → IdealStageAnalysisData d T N :=
  fun j => idealStageObservation hT U A r ξ a j.val

theorem idealStageObservation_eq_of_prefix_agree
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d}
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (i t : ℕ) (hti : t ≤ i)
    (h : ∀ k, k ≤ idealPrefixIndex hT i → U k = V k) :
    idealStageObservation hT U A r ξ a t = idealStageObservation hT V A r ξ a t := by
  have hj : idealPrefixIndex hT t ≤ idealPrefixIndex hT i := by
    change min t (T - 1) ≤ min i (T - 1)
    omega
  have hlocal : ∀ k, k ≤ idealPrefixIndex hT t → U k = V k :=
    fun k hk => h k (hk.trans hj)
  dsimp only [idealStageObservation]
  rw [prefixFrame_eq_of_agree _ hlocal,
    idealStoppedPreHistory_eq_of_agree hT _ hlocal A r ξ a]

/-- The entire accumulated path factors through the current revealed prefix,
including paths whose later records are never-started sentinel snapshots. -/
theorem idealStageCumulativeData_prefix_factorization
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (i : ℕ) :
    idealStageCumulativeData hT U A r ξ a i =
      idealStageCumulativeData hT
        (idealPrefixExtension (idealPrefixIndex hT i)
          (framePrefix (Nat.succ_le_iff.mpr (idealPrefixIndex hT i).isLt) U))
        A r ξ a i := by
  funext t
  exact idealStageObservation_eq_of_prefix_agree hT A r ξ a i t.val t.property
    (idealPrefixExtension_agree U (idealPrefixIndex hT i))

def idealStageCumulativeDataFromPrefix
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (i : ℕ) (A : RandomAlgorithm d N Private) (a : ℝ) :
    (Fin ((idealPrefixIndex hT i).val + 1) → Point d) ×
      (Private × (Fin N → Point d)) → Set.Iic i → IdealStageAnalysisData d T N :=
  fun z => idealStageCumulativeData hT
    (idealPrefixExtension (idealPrefixIndex hT i) z.1) A z.2.1 z.2.2 a i

theorem measurable_idealStageCumulativeDataFromPrefix
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (i : ℕ) (A : RandomAlgorithm d N Private) (a : ℝ) :
    Measurable (idealStageCumulativeDataFromPrefix hT i A a) := by
  apply measurable_pi_iff.mpr
  intro t
  have hp : Measurable (fun z :
      (Fin ((idealPrefixIndex hT i).val + 1) → Point d) ×
        (Private × (Fin N → Point d)) =>
      (idealPrefixExtension (idealPrefixIndex hT i) z.1, z.2)) :=
    ((measurable_idealPrefixExtension (idealPrefixIndex hT i)).comp measurable_fst).prodMk
      measurable_snd
  exact (measurable_joint_idealStageObservation hT A a t.val).comp hp

theorem measurable_idealStageObservation
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [MeasurableSpace Ω]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) (i : ℕ) :
    Measurable (fun ω => idealStageObservation hT (U ω) A r (ξ ω) a i) :=
  (measurable_joint_idealStageObservation hT A a i).comp
    (hU.prodMk ((measurable_const : Measurable (fun _ : Ω => r)).prodMk hξ))

/-- The product-coordinate filtration retains every observation j≤i.  It is analysis
state and does not change A's observations or private measurable space. -/
def idealStageFiltration
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [mΩ : MeasurableSpace Ω]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) : Filtration ℕ mΩ :=
  let obs : Ω → ℕ → IdealStageAnalysisData d T N :=
    fun ω i => idealStageObservation hT (U ω) A r (ξ ω) a i
  let past : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → IdealStageAnalysisData d T N)) :=
    Filtration.piLE
  let hobs : Measurable obs := measurable_pi_iff.mpr
    (fun i => measurable_idealStageObservation hT A r a U ξ hU hξ i)
  { seq := fun i => (past i).comap obs
    mono' := fun _ _ hij => MeasurableSpace.comap_mono (past.mono hij)
    le' := fun i => (MeasurableSpace.comap_mono (past.le i)).trans hobs.comap_le }

theorem idealStageFiltration_eq_cumulative
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [mΩ : MeasurableSpace Ω]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) (i : ℕ) :
    idealStageFiltration hT A r a U ξ hU hξ i =
      MeasurableSpace.comap
        (fun ω => idealStageCumulativeData hT (U ω) A r (ξ ω) a i) inferInstance := by
  change (Filtration.piLE (X := fun _ : ℕ => IdealStageAnalysisData d T N) i).comap
    (fun ω j => idealStageObservation hT (U ω) A r (ξ ω) a j) = _
  simp only [Filtration.piLE, MeasurableSpace.comap_comp]
  rfl

theorem idealStageFiltration_mono
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [mΩ : MeasurableSpace Ω]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) {i j : ℕ} (hij : i ≤ j) :
    idealStageFiltration hT A r a U ξ hU hξ i ≤
      idealStageFiltration hT A r a U ξ hU hξ j :=
  (idealStageFiltration hT A r a U ξ hU hξ).mono hij

theorem idealStoppedPreHistory_time_eq_stageStart
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) :
    (idealStoppedPreHistory hT U j A r ξ a).time =
      idealStageStart hT U A r ξ a (j.val + 1) := by
  let τ := idealStageStart hT U A r ξ a (j.val + 1)
  change (idealPreHistoryAtTime hT U A r ξ a τ).time = τ
  by_cases hτ : τ ≤ N
  · simp only [idealPreHistoryAtTime, dite_eq_left hτ]
  · have hb : τ ≤ N + 1 := idealStageStart_le_succ hT U A r ξ a (j.val + 1)
    have heq : τ = N + 1 := by omega
    simp only [idealPreHistoryAtTime, dite_eq_right hτ]
    exact heq.symm

theorem measurable_idealStageStart_at_stageFiltration
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [mΩ : MeasurableSpace Ω]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) (i : ℕ) (hi : i < T) :
    Measurable[idealStageFiltration hT A r a U ξ hU hξ i]
      (fun ω => idealStageStart hT (U ω) A r (ξ ω) a (i + 1)) := by
  have hc : Measurable[idealStageFiltration hT A r a U ξ hU hξ i]
      (fun ω => idealStageCumulativeData hT (U ω) A r (ξ ω) a i) := by
    rw [idealStageFiltration_eq_cumulative]
    exact comap_measurable _
  have hobs := (measurable_pi_apply (⟨i, by simp⟩ : Set.Iic i)).comp hc
  have ht : Measurable[idealStageFiltration hT A r a U ξ hU hξ i]
      (fun ω => (idealStageObservation hT (U ω) A r (ξ ω) a i).2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hobs))
  have hj : idealPrefixIndex hT i = (⟨i, hi⟩ : Fin T) := by
    apply Fin.ext
    simp only [idealPrefixIndex]
    omega
  simpa only [idealStageObservation, idealPreResponseTuple,
    idealStoppedPreHistory_time_eq_stageStart, hj] using ht

/-- X_i is known at level i because the cumulative data contain both stage
clocks.  The virtual stage-zero clock is public, and sentinel clocks stay N+1. -/
theorem idealShortStageIndicator_stronglyAdapted
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [mΩ : MeasurableSpace Ω]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) (m : ℕ) :
    StronglyAdapted (idealStageFiltration hT A r a U ξ hU hξ)
      (fun i ω => idealShortStageIndicator hT (U ω) A r (ξ ω) a m i) := by
  classical
  intro i
  by_cases hi : i < T
  · have hn := measurable_idealStageStart_at_stageFiltration hT A r a U ξ hU hξ i hi
    have hp : Measurable[idealStageFiltration hT A r a U ξ hU hξ i]
        (fun ω => idealStageStart hT (U ω) A r (ξ ω) a i) := by
      by_cases hz : i = 0
      · subst i
        simpa only [idealStageStart_zero] using
          (measurable_const : Measurable[idealStageFiltration hT A r a U ξ hU hξ 0]
            (fun _ : Ω => (0 : ℕ)))
      · have hk : i - 1 < T := by omega
        have hprev := (measurable_idealStageStart_at_stageFiltration
          hT A r a U ξ hU hξ (i - 1) hk).mono
          ((idealStageFiltration hT A r a U ξ hU hξ).mono (Nat.sub_le i 1)) le_rfl
        have heq : i - 1 + 1 = i := by omega
        simpa only [heq] using hprev
    have hcode : Measurable (fun z : ℕ × ℕ =>
        if z.1 ≤ N ∧ z.1 - z.2 ≤ m then (1 : ℝ) else 0) := measurable_of_countable _
    have hX := hcode.comp (hn.prodMk hp)
    have hmeas : Measurable[idealStageFiltration hT A r a U ξ hU hξ i]
        (fun ω => idealShortStageIndicator hT (U ω) A r (ξ ω) a m i) := by
      simpa [idealShortStageIndicator, hi, idealShortCompletedStage, idealStageLength,
        Function.comp_def] using hX
    exact hmeas.stronglyMeasurable
  · simpa only [idealShortStageIndicator, dite_eq_right hi] using
      (stronglyMeasurable_const :
        StronglyMeasurable[idealStageFiltration hT A r a U ξ hU hξ i]
          (fun _ : Ω => (0 : ℝ)))

end

end HeavyTailedNoise
