import HeavyTailedNoise.Lower.Gated.IdealStoppedHistory
import HeavyTailedNoise.Lower.Gated.JointHardObjective
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
Joint measurability of the actual truncated response gradient.  Fixed-frame
smoothness by itself is insufficient when integrating over the hidden frame.
-/

namespace HeavyTailedNoise

noncomputable section

open InnerProductSpace
open MeasureTheory ProbabilityTheory

private theorem continuous_prefixFrame {d T : ℕ} (j : Fin T) :
    Continuous (fun U : Fin T → Point d => prefixFrame U j) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : i ≤ j
  · simpa [prefixFrame, hi] using
      (continuous_apply i : Continuous (fun U : Fin T → Point d => U i))
  · simpa [prefixFrame, hi] using
      (continuous_const : Continuous (fun _ : Fin T → Point d => (0 : Point d)))

theorem continuous_joint_prefixHardPotential {d T : ℕ}
    (hT : 0 < T) (j : Fin T) :
    Continuous (fun z : (Fin T → Point d) × Point d =>
      prefixHardPotential z.1 j z.2) := by
  have hR : 0 < hardRadius T := by
    unfold hardRadius
    have ht : (0 : ℝ) < T := by exact_mod_cast hT
    positivity
  have hpair : Continuous (fun z : (Fin T → Point d) × Point d =>
      (prefixFrame z.1 j, softProjection (hardRadius T) z.2)) :=
    ((continuous_prefixFrame j).comp continuous_fst).prodMk
      ((contDiff_softProjection_two hR).continuous.comp continuous_snd)
  have hpre : Continuous (fun z : (Fin T → Point d) × Point d =>
      hardPreprojectionPotential z.1 z.2) :=
    contDiff_joint_hardPreprojectionPotential_two.continuous
  have hnorm : Continuous (fun z : (Fin T → Point d) × Point d =>
      (1 / 10 : ℝ) * ‖z.2‖ ^ 2) := by fun_prop
  change Continuous (fun z : (Fin T → Point d) × Point d =>
    hardPreprojectionPotential (prefixFrame z.1 j)
      (softProjection (hardRadius T) z.2) +
        (1 / 10 : ℝ) * ‖z.2‖ ^ 2)
  exact (hpre.comp hpair).add hnorm

theorem measurable_joint_prefixGradient {d T : ℕ}
    (hT : 0 < T) (j : Fin T) :
    Measurable (fun z : (Fin T → Point d) × Point d =>
      gradient (prefixHardPotential z.1 j) z.2) := by
  have hcont : Continuous
      (Function.uncurry (fun U : Fin T → Point d =>
        prefixHardPotential U j)) := by
    change Continuous (fun z : (Fin T → Point d) × Point d =>
      prefixHardPotential z.1 j z.2)
    exact continuous_joint_prefixHardPotential hT j
  have hderiv := measurable_fderiv_with_param ℝ hcont
  change Measurable (fun z : (Fin T → Point d) × Point d =>
    (toDual ℝ (Point d)).symm
      (fderiv ℝ (prefixHardPotential z.1 j) z.2))
  exact (toDual ℝ (Point d)).symm.continuous.measurable.comp hderiv

private theorem measurableSet_joint_idealCapHit {d T : ℕ}
    (hT : 0 < T) (s : ℕ) :
    MeasurableSet {z : (Fin T → Point d) × Point d |
      idealCapHit z.1 s z.2} := by
  classical
  by_cases hs : s < T
  · let j : Fin T := ⟨s, hs⟩
    have hR : 0 < hardRadius T := by
      unfold hardRadius
      have ht : (0 : ℝ) < T := by exact_mod_cast hT
      positivity
    have hpair : Continuous (fun z : (Fin T → Point d) × Point d =>
        (z.1, softProjection (hardRadius T) z.2)) :=
      continuous_fst.prodMk
        ((contDiff_softProjection_two hR).continuous.comp continuous_snd)
    have hcoord : Measurable (fun z : (Fin T → Point d) × Point d =>
        frameCoordinates z.1 (softProjection (hardRadius T) z.2) j) :=
      ((measurable_pi_apply j).comp
        (contDiff_joint_frameCoordinates_two.continuous.measurable)).comp
          hpair.measurable
    have hres : Measurable (fun z : (Fin T → Point d) × Point d =>
        frameOrthogonalResidual z.1 (Finset.univ.filter (· ≤ j))
          (softProjection (hardRadius T) z.2)) :=
      (contDiff_joint_frameOrthogonalResidual_two
        (Finset.univ.filter (· ≤ j))).continuous.measurable.comp
          hpair.measurable
    have hleft : MeasurableSet {z : (Fin T → Point d) × Point d |
        (1 / 2 : ℝ) ≤ |frameCoordinates z.1
          (softProjection (hardRadius T) z.2) j|} :=
      measurableSet_le measurable_const hcoord.abs
    have hright : MeasurableSet {z : (Fin T → Point d) × Point d |
        ‖frameOrthogonalResidual z.1 (Finset.univ.filter (· ≤ j))
          (softProjection (hardRadius T) z.2)‖ ^ 2 ≤
            (1000 + 1 / 16 + 1 : ℝ)} :=
      measurableSet_le (hres.norm.pow_const 2) measurable_const
    have heq : {z : (Fin T → Point d) × Point d |
          idealCapHit z.1 s z.2} =
        {z | (1 / 2 : ℝ) ≤ |frameCoordinates z.1
            (softProjection (hardRadius T) z.2) j| ∧
          ‖frameOrthogonalResidual z.1 (Finset.univ.filter (· ≤ j))
            (softProjection (hardRadius T) z.2)‖ ^ 2 ≤
              (1000 + 1 / 16 + 1 : ℝ)} := by
      ext z
      constructor
      · rintro ⟨hs', hz⟩
        simpa [idealCapHit, prefixCapSet, j] using hz
      · intro hz
        exact ⟨hs, by simpa [prefixCapSet, j] using hz⟩
    rw [heq]
    exact hleft.inter hright
  · have heq : {z : (Fin T → Point d) × Point d |
        idealCapHit z.1 s z.2} = ∅ := by
      ext z
      simp [idealCapHit, hs]
    rw [heq]
    exact MeasurableSet.empty

private theorem measurable_joint_idealStageAfter {d T : ℕ}
    (hT : 0 < T) :
    Measurable (fun z : ℕ × ((Fin T → Point d) × Point d) =>
      idealStageAfter z.2.1 z.1 z.2.2) := by
  classical
  apply measurable_from_prod_countable_right
  intro s
  change Measurable (fun z : (Fin T → Point d) × Point d =>
    if idealCapHit z.1 s z.2 then s + 1 else s)
  exact Measurable.ite (measurableSet_joint_idealCapHit hT s)
    measurable_const measurable_const

private theorem measurable_joint_idealResponseMean {d T : ℕ}
    (hT : 0 < T) :
    Measurable (fun z : ℕ × ((Fin T → Point d) × Point d) =>
      idealResponseMean hT z.2.1 z.1 z.2.2) := by
  apply measurable_from_prod_countable_right
  intro s
  exact measurable_joint_prefixGradient hT (idealPrefixIndex hT s)

private theorem measurable_joint_idealStateAt
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (a : ℝ)
    (n : ℕ) :
    Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
      (idealStateAt hT z.1 A z.2.1 z.2.2 a n).stage) ∧
    Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
      (idealStateAt hT z.1 A z.2.1 z.2.2 a n).transcript) := by
  classical
  induction n with
  | zero =>
      constructor
      · simpa only [idealStateAt] using
          (measurable_const : Measurable
            (fun _ : (Fin T → Point d) ×
              (Private × (Fin N → Point d)) => (0 : ℕ)))
      · apply measurable_pi_iff.mpr
        intro i
        exact i.elim0
  | succ n ih =>
      let st := fun z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) =>
        idealStateAt hT z.1 A z.2.1 z.2.2 a n
      let q := fun z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) =>
        A.decide n z.2.1 (st z).transcript
      let next := fun z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) =>
        idealStageAfter z.1 (st z).stage (q z)
      let y := fun z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) =>
        idealResponseMean hT z.1 (next z) (q z) +
          a • idealNoiseAt z.2.2 n
      have hq : Measurable q :=
        (A.measurable_decide n).comp
          ((measurable_fst.comp measurable_snd).prodMk ih.2)
      have hnext : Measurable next :=
        (measurable_joint_idealStageAfter hT).comp
          (ih.1.prodMk (measurable_fst.prodMk hq))
      have hnoise : Measurable (fun z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) => idealNoiseAt z.2.2 n) := by
        by_cases hn : n < N
        · simp only [idealNoiseAt, dif_pos hn]
          exact (measurable_pi_apply (⟨n, hn⟩ : Fin N)).comp
            (measurable_snd.comp measurable_snd)
        · simpa [idealNoiseAt, hn] using
            (measurable_const : Measurable
              (fun _ : (Fin T → Point d) ×
                (Private × (Fin N → Point d)) => (0 : Point d)))
      have hinput : Measurable (fun z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) => (next z, (z.1, q z))) :=
        hnext.prodMk (measurable_fst.prodMk hq)
      have hmean : Measurable (fun z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) =>
          idealResponseMean hT z.1 (next z) (q z)) := by
        have hcomp :=
          (measurable_joint_idealResponseMean (d := d) (T := T) hT).comp hinput
        simpa only [Function.comp_def] using hcomp
      have hscaled : Measurable (fun z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) =>
          a • idealNoiseAt z.2.2 n) :=
        (measurable_const : Measurable
          (fun _ : (Fin T → Point d) ×
            (Private × (Fin N → Point d)) => a)).smul hnoise
      have hy : Measurable y := hmean.add hscaled
      constructor
      · change Measurable next
        exact hnext
      · change Measurable (fun z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) =>
            Fin.snoc (α := fun _ : Fin (n + 1) =>
              Point d × Point d) (st z).transcript (q z, y z))
        apply measurable_pi_iff.mpr
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using hq.prodMk hy
        · simpa only [Fin.snoc_castSucc, Function.comp_def] using
            (measurable_pi_apply j).comp ih.2

private theorem measurable_joint_idealDecisionAt
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (a : ℝ)
    (t : ℕ) :
    Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
      idealDecisionAt hT z.1 A z.2.1 z.2.2 a t) := by
  classical
  by_cases ht : t < N
  · have htr := (measurable_joint_idealStateAt hT A a t).2
    have hq := (A.measurable_decide t).comp
      ((measurable_fst.comp measurable_snd).prodMk htr)
    simp only [idealDecisionAt, dif_pos ht]
    exact hq
  · have htr := (measurable_joint_idealStateAt hT A a N).2
    have hq := A.measurable_output.comp
      ((measurable_fst.comp measurable_snd).prodMk htr)
    simp only [idealDecisionAt, dif_neg ht]
    exact hq

private theorem measurable_joint_idealAfterAt
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (a : ℝ)
    (t : ℕ) :
    Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
      idealAfterAt hT z.1 A z.2.1 z.2.2 a t) := by
  have hs := (measurable_joint_idealStateAt hT A a t).1
  have hq := measurable_joint_idealDecisionAt hT A a t
  have hinput : Measurable (fun z : (Fin T → Point d) ×
      (Private × (Fin N → Point d)) =>
      ((idealStateAt hT z.1 A z.2.1 z.2.2 a t).stage,
        (z.1, idealDecisionAt hT z.1 A z.2.1 z.2.2 a t))) :=
    hs.prodMk (measurable_fst.prodMk hq)
  have hcomp :=
    (measurable_joint_idealStageAfter (d := d) (T := T) hT).comp hinput
  simpa only [Function.comp_def, idealAfterAt] using hcomp

private theorem measurable_joint_idealStageStart
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (a : ℝ)
    (j : ℕ) :
    Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
      idealStageStart hT z.1 A z.2.1 z.2.2 a j) := by
  classical
  let p : ((Fin T → Point d) ×
      (Private × (Fin N → Point d))) → ℕ → Prop :=
    fun z t =>
      (t ≤ N ∧ j ≤ idealAfterAt hT z.1 A z.2.1 z.2.2 a t) ∨
        t = N + 1
  have hex (z : (Fin T → Point d) ×
      (Private × (Fin N → Point d))) : ∃ t, p z t :=
    ⟨N + 1, Or.inr rfl⟩
  have hpm (t : ℕ) : MeasurableSet
      {z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) | p z t} := by
    have hset : MeasurableSet
        {z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) |
          j ≤ idealAfterAt hT z.1 A z.2.1 z.2.2 a t} :=
      measurableSet_le measurable_const
        (measurable_joint_idealAfterAt hT A a t)
    have hleft : MeasurableSet
        {z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) |
          t ≤ N ∧ j ≤ idealAfterAt hT z.1 A z.2.1 z.2.2 a t} := by
      by_cases ht : t ≤ N
      · simpa [ht] using hset
      · simp [ht]
    have hright : MeasurableSet
        {z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) | t = N + 1} := by
      by_cases ht : t = N + 1 <;> simp [ht]
    change MeasurableSet
      ({z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) |
          t ≤ N ∧ j ≤ idealAfterAt hT z.1 A z.2.1 z.2.2 a t} ∪
        {z : (Fin T → Point d) ×
          (Private × (Fin N → Point d)) | t = N + 1})
    exact hleft.union hright
  have hfind : Measurable (fun z : (Fin T → Point d) ×
      (Private × (Fin N → Point d)) => Nat.find (hex z)) :=
    measurable_find hex hpm
  have heq (z : (Fin T → Point d) ×
      (Private × (Fin N → Point d))) :
      idealStageStart hT z.1 A z.2.1 z.2.2 a j =
        Nat.find (hex z) := by
    let τ := idealStageStart hT z.1 A z.2.1 z.2.2 a j
    have hbound : τ ≤ N + 1 :=
      idealStageStart_le_succ hT z.1 A z.2.1 z.2.2 a j
    have hpτ : p z τ := by
      by_cases hs : τ ≤ N
      · exact Or.inl
          ⟨hs, idealStageStart_hit hT z.1 A z.2.1 z.2.2 a j hs⟩
      · exact Or.inr (by omega)
    have hbefore (t : ℕ) (ht : t < τ) : ¬p z t := by
      rintro (⟨htN, hge⟩ | hsentinel)
      · have hlt := idealStageStart_before hT z.1 A z.2.1 z.2.2 a
          j t ht htN
        omega
      · omega
    exact ((Nat.find_eq_iff (hex z)).2 ⟨hpτ, hbefore⟩).symm
  simpa only [heq] using hfind

private theorem measurable_idealPadTranscript {d N t : ℕ} :
    Measurable (idealPadTranscript (d := d) (N := N) (t := t)) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i.val < t
  · simpa [idealPadTranscript, hi] using
      (measurable_pi_apply (⟨i.val, hi⟩ : Fin t) :
        Measurable (fun tr : Transcript d t => tr ⟨i.val, hi⟩))
  · simpa [idealPadTranscript, hi] using
      (measurable_const : Measurable
        (fun _ : Transcript d t => ((0 : Point d), (0 : Point d))))

private theorem measurable_joint_idealPreHistoryAtTime_fixed
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (a : ℝ)
    (t : ℕ) :
    Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
      idealPreResponseTuple
        (idealPreHistoryAtTime hT z.1 A z.2.1 z.2.2 a t)) := by
  classical
  by_cases ht : t ≤ N
  · have htr := (measurable_joint_idealStateAt hT A a t).2
    have hpad : Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
        idealPadTranscript
          (idealStateAt hT z.1 A z.2.1 z.2.2 a t).transcript) :=
      (measurable_idealPadTranscript (d := d) (N := N) (t := t)).comp htr
    have hq := measurable_joint_idealDecisionAt hT A a t
    have htuple : Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
        ((true, t,
          idealPadTranscript
            (idealStateAt hT z.1 A z.2.1 z.2.2 a t).transcript,
          idealDecisionAt hT z.1 A z.2.1 z.2.2 a t) :
            Bool × ℕ × Transcript d N × Point d)) :=
      measurable_const.prodMk
        (measurable_const.prodMk (hpad.prodMk hq))
    simpa [idealPreHistoryAtTime, idealPreResponseTuple, ht] using htuple
  · have hconst : Measurable (fun _ : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
        ((false, N + 1, fun _ : Fin N => ((0 : Point d), (0 : Point d)),
          (0 : Point d)) : Bool × ℕ × Transcript d N × Point d)) :=
      measurable_const
    simpa [idealPreHistoryAtTime, idealPreResponseTuple, ht] using hconst

private theorem measurable_joint_idealPreHistoryAtTime
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (a : ℝ) :
    Measurable (fun z : ℕ × ((Fin T → Point d) ×
        (Private × (Fin N → Point d))) =>
      idealPreResponseTuple
        (idealPreHistoryAtTime hT z.2.1 A z.2.2.1 z.2.2.2 a z.1)) := by
  apply measurable_from_prod_countable_right
  intro t
  exact measurable_joint_idealPreHistoryAtTime_fixed hT A a t

private theorem measurable_joint_idealStoppedPreHistory
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (a : ℝ) :
    Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
      idealPreResponseTuple
        (idealStoppedPreHistory hT z.1 k A z.2.1 z.2.2 a)) := by
  have hτ := measurable_joint_idealStageStart hT A a (k.val + 1)
  have hinput : Measurable (fun z : (Fin T → Point d) ×
      (Private × (Fin N → Point d)) =>
      (idealStageStart hT z.1 A z.2.1 z.2.2 a (k.val + 1), z)) :=
    hτ.prodMk measurable_id
  have hcomp := (measurable_joint_idealPreHistoryAtTime hT A a).comp hinput
  simpa only [Function.comp_def, idealStoppedPreHistory] using hcomp

/-- The explicit stopped-history factor from the revealed prefix and the
independent joint private tape is measurable. -/
theorem measurable_idealStoppedPreHistoryFromPrefix
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (a : ℝ) :
    Measurable (idealStoppedPreHistoryFromPrefix hT k A a) := by
  have hinput : Measurable (fun z :
      (Fin (k.val + 1) → Point d) ×
        (Private × (Fin N → Point d)) =>
      (idealPrefixExtension k z.1, z.2)) :=
    ((measurable_idealPrefixExtension k).comp measurable_fst).prodMk
      measurable_snd
  have hcomp :=
    (measurable_joint_idealStoppedPreHistory hT k A a).comp hinput
  change Measurable (fun z :
      (Fin (k.val + 1) → Point d) ×
        (Private × (Fin N → Point d)) =>
      idealPreResponseTuple
        (idealStoppedPreHistory hT (idealPrefixExtension k z.1)
          k A z.2.1 z.2.2 a))
  simpa only [Function.comp_def] using hcomp

/-- The next unrevealed frame direction has the intrinsic complement-sphere
conditional law given the actual stopped, pre-response history.  No extra
measurability premise is needed. -/
theorem idealStoppedPreHistory_nextColumn_hasCondDistrib_complete
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hT : 0 < T) (hTd : T ≤ d)
    (k : Fin T) (hk : k.val + 1 + 1 ≤ T)
    (A : RandomAlgorithm d N Private) (a : ℝ)
    (U : Ω → {v : Fin T → Point d // Orthonormal ℝ v})
    (Zvar : Ω → Private × (Fin N → Point d))
    (hU : Measurable U) (hZ : Measurable Zvar)
    (hInd : U ⟂ᵢ[P] Zvar)
    (hLaw : P.map U = preselectedOrthonormalFrameLaw d T hTd) :
    HasCondDistrib
      (fun ω => (framePrefix hk (U ω).1) (Fin.last (k.val + 1)))
      (fun ω =>
        (Fin.init (framePrefix hk (U ω).1),
          idealPreResponseTuple
            (idealStoppedPreHistory hT (U ω).1 k A
              (Zvar ω).1 (Zvar ω).2 a)))
      ((frameNextKernel d (k.val + 1)).comap
        (Prod.fst :
          ((Fin (k.val + 1) → Point d) ×
            (Bool × ℕ × Transcript d N × Point d)) →
              (Fin (k.val + 1) → Point d))
        (measurable_fst : Measurable
          (Prod.fst :
            ((Fin (k.val + 1) → Point d) ×
              (Bool × ℕ × Transcript d N × Point d)) →
                (Fin (k.val + 1) → Point d))))
      P :=
  idealStoppedPreHistory_nextColumn_hasCondDistrib
    P hT hTd k hk A a U Zvar hU hZ hInd hLaw
      (measurable_idealStoppedPreHistoryFromPrefix hT k A a)

end

end HeavyTailedNoise
