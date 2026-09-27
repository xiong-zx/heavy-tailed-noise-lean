import HeavyTailedNoise.Lower.Gated.IdealAccidentSingleColumnProbability
import HeavyTailedNoise.Lower.Gated.JointPrefixGradientMeas

/-!
Public joint measurability for the existing ideal protocol. The proof follows
the actual `idealStateAt` recursion on its stage and complete transcript;
there is no second algorithm or state recursion. It uses the checked public
joint prefix-gradient theorem and the algorithm's measurable decision/output
fields. No private declarations are accessed.

The public state/decision results include the arbitrary measurable private
source jointly. Fixing one private seed is just composition with a constant
coordinate. Prefix extension, masking, and soft projection then discharge the
factor measurability parameter of the full-horizon accident theorem.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem measurableSet_idealCapHit_joint
    {d T : ℕ} (hT : 0 < T) (s : ℕ) :
    MeasurableSet {z : (Fin T → Point d) × Point d | idealCapHit z.1 s z.2} := by
  by_cases hs : s < T
  · let j : Fin T := ⟨s, hs⟩
    have ht : (0 : ℝ) < T := by exact_mod_cast hT
    have hR : 0 < hardRadius T := by unfold hardRadius; positivity
    have hpair : Measurable (fun z : (Fin T → Point d) × Point d =>
        (z.1, softProjection (hardRadius T) z.2)) :=
      measurable_fst.prodMk ((contDiff_softProjection_two hR).continuous.measurable.comp
        measurable_snd)
    have hc : Measurable (fun z : (Fin T → Point d) × Point d =>
        frameCoordinates z.1 (softProjection (hardRadius T) z.2) j) :=
      ((measurable_pi_apply j).comp
        contDiff_joint_frameCoordinates_two.continuous.measurable).comp hpair
    have hr : Measurable (fun z : (Fin T → Point d) × Point d =>
        frameOrthogonalResidual z.1 (Finset.univ.filter (· ≤ j))
          (softProjection (hardRadius T) z.2)) :=
      (contDiff_joint_frameOrthogonalResidual_two
        (Finset.univ.filter (· ≤ j))).continuous.measurable.comp hpair
    have heq : {z : (Fin T → Point d) × Point d | idealCapHit z.1 s z.2} =
        {z | (1 / 2 : ℝ) ≤ |frameCoordinates z.1
            (softProjection (hardRadius T) z.2) j| ∧
          ‖frameOrthogonalResidual z.1 (Finset.univ.filter (· ≤ j))
            (softProjection (hardRadius T) z.2)‖ ^ 2 ≤
              (1000 + 1 / 16 + 1 : ℝ)} := by
      ext z
      constructor
      · rintro ⟨hs', hz⟩
        simpa [prefixCapSet, j] using hz
      · intro hz
        exact ⟨hs, by simpa [prefixCapSet, j] using hz⟩
    rw [heq]
    exact (measurableSet_le measurable_const hc.abs).inter
      (measurableSet_le (hr.norm.pow_const 2) measurable_const)
  · have heq : {z : (Fin T → Point d) × Point d | idealCapHit z.1 s z.2} = ∅ := by
      ext z
      simp [idealCapHit, hs]
    rw [heq]
    exact MeasurableSet.empty

theorem measurable_idealStageAfter_joint
    {d T : ℕ} (hT : 0 < T) :
    Measurable (fun z : ℕ × ((Fin T → Point d) × Point d) =>
      idealStageAfter z.2.1 z.1 z.2.2) := by
  classical
  apply measurable_from_prod_countable_right
  intro s
  change Measurable (fun z : (Fin T → Point d) × Point d =>
    if idealCapHit z.1 s z.2 then s + 1 else s)
  exact Measurable.ite (measurableSet_idealCapHit_joint hT s)
    measurable_const measurable_const

theorem measurable_idealResponseMean_joint
    {d T : ℕ} (hT : 0 < T) :
    Measurable (fun z : ℕ × ((Fin T → Point d) × Point d) =>
      idealResponseMean hT z.2.1 z.1 z.2.2) := by
  apply measurable_from_prod_countable_right
  intro s
  exact measurable_joint_prefixGradient hT (idealPrefixIndex hT s)

/-- Joint measurability of both fields of the actual ideal state. Private
randomness needs only its existing measurable-space structure. -/
theorem measurable_idealStateAt_fields_joint
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (a : ℝ) (n : ℕ) :
    Measurable (fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      (idealStateAt hT z.1 A z.2.1 z.2.2 a n).stage) ∧
    Measurable (fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      (idealStateAt hT z.1 A z.2.1 z.2.2 a n).transcript) := by
  induction n with
  | zero =>
    constructor
    · exact measurable_const
    · apply measurable_pi_iff.mpr
      intro i
      exact i.elim0
  | succ n ih =>
    let st := fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      idealStateAt hT z.1 A z.2.1 z.2.2 a n
    let q := fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      A.decide n z.2.1 (st z).transcript
    let next := fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      idealStageAfter z.1 (st z).stage (q z)
    let y := fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      idealResponseMean hT z.1 (next z) (q z) + a • idealNoiseAt z.2.2 n
    have hq : Measurable q := (A.measurable_decide n).comp
      ((measurable_fst.comp measurable_snd).prodMk ih.2)
    have hnext : Measurable next := (measurable_idealStageAfter_joint hT).comp
      (ih.1.prodMk (measurable_fst.prodMk hq))
    have hnoise : Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) => idealNoiseAt z.2.2 n) := by
      by_cases hn : n < N
      · simp only [idealNoiseAt, dite_eq_left hn]
        exact (measurable_pi_apply (⟨n, hn⟩ : Fin N)).comp
          (measurable_snd.comp measurable_snd)
      · simpa only [idealNoiseAt, dite_eq_right hn] using
          (measurable_const : Measurable (fun _ : (Fin T → Point d) ×
            (Private × (Fin N → Point d)) => (0 : Point d)))
    have hinput : Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) => (next z, (z.1, q z))) :=
      hnext.prodMk (measurable_fst.prodMk hq)
    have hmean : Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) => idealResponseMean hT z.1 (next z) (q z)) := by
      have hcomp := (measurable_idealResponseMean_joint hT).comp hinput
      simpa only [Function.comp_def] using hcomp
    have hscaled : Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) => a • idealNoiseAt z.2.2 n) :=
      (measurable_const : Measurable (fun _ : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) => (a : ℝ))).smul hnoise
    have hy : Measurable y := hmean.add hscaled
    constructor
    · change Measurable next
      exact hnext
    · change Measurable (fun z : (Fin T → Point d) ×
        (Private × (Fin N → Point d)) =>
        Fin.snoc (α := fun _ : Fin (n + 1) => Point d × Point d)
          (st z).transcript (q z, y z))
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hq.prodMk hy
      · simpa only [Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply j).comp ih.2

/-- Includes the arbitrary output branch after the fixed response cap. -/
theorem measurable_idealDecisionAt_joint
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (a : ℝ) (t : ℕ) :
    Measurable (fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      idealDecisionAt hT z.1 A z.2.1 z.2.2 a t) := by
  by_cases ht : t < N
  · have htr := (measurable_idealStateAt_fields_joint hT A a t).2
    have hq := (A.measurable_decide t).comp
      ((measurable_fst.comp measurable_snd).prodMk htr)
    simpa only [idealDecisionAt, dite_eq_left ht, Function.comp_def] using hq
  · have htr := (measurable_idealStateAt_fields_joint hT A a N).2
    have hq := A.measurable_output.comp
      ((measurable_fst.comp measurable_snd).prodMk htr)
    simpa only [idealDecisionAt, dite_eq_right ht, Function.comp_def] using hq

theorem measurable_idealPrefixMaskedQueryAt_joint
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (a : ℝ) (t : ℕ) :
    Measurable (fun z : (Fin T → Point d) × (Private × (Fin N → Point d)) =>
      idealPrefixMaskedQueryAt hT z.1 k A z.2.1 z.2.2 a t) := by
  have hstage := (measurable_idealStateAt_fields_joint hT A a t).1
  have hgate : MeasurableSet {z : (Fin T → Point d) ×
      (Private × (Fin N → Point d)) |
      (idealStateAt hT z.1 A z.2.1 z.2.2 a t).stage ≤ k.val} :=
    measurableSet_le hstage measurable_const
  exact Measurable.ite hgate (measurable_idealDecisionAt_joint hT A a t) measurable_const

/-- The exact joint factor measurability formerly supplied as an analytic
parameter. This holds for every time; the probability application uses `t≤N`.
-/
theorem measurable_idealFutureProjectedFactor
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) (t : ℕ) :
    Measurable (idealFutureProjectedFactor hT k A r a t) := by
  change Measurable (fun p : (Fin (k.val + 1) → Point d) ×
    (Fin N → Point d) => softProjection (hardRadius T)
      (idealPrefixMaskedQueryAt hT (idealPrefixExtension k p.1) k A r p.2 a t))
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < hardRadius T := by unfold hardRadius; positivity
  have hproj : Measurable (softProjection (d := d) (hardRadius T)) :=
    (contDiff_softProjection_two hR).continuous.measurable
  have hinput : Measurable (fun p : (Fin (k.val + 1) → Point d) ×
      (Fin N → Point d) => (idealPrefixExtension k p.1, (r, p.2))) :=
    ((measurable_idealPrefixExtension k).comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)
  have hcomp := (hproj.comp (measurable_idealPrefixMaskedQueryAt_joint hT k A a t)).comp hinput
  simpa only [Function.comp_def] using hcomp

/-- The full ideal accident probability estimate now has no unproved
measurability parameter. Its public sharp-cap dimension condition is retained.
-/
theorem idealPrefixAccident_horizon_probability
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hTd : T ≤ d)
    (hDim : 4096 * (hardRadius T) ^ 2 ≤ ((d - T : ℕ) : ℝ))
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    (((preselectedOrthonormalFrameLaw d T hTd).prod
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d))).real
      {z : IdealAccidentSample d T N |
        ∃ t ≤ N, idealPrefixAccidentAt hT z.1.1 A r z.2 a t}) ≤
      2 * (N + 2 : ℕ) * T *
        Real.exp (-((d - T : ℕ) : ℝ) / (2048 * (hardRadius T) ^ 2)) :=
  idealPrefixAccident_horizon_probability_bound hT hTd hDim A r a
    (fun t i hi => measurable_idealFutureProjectedFactor
      hT (idealFuturePredecessor i hi) A r a t.val)

end

end HeavyTailedNoise
