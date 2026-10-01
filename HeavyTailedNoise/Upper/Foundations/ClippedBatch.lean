import HeavyTailedNoise.Upper.Foundations.ClipGeometry
import HeavyTailedNoise.Upper.Foundations.UpperBatchProtocol

/-!
One fresh batch may be passed through several deterministic clipping maps.  The
probabilistic unit is the *whole transformed response*, so no independence of
the maps applied to one seed is assumed.  History is fixed before the product
law of the fresh seeds is sampled.  The estimates here use bounded transforms;
they do not assert a conditional moment bound for the unbounded residual.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace HeavyTailedNoise

/-- A deterministic transform of one residual, averaged over one fresh batch. -/
def upperResidualBatchMean {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (x w : Point d) (seeds : Fin b → Seed) : Point d :=
  (b : ℝ)⁻¹ • ∑ i : Fin b, φ (O.response x (seeds i) - w)

/-- The source mean uses a fresh auxiliary seed, not an additional oracle call. -/
def upperResidualSourceMean {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (x w : Point d) : Point d :=
  ∫ ξ, φ (O.response x ξ - w) ∂O.law

/-- Each fresh coordinate is a measurable clipped residual even when its
pre-batch decision and center depend on arbitrary measurable history. -/
theorem measurable_upperClippedResidual_coordinate
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) {τ : ℝ} (hτ : 0 < τ)
    (x w : History → Point d) (hx : Measurable x) (hw : Measurable w)
    (i : Fin b) :
    Measurable (fun z : History × (Fin b → Seed) =>
      upperClip τ (O.response (x z.1) (z.2 i) - w z.1)) := by
  exact (measurable_upperClip hτ).comp
    ((O.measurable_response.comp
      ((hx.comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))).sub
          (hw.comp measurable_fst))

theorem measurable_upperResidualBatchMean
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (x w : History → Point d)
    (hx : Measurable x) (hw : Measurable w) :
    Measurable (fun z : History × (Fin b → Seed) =>
      upperResidualBatchMean O φ (x z.1) (w z.1) z.2) := by
  unfold upperResidualBatchMean
  have hsum : Measurable (fun z : History × (Fin b → Seed) =>
      ∑ i : Fin b, φ (O.response (x z.1) (z.2 i) - w z.1)) := by
    apply Finset.measurable_sum
    intro i hi
    exact hφ.comp ((O.measurable_response.comp
      ((hx.comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))).sub
          (hw.comp measurable_fst))
  exact (measurable_const : Measurable
    (fun _ : History × (Fin b → Seed) => (b : ℝ)⁻¹)).smul hsum

theorem measurable_upperClippedBatchMean
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) {τ : ℝ} (hτ : 0 < τ)
    (x w : History → Point d) (hx : Measurable x) (hw : Measurable w) :
    Measurable (fun z : History × (Fin b → Seed) =>
      upperResidualBatchMean O (upperClip τ) (x z.1) (w z.1) z.2) :=
  measurable_upperResidualBatchMean O (upperClip τ)
    (measurable_upperClip hτ) x w hx hw

theorem measurable_upperShellBatchMean
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) {τhi τlo : ℝ}
    (hhi : 0 < τhi) (hlo : 0 < τlo)
    (x w : History → Point d) (hx : Measurable x) (hw : Measurable w) :
    Measurable (fun z : History × (Fin b → Seed) =>
      upperResidualBatchMean O (upperShell τhi τlo) (x z.1) (w z.1) z.2) :=
  measurable_upperResidualBatchMean O (upperShell τhi τlo)
    (measurable_upperShell hhi hlo) x w hx hw

/-- A bounded transformed residual is integrable for each fixed pre-batch
decision and center.  The raw residual itself need not have a second moment. -/
theorem upperResidualSource_integrable
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (x w : Point d) :
    Integrable (fun ξ => φ (O.response x ξ - w)) O.law := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  have hresponse : Measurable (O.response x) :=
    O.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (fun ξ => φ (O.response x ξ - w)) :=
    hφ.comp (hresponse.sub measurable_const)
  exact Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ξ => hC _))

theorem upperResidualBatchMean_integrable
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (x w : Point d) :
    Integrable (upperResidualBatchMean O φ x w) (freshSeedLaw O b) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  have hInt := upperResidualSource_integrable O φ hφ C hC x w
  have hsum : Integrable (fun seeds : Fin b → Seed =>
      ∑ i : Fin b, φ (O.response x (seeds i) - w)) (freshSeedLaw O b) := by
    apply integrable_finsetSum
    intro i hi
    change Integrable (fun seeds : Fin b → Seed =>
      φ (O.response x (seeds i) - w))
      (Measure.pi (fun _ : Fin b => O.law))
    exact integrable_comp_eval (μ := fun _ : Fin b => O.law) (i := i) hInt
  have hrepr : upperResidualBatchMean O φ x w =
      (b : ℝ)⁻¹ • (fun seeds : Fin b → Seed =>
        ∑ i : Fin b, φ (O.response x (seeds i) - w)) := by
    funext seeds
    rfl
  rw [hrepr]
  exact hsum.smul (b : ℝ)⁻¹

/-- Conditional on any fixed history, averaging the independent coordinates
has exactly the one-source mean.  The transform may combine all clipping
scales of one response. -/
theorem upperResidualBatchMean_inner
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (x w : Point d) (hb : 0 < b) :
    (∫ seeds, upperResidualBatchMean O φ x w seeds
      ∂freshSeedLaw O b) = upperResidualSourceMean O φ x w := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  have hInt := upperResidualSource_integrable O φ hφ C hC x w
  have hcoord (i : Fin b) : Integrable
      (fun seeds : Fin b → Seed => φ (O.response x (seeds i) - w))
      (freshSeedLaw O b) := by
    change Integrable (fun seeds : Fin b → Seed =>
      φ (O.response x (seeds i) - w))
      (Measure.pi (fun _ : Fin b => O.law))
    exact integrable_comp_eval (μ := fun _ : Fin b => O.law) (i := i) hInt
  have hbReal : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  calc
    (∫ seeds, upperResidualBatchMean O φ x w seeds
      ∂freshSeedLaw O b) =
        (b : ℝ)⁻¹ • ∫ seeds : Fin b → Seed,
          ∑ i : Fin b, φ (O.response x (seeds i) - w)
          ∂freshSeedLaw O b := by
            change (∫ seeds : Fin b → Seed,
              (b : ℝ)⁻¹ • ∑ i : Fin b, φ (O.response x (seeds i) - w)
              ∂freshSeedLaw O b) = _
            rw [integral_smul]
    _ = (b : ℝ)⁻¹ • ∑ i : Fin b,
        ∫ seeds : Fin b → Seed, φ (O.response x (seeds i) - w)
          ∂freshSeedLaw O b := by
            rw [integral_finsetSum]
            intro i hi
            exact hcoord i
    _ = (b : ℝ)⁻¹ • ∑ _i : Fin b, upperResidualSourceMean O φ x w := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      unfold freshSeedLaw upperResidualSourceMean
      exact integral_comp_eval (μ := fun _ : Fin b => O.law) (i := i)
        hInt.aestronglyMeasurable
    _ = upperResidualSourceMean O φ x w := by
      simp only [Finset.sum_const, Finset.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℝ b (upperResidualSourceMean O φ x w),
        smul_smul, inv_mul_cancel₀ hbReal, one_smul]

/-- The clipped batch has its exact conditional source mean after the
pre-batch decision and center have been fixed. -/
theorem upperClippedBatchMean_inner
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) {τ : ℝ} (hτ : 0 < τ)
    (x w : Point d) (hb : 0 < b) :
    (∫ seeds, upperResidualBatchMean O (upperClip τ) x w seeds
      ∂freshSeedLaw O b) = upperResidualSourceMean O (upperClip τ) x w :=
  upperResidualBatchMean_inner O (upperClip τ) (measurable_upperClip hτ)
    τ (upperClip_norm_le hτ) x w hb

/-- A pointwise conditional-mean identity under the product law of pre-batch
history and fresh seeds; no moment of `response - w` is assumed. -/
theorem predictable_upperClippedBatchMean_inner
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) {τ : ℝ} (hτ : 0 < τ)
    (x w : History → Point d) (hb : 0 < b) (h : History) :
    (∫ seeds, upperResidualBatchMean O (upperClip τ) (x h) (w h) seeds
      ∂freshSeedLaw O b) =
      upperResidualSourceMean O (upperClip τ) (x h) (w h) :=
  upperClippedBatchMean_inner O hτ (x h) (w h) hb

/-- The source mean is measurable as a function of the whole pre-batch
history. The fresh seed is integrated only after that history is fixed. -/
theorem measurable_upperResidualSourceMean
    {d : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (x w : History → Point d)
    (hx : Measurable x) (hw : Measurable w) :
    Measurable (fun h => upperResidualSourceMean O φ (x h) (w h)) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  have hjoint : Measurable (fun z : History × Seed =>
      φ (O.response (x z.1) z.2 - w z.1)) :=
    hφ.comp ((O.measurable_response.comp
      ((hx.comp measurable_fst).prodMk measurable_snd)).sub
        (hw.comp measurable_fst))
  have hmean : StronglyMeasurable (fun h : History =>
      ∫ ξ : Seed, φ (O.response (x h) ξ - w h) ∂O.law) :=
    hjoint.stronglyMeasurable.integral_prod_right' (ν := O.law)
  exact hmean.measurable

/-- Joint integrability uses only the bounded deterministic transform.  It
does not require the predicted center or raw residual to have a conditional
second moment. -/
theorem upperResidualBatchMean_joint_integrable
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x w : History → Point d) (hx : Measurable x) (hw : Measurable w) :
    Integrable (fun z : History × (Fin b → Seed) =>
      upperResidualBatchMean O φ (x z.1) (w z.1) z.2)
      (historyLaw.prod (freshSeedLaw O b)) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw O b) := by
    unfold freshSeedLaw
    infer_instance
  have hcoord (i : Fin b) : Integrable
      (fun z : History × (Fin b → Seed) =>
        φ (O.response (x z.1) (z.2 i) - w z.1))
      (historyLaw.prod (freshSeedLaw O b)) := by
    have hm : Measurable (fun z : History × (Fin b → Seed) =>
        φ (O.response (x z.1) (z.2 i) - w z.1)) :=
      hφ.comp ((O.measurable_response.comp
        ((hx.comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd))).sub
            (hw.comp measurable_fst))
    exact Integrable.of_bound hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun z => hC _))
  have hsum : Integrable (fun z : History × (Fin b → Seed) =>
      ∑ i : Fin b, φ (O.response (x z.1) (z.2 i) - w z.1))
      (historyLaw.prod (freshSeedLaw O b)) := by
    apply integrable_finsetSum
    intro i hi
    exact hcoord i
  have hrepr : (fun z : History × (Fin b → Seed) =>
      upperResidualBatchMean O φ (x z.1) (w z.1) z.2) =
      (b : ℝ)⁻¹ • (fun z : History × (Fin b → Seed) =>
        ∑ i : Fin b, φ (O.response (x z.1) (z.2 i) - w z.1)) := by
    funext z
    rfl
  rw [hrepr]
  exact hsum.smul (b : ℝ)⁻¹

theorem upperResidualSourceMean_joint_integrable
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x w : History → Point d) (hx : Measurable x) (hw : Measurable w) :
    Integrable (fun z : History × (Fin b → Seed) =>
      upperResidualSourceMean O φ (x z.1) (w z.1))
      (historyLaw.prod (freshSeedLaw O b)) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw O b) := by
    unfold freshSeedLaw
    infer_instance
  have hm := measurable_upperResidualSourceMean O φ hφ x w hx hw
  have hbound (h : History) : ‖upperResidualSourceMean O φ (x h) (w h)‖ ≤ C := by
    unfold upperResidualSourceMean
    simpa using (norm_integral_le_of_norm_le_const (μ := O.law)
      (Filter.Eventually.of_forall (fun ξ => hC
        (O.response (x h) ξ - w h))))
  have hint : Integrable (fun h => upperResidualSourceMean O φ (x h) (w h))
      historyLaw :=
    Integrable.of_bound hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbound)
  exact hint.comp_fst (freshSeedLaw O b)

theorem upperResidualBatchMean_centered_inner
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (x w : Point d) (hb : 0 < b) :
    (∫ seeds, upperResidualBatchMean O φ x w seeds -
      upperResidualSourceMean O φ x w ∂freshSeedLaw O b) = 0 := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw O b) := by
    unfold freshSeedLaw
    infer_instance
  have hbatchInt : Integrable (upperResidualBatchMean O φ x w)
      (freshSeedLaw O b) :=
    upperResidualBatchMean_integrable (b := b) O φ hφ C hC x w
  rw [integral_sub hbatchInt (integrable_const _),
    upperResidualBatchMean_inner O φ hφ C hC x w hb]
  simp

/-- Condition on the entire history before the whole batch. A fresh response
may be reused in every clipping scale inside `φ`, but no response from this
batch is included in the conditioning sigma-field. -/
theorem upperResidualBatchMean_centered_condExp
    {d b : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (historyLaw : Measure History) [IsProbabilityMeasure historyLaw]
    (x w : History → Point d) (hx : Measurable x) (hw : Measurable w)
    (hb : 0 < b) :
    (historyLaw.prod (freshSeedLaw O b))[
      (fun z : History × (Fin b → Seed) =>
        upperResidualBatchMean O φ (x z.1) (w z.1) z.2 -
          upperResidualSourceMean O φ (x z.1) (w z.1)) |
      MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace History)]
      =ᵐ[historyLaw.prod (freshSeedLaw O b)] 0 := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw O b) := by
    unfold freshSeedLaw
    infer_instance
  have hm : MeasurableSpace.comap
      (Prod.fst : History × (Fin b → Seed) → History)
      (inferInstance : MeasurableSpace History) ≤
      (inferInstance : MeasurableSpace (History × (Fin b → Seed))) :=
    (measurable_fst : Measurable
      (Prod.fst : History × (Fin b → Seed) → History)).comap_le
  have hInt : Integrable (fun z : History × (Fin b → Seed) =>
      upperResidualBatchMean O φ (x z.1) (w z.1) z.2 -
        upperResidualSourceMean O φ (x z.1) (w z.1))
      (historyLaw.prod (freshSeedLaw O b)) :=
    (upperResidualBatchMean_joint_integrable O φ hφ C hC
      historyLaw x w hx hw).sub
      (upperResidualSourceMean_joint_integrable O φ hφ C hC
        historyLaw x w hx hw)
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hInt ?_ ?_ ?_
  · intro s hs hfinite
    exact integrable_zero _ _ _
  · intro s hs hfinite
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hset : (Prod.fst ⁻¹' t : Set (History × (Fin b → Seed))) =
        t ×ˢ Set.univ := by
      ext z
      simp
    rw [hset]
    simp only [Pi.zero_apply, integral_zero]
    rw [setIntegral_prod _ hInt.integrableOn]
    simp only [Measure.restrict_univ]
    simp_rw [upperResidualBatchMean_centered_inner O φ hφ C hC (x _) (w _) hb]
    simp
  · exact stronglyMeasurable_zero.aestronglyMeasurable

theorem upperResidualBatchMean_coordinate_memLp
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (x w : Point d) (k : Fin d) :
    MemLp (fun seeds : Fin b → Seed =>
      (upperResidualBatchMean O φ x w seeds) k) 2 (freshSeedLaw O b) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  let f : Seed → ℝ := fun ξ => (φ (O.response x ξ - w)) k
  have hresponse : Measurable (O.response x) :=
    O.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hvec : Measurable (fun ξ : Seed => φ (O.response x ξ - w)) :=
    hφ.comp (hresponse.sub
      (measurable_const : Measurable (fun _ : Seed => w)))
  have hf : Measurable f :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) k).measurable.comp hvec
  have hbound (ξ : Seed) : ‖f ξ‖ ≤ C :=
    (PiLp.norm_apply_le (φ (O.response x ξ - w)) k).trans (hC _)
  have hMem : MemLp f 2 O.law :=
    MemLp.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbound)
  have hcoord (i : Fin b) : MemLp
      (fun seeds : Fin b → Seed => f (seeds i)) 2 (freshSeedLaw O b) := by
    change MemLp (fun seeds : Fin b → Seed => f (seeds i)) 2
      (Measure.pi (fun _ : Fin b => O.law))
    exact hMem.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin b => O.law) i)
  have hsum : MemLp (fun seeds : Fin b → Seed =>
      ∑ i : Fin b, f (seeds i)) 2 (freshSeedLaw O b) := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    exact hcoord i
  have hscaled := hsum.const_smul (b : ℝ)⁻¹
  have hfun :
      (fun seeds : Fin b → Seed => (upperResidualBatchMean O φ x w seeds) k) =
      (b : ℝ)⁻¹ • (fun seeds : Fin b → Seed =>
        ∑ i : Fin b, f (seeds i)) := by
    funext seeds
    simp [upperResidualBatchMean, f]
  rw [hfun]
  exact hscaled

/-- Each scalar coordinate of the *whole transformed batch* has exactly the
usual independent-sample variance.  In particular `φ` may be a sum of all
clipping bands applied to each one response; this theorem assumes no
independence among the bands within a response. -/
theorem upperResidualBatchMean_coordinate_variance
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (x w : Point d) (hb : 0 < b) (k : Fin d) :
    ProbabilityTheory.variance
      (fun seeds : Fin b → Seed => (upperResidualBatchMean O φ x w seeds) k)
      (freshSeedLaw O b) =
      (b : ℝ)⁻¹ * ProbabilityTheory.variance
        (fun ξ => (φ (O.response x ξ - w)) k) O.law := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  let f : Seed → ℝ := fun ξ => (φ (O.response x ξ - w)) k
  have hresponse : Measurable (O.response x) :=
    O.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hvec : Measurable (fun ξ : Seed => φ (O.response x ξ - w)) :=
    hφ.comp (hresponse.sub
      (measurable_const : Measurable (fun _ : Seed => w)))
  have hf : Measurable f :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) k).measurable.comp hvec
  have hbound (ξ : Seed) : ‖f ξ‖ ≤ C := by
    exact (PiLp.norm_apply_le (φ (O.response x ξ - w)) k).trans (hC _)
  have hMem : MemLp f 2 O.law :=
    MemLp.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbound)
  have hbReal : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hfun :
      (fun seeds : Fin b → Seed => (upperResidualBatchMean O φ x w seeds) k) =
      (fun seeds : Fin b → Seed =>
        (b : ℝ)⁻¹ * ∑ i : Fin b, f (seeds i)) := by
    funext seeds
    simp [upperResidualBatchMean, f]
  rw [hfun]
  change ProbabilityTheory.variance
    (fun seeds : Fin b → Seed => (b : ℝ)⁻¹ * ∑ i : Fin b, f (seeds i))
    (Measure.pi (fun _ : Fin b => O.law)) = _
  rw [ProbabilityTheory.variance_const_mul]
  have hsum := ProbabilityTheory.variance_sum_pi
    (μ := fun _ : Fin b => O.law) (X := fun _ : Fin b => f)
    (fun _ => hMem)
  have hsum' : ProbabilityTheory.variance
      (fun seeds : Fin b → Seed => ∑ i : Fin b, f (seeds i))
      (Measure.pi (fun _ : Fin b => O.law)) =
      ∑ i : Fin b, ProbabilityTheory.variance f O.law := by
    have hfunSum :
        (∑ i : Fin b, fun seeds : Fin b → Seed => f (seeds i)) =
        (fun seeds : Fin b → Seed => ∑ i : Fin b, f (seeds i)) := by
      funext seeds
      simp only [Finset.sum_apply]
    rw [hfunSum] at hsum
    exact hsum
  rw [hsum']
  change (b : ℝ)⁻¹ ^ 2 *
      (∑ _i : Fin b, ProbabilityTheory.variance f O.law) =
    (b : ℝ)⁻¹ * ProbabilityTheory.variance f O.law
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp [hbReal]

/-- The exact conditional second moment of the vector batch error.  The right
side is the sum of coordinate variances of one *whole transformed response*;
it retains all covariance among clipping scales inside `φ`. -/
theorem upperResidualBatchMean_secondMoment
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (x w : Point d) (hb : 0 < b) :
    (∫ seeds : Fin b → Seed,
      ‖upperResidualBatchMean O φ x w seeds -
        upperResidualSourceMean O φ x w‖ ^ 2
      ∂freshSeedLaw O b) =
      (b : ℝ)⁻¹ * ∑ k : Fin d, ProbabilityTheory.variance
        (fun ξ => (φ (O.response x ξ - w)) k) O.law := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure (freshSeedLaw O b) := by
    unfold freshSeedLaw
    infer_instance
  let Z : (Fin b → Seed) → Point d := upperResidualBatchMean O φ x w
  let m : Point d := upperResidualSourceMean O φ x w
  have hZ : Integrable Z (freshSeedLaw O b) :=
    upperResidualBatchMean_integrable O φ hφ C hC x w
  have hm : (∫ seeds, Z seeds ∂freshSeedLaw O b) = m :=
    upperResidualBatchMean_inner O φ hφ C hC x w hb
  have hcoordMean (k : Fin d) :
      (∫ seeds, (Z seeds) k ∂freshSeedLaw O b) = m k := by
    let projk : Point d →L[ℝ] ℝ :=
      PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k
    have hproj := projk.integral_comp_comm hZ
    simpa [projk, hm] using hproj
  have hcoordMem (k : Fin d) :
      MemLp (fun seeds : Fin b → Seed => (Z seeds) k) 2 (freshSeedLaw O b) :=
    upperResidualBatchMean_coordinate_memLp O φ hφ C hC x w k
  have hsquare (k : Fin d) : Integrable
      (fun seeds : Fin b → Seed => ((Z seeds - m) k) ^ 2)
      (freshSeedLaw O b) := by
    have h := ((hcoordMem k).sub (memLp_const (m k))).integrable_sq
    simpa [PiLp.sub_apply] using h
  calc
    (∫ seeds : Fin b → Seed, ‖Z seeds - m‖ ^ 2 ∂freshSeedLaw O b) =
        ∫ seeds : Fin b → Seed, ∑ k : Fin d, ((Z seeds - m) k) ^ 2
          ∂freshSeedLaw O b := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun seeds => EuclideanSpace.real_norm_sq_eq _)
    _ = ∑ k : Fin d, ∫ seeds : Fin b → Seed,
        ((Z seeds - m) k) ^ 2 ∂freshSeedLaw O b := by
          rw [integral_finsetSum]
          intro k hk
          exact hsquare k
    _ = ∑ k : Fin d, ProbabilityTheory.variance
        (fun seeds : Fin b → Seed => (Z seeds) k) (freshSeedLaw O b) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [ProbabilityTheory.variance_eq_integral (hcoordMem k).aemeasurable]
          simp only [PiLp.sub_apply, hcoordMean k]
    _ = (b : ℝ)⁻¹ * ∑ k : Fin d, ProbabilityTheory.variance
        (fun ξ => (φ (O.response x ξ - w)) k) O.law := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          exact upperResidualBatchMean_coordinate_variance O φ hφ C hC x w hb k

/-- A reference response may be chosen after the pre-batch history is fixed.
The bound is dimension free and does not require a moment estimate for
`response x ξ - w`; only the transformed difference appears. -/
theorem upperResidualBatchMean_secondMoment_le_reference
    {d b : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (x w a : Point d) (hb : 0 < b) :
    (∫ seeds : Fin b → Seed,
      ‖upperResidualBatchMean O φ x w seeds -
        upperResidualSourceMean O φ x w‖ ^ 2
      ∂freshSeedLaw O b) ≤
      (b : ℝ)⁻¹ * ∫ ξ,
        ‖φ (O.response x ξ - w) - φ (a - w)‖ ^ 2 ∂O.law := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  have hresponse : Measurable (O.response x) :=
    O.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hvec : Measurable (fun ξ => φ (O.response x ξ - w)) :=
    hφ.comp (hresponse.sub measurable_const)
  let c : Point d := φ (a - w)
  have hcoord (k : Fin d) :
      ProbabilityTheory.variance
        (fun ξ => (φ (O.response x ξ - w)) k) O.law ≤
        ∫ ξ, ((φ (O.response x ξ - w) - c) k) ^ 2 ∂O.law := by
    let f : Seed → ℝ := fun ξ => (φ (O.response x ξ - w)) k
    have hf : Measurable f :=
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) k).measurable.comp hvec
    let fs : Seed → ℝ := fun ξ => f ξ - c k
    have hfs : Measurable fs :=
      hf.sub (measurable_const : Measurable (fun _ : Seed => c k))
    have hshift : ProbabilityTheory.variance fs O.law =
        ProbabilityTheory.variance f O.law :=
      ProbabilityTheory.variance_sub_const hf.aestronglyMeasurable (c k)
    calc
      ProbabilityTheory.variance f O.law = ProbabilityTheory.variance fs O.law :=
        hshift.symm
      _ ≤ ∫ ξ, fs ξ ^ 2 ∂O.law :=
        ProbabilityTheory.variance_le_expectation_sq hfs.aestronglyMeasurable
      _ = ∫ ξ, ((φ (O.response x ξ - w) - c) k) ^ 2 ∂O.law := by
        simp [fs, f, PiLp.sub_apply]
  have hsquare (k : Fin d) : Integrable
      (fun ξ => ((φ (O.response x ξ - w) - c) k) ^ 2) O.law := by
    let f : Seed → ℝ := fun ξ => (φ (O.response x ξ - w)) k
    have hf : Measurable f :=
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) k).measurable.comp hvec
    have hbound (ξ : Seed) : ‖f ξ‖ ≤ C :=
      (PiLp.norm_apply_le (φ (O.response x ξ - w)) k).trans (hC _)
    have hMem : MemLp f 2 O.law :=
      MemLp.of_bound hf.aestronglyMeasurable C
        (Filter.Eventually.of_forall hbound)
    have h := (hMem.sub (memLp_const (c k))).integrable_sq
    simpa [f, c] using h
  calc
    (∫ seeds : Fin b → Seed,
      ‖upperResidualBatchMean O φ x w seeds -
        upperResidualSourceMean O φ x w‖ ^ 2
      ∂freshSeedLaw O b) =
        (b : ℝ)⁻¹ * ∑ k : Fin d, ProbabilityTheory.variance
          (fun ξ => (φ (O.response x ξ - w)) k) O.law :=
            upperResidualBatchMean_secondMoment O φ hφ C hC x w hb
    _ ≤ (b : ℝ)⁻¹ * ∑ k : Fin d,
        ∫ ξ, ((φ (O.response x ξ - w) - c) k) ^ 2 ∂O.law := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg b))
          apply Finset.sum_le_sum
          intro k hk
          exact hcoord k
    _ = (b : ℝ)⁻¹ * ∫ ξ,
        ‖φ (O.response x ξ - w) - c‖ ^ 2 ∂O.law := by
          congr 1
          rw [← integral_finsetSum Finset.univ (fun k _ => hsquare k)]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun ξ =>
            (EuclideanSpace.real_norm_sq_eq _).symm)
    _ = _ := rfl

end HeavyTailedNoise
