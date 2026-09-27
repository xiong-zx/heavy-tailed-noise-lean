import HeavyTailedNoise.Lower.Randomized.Basic
import HeavyTailedNoise.Lower.Randomized.HaarGeometry
import HeavyTailedNoise.Probability.ConditionalParametricMap

/-!
Pathwise invariance for the actual Bernoulli oracle and the shared
full-history randomized-algorithm interface.

This file proves deterministic inputs to the adaptive Haar argument. It
does not turn a prefix conditional law into an actual-history law. The
adaptive projection-conditioned disintegration remains a separate required
probabilistic theorem.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace HeavyTailedNoise.RandomizedLift

/-- Joint measurability of finite Gram--Schmidt, including dependent input
lists. No basis extension or choice of nonzero indices is made. -/
theorem measurable_gramSchmidt_fin (d n : ℕ) (i : Fin n) :
    Measurable (fun v : Fin n → Point d => InnerProductSpace.gramSchmidt ℝ v i) := by
  classical
  induction i using WellFoundedLT.induction with
  | ind i ih =>
      have heq : (fun v : Fin n → Point d => InnerProductSpace.gramSchmidt ℝ v i) =
          (fun v => v i - ∑ k ∈ Finset.Iio i,
            (inner ℝ (InnerProductSpace.gramSchmidt ℝ v k) (v i) /
              ‖InnerProductSpace.gramSchmidt ℝ v k‖ ^ 2) •
                InnerProductSpace.gramSchmidt ℝ v k) := by
        funext v
        apply (eq_sub_iff_add_eq).2
        exact (InnerProductSpace.gramSchmidt_def'' ℝ v i).symm
      rw [heq]
      apply (measurable_pi_apply i).sub
      apply Finset.measurable_sum
      intro k hk
      have hgi := ih k (Finset.mem_Iio.mp hk)
      exact ((hgi.inner (measurable_pi_apply i)).div (hgi.norm.pow_const 2)).smul hgi

@[fun_prop] theorem measurable_gramSchmidtNormed_fin (d n : ℕ) :
    Measurable (fun v : Fin n → Point d => InnerProductSpace.gramSchmidtNormed ℝ v) := by
  apply measurable_pi_iff.mpr
  intro i
  have hgi := measurable_gramSchmidt_fin d n i
  exact hgi.norm.inv.smul hgi

/-- The observed span residual uses the existing frame residual with the
totalized normalized Gram--Schmidt list (zero entries are retained). -/
def observedResidual {d n : ℕ} (v : Fin n → Point d) (x : Point d) : Point d :=
  frameResidual (InnerProductSpace.gramSchmidtNormed ℝ v) x

@[fun_prop] theorem measurable_observedResidual (d n : ℕ) :
    Measurable (fun p : (Fin n → Point d) × Point d => observedResidual p.1 p.2) := by
  have hv : Measurable (fun p : (Fin n → Point d) × Point d =>
      InnerProductSpace.gramSchmidtNormed ℝ p.1) :=
    (measurable_gramSchmidtNormed_fin d n).comp measurable_fst
  unfold observedResidual frameResidual
  fun_prop

theorem observedResidual_mem_orthogonal {d n : ℕ}
    (v : Fin n → Point d) (x : Point d) :
    observedResidual v x ∈ (Submodule.span ℝ (Set.range v))ᗮ := by
  classical
  let b := InnerProductSpace.gramSchmidtNormed ℝ v
  have hspan : Submodule.span ℝ (Set.range b) = Submodule.span ℝ (Set.range v) :=
    (InnerProductSpace.span_gramSchmidtNormed_range (𝕜 := ℝ) v).trans
      (InnerProductSpace.span_gramSchmidt ℝ v)
  have hpair : ∀ i k : Fin n, i ≠ k → inner ℝ (b i) (b k) = 0 := by
    intro i k hik
    simp [b, InnerProductSpace.gramSchmidtNormed, real_inner_smul_left,
      real_inner_smul_right, InnerProductSpace.gramSchmidt_orthogonal ℝ v hik]
  have hinner (i : Fin n) : inner ℝ (b i) (observedResidual v x) = 0 := by
    by_cases hi : b i = 0
    · simp [hi]
    have hnorm : ‖b i‖ = 1 := InnerProductSpace.gramSchmidtNormed_unit_length' hi
    have hself : inner ℝ (b i) (b i) = 1 := by
      rw [real_inner_self_eq_norm_sq, hnorm]
      norm_num
    change inner ℝ (b i) (frameResidual b x) = 0
    simp only [frameResidual, inner_sub_right, inner_sum, real_inner_smul_right]
    rw [Finset.sum_eq_single i]
    · rw [hself]
      ring
    · intro k _ hki
      rw [hpair i k hki.symm]
      ring
    · simp
  rw [← hspan]
  have hle : Submodule.span ℝ (Set.range b) ≤ (innerSL ℝ (observedResidual v x)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change inner ℝ (observedResidual v x) (b i) = 0
    rw [real_inner_comm]
    exact hinner i
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro y hy
  exact hle hy

theorem observedResidual_eq_starProjection {d n : ℕ}
    (v : Fin n → Point d) (x : Point d) :
    observedResidual v x = ((Submodule.span ℝ (Set.range v))ᗮ).starProjection x := by
  classical
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (observedResidual_mem_orthogonal v x)
  intro y hy
  have hspan : Submodule.span ℝ
      (Set.range (InnerProductSpace.gramSchmidtNormed ℝ v)) =
      Submodule.span ℝ (Set.range v) :=
    (InnerProductSpace.span_gramSchmidtNormed_range (𝕜 := ℝ) v).trans
      (InnerProductSpace.span_gramSchmidt ℝ v)
  have hsum : x - observedResidual v x ∈ Submodule.span ℝ (Set.range v) := by
    simp only [observedResidual, frameResidual, sub_sub_cancel]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  exact Submodule.inner_right_of_mem_orthogonal hsum hy

/-- Total Householder reflection: zero normal gives the identity. -/
def householder {d : ℕ} (w : Point d) : Point d ≃ₗᵢ[ℝ] Point d :=
  (Submodule.span ℝ ({w} : Set (Point d)))ᗮ.reflection

theorem householder_apply {d : ℕ} (w x : Point d) :
    householder w x = x - (2 : ℝ) • ((inner ℝ w x / ‖w‖ ^ 2) • w) := by
  rw [householder, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [neg_sub, smul_smul]
  module

@[fun_prop] theorem measurable_householder_apply (d : ℕ) :
    Measurable (fun p : Point d × Point d => householder p.1 p.2) := by
  simp only [householder_apply]
  fun_prop

theorem householder_observedResidual_fixed {d n : ℕ}
    (v : Fin n → Point d) (r x : Point d)
    (hx : x ∈ Submodule.span ℝ (Set.range v)) :
    householder (observedResidual v r) x = x := by
  have hw := observedResidual_mem_orthogonal v r
  have hi : inner ℝ (observedResidual v r) x = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hx hw
  simp [householder_apply, hi]

section MeasurableReflection

attribute [local irreducible] householder observedResidual

/-- A fixed ambient vector selects a measurable reflection section in the
complement of a varying finite observation span. -/
theorem measurable_observedReflection_frameAction (d n T : ℕ) (r : Point d) :
    Measurable (fun p : (Fin n → Point d) × (Fin T → Point d) =>
      frameAction (householder (observedResidual p.1 r)) p.2) := by
  have hpair : Measurable (fun p : (Fin n → Point d) × (Fin T → Point d) => (p.1, r)) :=
    measurable_fst.prodMk measurable_const
  have hr : Measurable
      (fun p : (Fin n → Point d) × (Fin T → Point d) => observedResidual p.1 r) :=
    (measurable_observedResidual d n).comp hpair
  have haction : Measurable (fun p : Point d × (Fin T → Point d) =>
      frameAction (householder p.1) p.2) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_householder_apply d).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact haction.comp (hr.prodMk measurable_snd)

end MeasurableReflection

/-- The exact joint-law arrow needed at one predictable measurement stage.
The transformation is allowed to depend on the *old* record. Its section
must preserve the actual old frame kernel, and the new measurement must be
invariant globally on that section. This is stronger than saying that a
single realized observation fiber is invariant.

This supporting probability lemma does not identify the old frame kernel
for the Bernoulli experiment, and is not a claimed randomized lift. -/
theorem predictable_observation_joint_invariance
    {A F Z : Type*} [MeasurableSpace A] [MeasurableSpace F]
    [MeasurableSpace Z] (q : Measure A) [IsProbabilityMeasure q]
    (κ : Kernel A F) [IsMarkovKernel κ]
    (B : A × F → Z) (hB : Measurable B)
    (rotate : A × F → F) (hrotate : Measurable rotate)
    (hpreserve : ∀ᵐ a ∂q, (κ a).map (fun u => rotate (a, u)) = κ a)
    (hobserve : ∀ a : A, ∀ u : F, B (a, rotate (a, u)) = B (a, u)) :
    (q ⊗ₘ κ).map (fun p : A × F => ((p.1, B p), rotate p)) =
      (q ⊗ₘ κ).map (fun p : A × F => ((p.1, B p), p.2)) := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hleft : Measurable (fun p : A × F => ((p.1, B p), rotate p)) :=
    (measurable_fst.prodMk hB).prodMk hrotate
  have hright : Measurable (fun p : A × F => ((p.1, B p), p.2)) :=
    (measurable_fst.prodMk hB).prodMk measurable_snd
  have hφleft : Measurable (fun p : A × F => φ ((p.1, B p), rotate p)) :=
    hφ.comp hleft
  have hφright : Measurable (fun p : A × F => φ ((p.1, B p), p.2)) :=
    hφ.comp hright
  rw [lintegral_map hφ hleft, lintegral_map hφ hright,
    Measure.lintegral_compProd hφleft,
    Measure.lintegral_compProd hφright]
  apply lintegral_congr_ae
  filter_upwards [hpreserve] with a hpa
  have hf : Measurable (fun u : F => φ ((a, B (a, u)), u)) :=
    hφ.comp ((measurable_const.prodMk
      (hB.comp (measurable_const.prodMk measurable_id))).prodMk measurable_id)
  have hr : Measurable (fun u : F => rotate (a, u)) :=
    hrotate.comp (measurable_const.prodMk measurable_id)
  have hi := lintegral_map (μ := κ a) hf hr
  rw [hpa] at hi
  simpa only [hobserve] using hi.symm

/-- A measurable old-record-dependent symmetry of the actual previous
kernel is inherited by the *actual* regular conditional distribution after
the new measurement. The RCD is mathlib's condDistrib of the concrete
composition-product experiment; no candidate posterior law is assumed. -/
theorem predictable_observation_condDistrib_invariance
    {A F Z : Type*} [MeasurableSpace A] [MeasurableSpace F]
    [MeasurableSpace Z] [StandardBorelSpace F] [Nonempty F]
    (q : Measure A) [IsProbabilityMeasure q]
    (κ : Kernel A F) [IsMarkovKernel κ]
    (B : A × F → Z) (hB : Measurable B)
    (rotate : A × F → F) (hrotate : Measurable rotate)
    (hpreserve : ∀ᵐ a ∂q, (κ a).map (fun u => rotate (a, u)) = κ a)
    (hobserve : ∀ a : A, ∀ u : F, B (a, rotate (a, u)) = B (a, u)) :
    let P := q ⊗ₘ κ
    let X : A × F → A × Z := fun p => (p.1, B p)
    let η := condDistrib Prod.snd X P
    let f : (A × Z) × F → F := fun p => rotate (p.1.1, p.2)
    ((Kernel.prod (Kernel.deterministic (id : A × Z → A × Z) measurable_id) η).map f)
      =ᵐ[P.map X] η := by
  let P := q ⊗ₘ κ
  let X : A × F → A × Z := fun p => (p.1, B p)
  let η := condDistrib Prod.snd X P
  let f : (A × Z) × F → F := fun p => rotate (p.1.1, p.2)
  have hX : Measurable X := measurable_fst.prodMk hB
  have hf : Measurable f :=
    hrotate.comp (measurable_fst.fst.prodMk measurable_snd)
  have hη : HasCondDistrib Prod.snd X η P := by
    refine ⟨(hX.prodMk measurable_snd).aemeasurable, ?_⟩
    exact (compProd_map_condDistrib hX.aemeasurable measurable_snd.aemeasurable).symm
  have hrot := hasCondDistrib_joint_map P X Prod.snd hX measurable_snd η hη f hf
  have hjoint := predictable_observation_joint_invariance q κ B hB rotate hrotate
    hpreserve hobserve
  apply Kernel.ae_eq_of_compProd_eq
  calc
    _ = P.map (fun p : A × F => (X p, f (X p, p.2))) := hrot.map_eq.symm
    _ = P.map (fun p : A × F => (X p, p.2)) := hjoint
    _ = _ := hη.map_eq

/-- A rotation fixes the first n columns pointwise; n may exceed T. -/
def FixesPrefix {d T : ℕ} (W : Point d ≃ₗᵢ[ℝ] Point d)
    (U : Fin T → Point d) (n : ℕ) : Prop :=
  ∀ i : Fin T, i.val < n → W (U i) = U i

theorem FixesPrefix.mono {d T n m : ℕ}
    {W : Point d ≃ₗᵢ[ℝ] Point d} {U : Fin T → Point d}
    (h : FixesPrefix W U m) (hn : n ≤ m) : FixesPrefix W U n := by
  intro i hi
  exact h i (hi.trans_le hn)

theorem softProjection_fixed_of_fixed {d : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (R : ℝ) (x : Point d)
    (hx : W x = x) : W (softProjection R x) = softProjection R x := by
  simp [softProjection, hx]

/-- All coordinates, including those of hidden columns, are unchanged
when the bounded query is fixed. -/
theorem coordinates_frameAction_of_fixed {d T : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (U : Fin T → Point d)
    (R : ℝ) (x : Point d) (hx : W x = x) :
    coordinates (frameAction W U) R x = coordinates U R x := by
  ext i
  change inner ℝ (W (U i)) (softProjection R x) =
    inner ℝ (U i) (softProjection R x)
  calc
    _ = inner ℝ (W (U i)) (W (softProjection R x)) := by
      rw [softProjection_fixed_of_fixed W R x hx]
    _ = _ := W.inner_map_map _ _

theorem frameEmbed_frameAction {d T : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (U : Fin T → Point d) (z : Point T) :
    frameEmbed (frameAction W U) z = W (frameEmbed U z) := by
  simp [frameEmbed_apply, frameAction, map_sum]

theorem frameEmbed_frameAction_eq_of_support {d T n : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (U : Fin T → Point d) (z : Point T)
    (hfix : FixesPrefix W U n) (hsupport : ∀ i : Fin T, n ≤ i.val → z i = 0) :
    frameEmbed (frameAction W U) z = frameEmbed U z := by
  simp only [frameEmbed_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < n
  · simp only [frameAction, hfix i hi]
  · simp [hsupport i (Nat.le_of_not_gt hi)]

/-- This uses the literal Basic.response formula, not a surrogate oracle.
The coefficients can depend on every hidden projection of the fixed query. -/
theorem response_frameAction_eq_of_support {d T n : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (U : Fin T → Point d)
    (R η : ℝ) (θ : unitInterval) (x : Point d) (D : Bool)
    (hx : W x = x) (hfix : FixesPrefix W U n)
    (hsupport : ∀ i : Fin T, n ≤ i.val →
      Fradin.bernoulliResponse θ (coordinates U R x) D i = 0) :
    response (frameAction W U) R η θ x D = response U R η θ x D := by
  simp only [response, transport, ContinuousLinearMap.comp_apply]
  rw [coordinates_frameAction_of_fixed W U R x hx,
    frameEmbed_frameAction_eq_of_support W U _ hfix hsupport]

/-- The global D=false event reveals no column after the current frontier. -/
theorem response_false_frameAction_eq_of_small_suffix {d T n : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (U : Fin T → Point d)
    (R η : ℝ) (θ : unitInterval) (x : Point d)
    (hx : W x = x) (hfix : FixesPrefix W U n)
    (hsmall : ∀ i : Fin T, n ≤ i.val → |coordinates U R x i| ≤ 1 / 4) :
    response (frameAction W U) R η θ x false = response U R η θ x false := by
  apply response_frameAction_eq_of_support W U R η θ x false hx hfix
  exact Fradin.bernoulliResponse_false_frontier_zero θ (coordinates U R x) hsmall

/-- For either seed, at most the next column can enter the response. -/
theorem response_frameAction_eq_of_small_suffix {d T n : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (U : Fin T → Point d)
    (R η : ℝ) (θ : unitInterval) (x : Point d) (D : Bool)
    (hx : W x = x) (hfix : FixesPrefix W U (n + 1))
    (hsmall : ∀ i : Fin T, n ≤ i.val → |coordinates U R x i| ≤ 1 / 4) :
    response (frameAction W U) R η θ x D = response U R η θ x D := by
  apply response_frameAction_eq_of_support W U R η θ x D hx hfix
  intro i hi
  exact Fradin.bernoulliResponse_tail_zero θ (coordinates U R x)
    (fun k hk => (hsmall k hk).trans (by norm_num)) i hi D

/-- Equality only on the original path suffices. A has arbitrary private
measurable space and full (query,response) history; no zero-respecting or
span restriction is imposed on its decision rules. -/
theorem runTranscript_eq_of_responses_on_path
    {d N n : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O O' : GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (r : Private) (seeds : Fin n → Seed)
    (hpath : ∀ t : ℕ, ∀ ht : t < n,
      let oldSeeds : Fin t → Seed := fun i => seeds ⟨i.val, i.isLt.trans ht⟩
      let history := runTranscript O A r t oldSeeds
      O'.response (A.decide t r history) (seeds ⟨t, ht⟩) =
        O.response (A.decide t r history) (seeds ⟨t, ht⟩)) :
    runTranscript O' A r n seeds = runTranscript O A r n seeds := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let seedPrefix : Fin n → Seed := fun i => seeds i.castSucc
    have hp : runTranscript O' A r n seedPrefix = runTranscript O A r n seedPrefix := by
      apply ih seedPrefix
      intro t ht
      simpa [seedPrefix] using hpath t (ht.trans (Nat.lt_succ_self n))
    simp only [runTranscript]
    change Fin.snoc (α := fun _ : Fin (n + 1) => Point d × Point d) (runTranscript O' A r n seedPrefix)
        (A.decide n r (runTranscript O' A r n seedPrefix),
          O'.response (A.decide n r (runTranscript O' A r n seedPrefix))
            (seeds (Fin.last n))) =
      Fin.snoc (α := fun _ : Fin (n + 1) => Point d × Point d) (runTranscript O A r n seedPrefix)
        (A.decide n r (runTranscript O A r n seedPrefix),
          O.response (A.decide n r (runTranscript O A r n seedPrefix))
            (seeds (Fin.last n)))
    rw [hp]
    have hlast := hpath n (Nat.lt_succ_self n)
    have htail : (fun i : Fin n => seeds ⟨i.val, i.isLt.trans (Nat.lt_succ_self n)⟩) =
        seedPrefix := by
      funext i
      apply congrArg seeds
      apply Fin.ext
      rfl
    dsimp only at hlast
    rw [htail] at hlast
    exact congrArg
      (fun y : Point d => Fin.snoc (α := fun _ : Fin (n + 1) => Point d × Point d)
        (runTranscript O A r n seedPrefix)
        (A.decide n r (runTranscript O A r n seedPrefix), y)) hlast

/-- The response-free output inherits the same pathwise invariance. -/
theorem output_eq_of_transcript_eq
    {d N : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O O' : GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (r : Private) (seeds : Fin N → Seed)
    (h : runTranscript O' A r N seeds = runTranscript O A r N seeds) :
    A.output r (runTranscript O' A r N seeds) =
      A.output r (runTranscript O A r N seeds) := by rw [h]

/-- Concrete fixed-seed transcript symmetry. The support hypotheses refer
to the actual Bernoulli coefficients of the original path. They impose no
restriction on A and do not assert a conditional distribution. -/
theorem runTranscript_frameAction_of_support
    {d T N n m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (W : Point d ≃ₗᵢ[ℝ] Point d) (U : Fin T → Point d)
    {R : ℝ} (hR : 0 < R) (η : ℝ) (θ : unitInterval)
    (A : RandomAlgorithm d N Private) (r : Private) (seeds : Fin n → Bool)
    (hfix : FixesPrefix W U m)
    (hqueries : ∀ t : ℕ, ∀ ht : t < n,
      let oldSeeds : Fin t → Bool := fun i => seeds ⟨i.val, i.isLt.trans ht⟩
      let history := runTranscript (oracle U hR η θ) A r t oldSeeds
      W (A.decide t r history) = A.decide t r history)
    (hsupport : ∀ t : ℕ, ∀ ht : t < n,
      let oldSeeds : Fin t → Bool := fun i => seeds ⟨i.val, i.isLt.trans ht⟩
      let history := runTranscript (oracle U hR η θ) A r t oldSeeds
      ∀ i : Fin T, m ≤ i.val →
        Fradin.bernoulliResponse θ (coordinates U R (A.decide t r history))
          (seeds ⟨t, ht⟩) i = 0) :
    runTranscript (oracle (frameAction W U) hR η θ) A r n seeds =
      runTranscript (oracle U hR η θ) A r n seeds := by
  apply runTranscript_eq_of_responses_on_path
  intro t ht
  exact response_frameAction_eq_of_support W U R η θ _ _
    (hqueries t ht) hfix (hsupport t ht)

end HeavyTailedNoise.RandomizedLift
