import HeavyTailedNoise.Probability.HaarDirection

/-!
Sequential projected-Gaussian frame kernels and their conditional laws.
The output space of every kernel is the fixed ambient Euclidean space; no
measurable choice of a basis for a variable orthogonal complement is made.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Pointwise

noncomputable section

namespace HeavyTailedNoise

/-- Remove the components along a proposed prefix.  For an orthonormal
prefix this is the orthogonal projection onto its complement. -/
def frameResidual {d j : ℕ} (v : Fin j → Point d) (z : Point d) : Point d :=
  z - ∑ i : Fin j, inner ℝ (v i) z • v i

/-- Totalized direction map for the residual.  It is zero on the degenerate
residual event, which has Gaussian probability zero for valid short prefixes. -/
def frameNextDirection {d j : ℕ} (v : Fin j → Point d) (z : Point d) : Point d :=
  gaussianDirection (frameResidual v z)

lemma measurable_frameNextDirection (d j : ℕ) :
    Measurable (fun p : (Fin j → Point d) × Point d =>
      frameNextDirection p.1 p.2) := by
  unfold frameNextDirection gaussianDirection frameResidual
  fun_prop

lemma measurable_frameNextDirection_fixed {d j : ℕ}
    (v : Fin j → Point d) :
    Measurable (frameNextDirection v) := by
  simpa [Function.comp_def] using
    (measurable_frameNextDirection d j).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun z : Point d => (v, z)))

/-- A jointly measurable transition law, defined even on invalid prefixes. -/
def frameNextKernel (d j : ℕ) :
    Kernel (Fin j → Point d) (Point d) :=
  (((Kernel.id : Kernel (Fin j → Point d) (Fin j → Point d)) ×ₖ
    Kernel.const (Fin j → Point d) (stdGaussian (Point d))).map
      (fun p => frameNextDirection p.1 p.2))

instance (d j : ℕ) : IsMarkovKernel (frameNextKernel d j) := by
  unfold frameNextKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_frameNextDirection d j)

lemma frameNextKernel_apply (d j : ℕ) (v : Fin j → Point d) :
    frameNextKernel d j v =
      (stdGaussian (Point d)).map (frameNextDirection v) := by
  apply Measure.ext
  intro s hs
  rw [frameNextKernel, Kernel.map_apply' _
    (measurable_frameNextDirection d j) v hs]
  rw [Kernel.id_prod_apply' _ v
    (hs.preimage (measurable_frameNextDirection d j))]
  rw [Measure.map_apply (measurable_frameNextDirection_fixed v) hs]
  simp only [Kernel.const_apply]
  rfl

/-- Drawing an independent ambient Gaussian after a fixed prefix measure
realizes the explicit next-direction kernel. -/
lemma frameNext_jointLaw (d j : ℕ)
    (q : Measure (Fin j → Point d)) [IsProbabilityMeasure q] :
    (q.prod (stdGaussian (Point d))).map
      (fun p => (p.1, frameNextDirection p.1 p.2)) =
      q ⊗ₘ frameNextKernel d j := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hmap : Measurable
      (fun p : (Fin j → Point d) × Point d =>
        (p.1, frameNextDirection p.1 p.2)) :=
    measurable_fst.prodMk (measurable_frameNextDirection d j)
  rw [lintegral_map hφ hmap]
  rw [lintegral_prod
    (fun p => φ (p.1, frameNextDirection p.1 p.2))
    (hφ.comp hmap).aemeasurable]
  rw [Measure.lintegral_compProd hφ]
  apply lintegral_congr
  intro v
  rw [frameNextKernel_apply]
  change
    (∫⁻ z : Point d,
      φ (v, frameNextDirection v z) ∂stdGaussian (Point d)) =
    ∫⁻ y : Point d, φ (v, y) ∂
      (stdGaussian (Point d)).map (frameNextDirection v)
  exact (lintegral_map (μ := stdGaussian (Point d))
    (f := fun y : Point d => φ (v, y))
    (g := frameNextDirection v)
    (hφ.comp (measurable_const.prodMk measurable_id))
    (measurable_frameNextDirection_fixed v)).symm

/-- The product construction gives a genuine conditional distribution, not
only a pointwise formula for the kernel. -/
theorem frameNext_hasCondDistrib (d j : ℕ)
    (q : Measure (Fin j → Point d)) [IsProbabilityMeasure q] :
    HasCondDistrib
      (fun p : (Fin j → Point d) × Point d =>
        frameNextDirection p.1 p.2)
      Prod.fst (frameNextKernel d j)
      (q.prod (stdGaussian (Point d))) := by
  refine ⟨(measurable_fst.prodMk
    (measurable_frameNextDirection d j)).aemeasurable, ?_⟩
  change
    (q.prod (stdGaussian (Point d))).map
      (fun p => (p.1, frameNextDirection p.1 p.2)) =
    ((q.prod (stdGaussian (Point d))).map Prod.fst) ⊗ₘ
      frameNextKernel d j
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact frameNext_jointLaw d j q

/-- The first column is the exact normalized surface measure supplied by
HaarDirection, including the two-point sphere when d=1. -/
theorem frameNextKernel_zero_eq_toSphere (d : ℕ) (hd : 0 < d)
    (v : Fin 0 → Point d) :
    frameNextKernel d 0 v =
      (((volume : Measure (Point d)).toSphere Set.univ)⁻¹ •
        ((volume : Measure (Point d)).toSphere)).map
          (Subtype.val :
            Metric.sphere (0 : Point d) 1 → Point d) := by
  rw [frameNextKernel_apply]
  have hfun : frameNextDirection v = gaussianDirection (m := d) := by
    funext z
    simp [frameNextDirection, frameResidual]
  rw [hfun]
  exact stdGaussian_direction_eq_normalized_toSphere d hd

/-- Appending an independent tape to a state/response law preserves the
transition kernel.  This concerns the *final state law*: it makes no claim
that a tape independent of the frame is independent of the raw Gaussians
used to construct that frame. -/
theorem compProd_independent_tape
    {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace Z] (q : Measure A) [IsProbabilityMeasure q]
    (κ : Kernel A B) [IsMarkovKernel κ]
    (ρ : Measure Z) [IsProbabilityMeasure ρ] :
    ((q ⊗ₘ κ).prod ρ).map
      (fun p : (A × B) × Z => ((p.1.1, p.2), p.1.2)) =
      (q.prod ρ) ⊗ₘ (κ.comap Prod.fst measurable_fst) := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hF : Measurable
      (fun p : (A × B) × Z => ((p.1.1, p.2), p.1.2)) := by
    fun_prop
  rw [lintegral_map hφ hF]
  rw [lintegral_prod
    (fun p : (A × B) × Z => φ ((p.1.1, p.2), p.1.2))
    (hφ.comp hF).aemeasurable]
  rw [Measure.lintegral_compProd (by fun_prop)]
  rw [Measure.lintegral_compProd hφ]
  simp_rw [Kernel.comap_apply]
  have hκZ : Measurable
      (fun p : A × Z => ∫⁻ b, φ (p, b) ∂κ p.1) := by
    simpa [Kernel.comap_apply] using
      (hφ.lintegral_kernel_prod_right'
        (κ := κ.comap Prod.fst measurable_fst))
  rw [lintegral_prod
    (fun p : A × Z => ∫⁻ b, φ (p, b) ∂κ p.1)
    hκZ.aemeasurable]
  apply lintegral_congr
  intro a
  exact lintegral_lintegral_swap (by fun_prop :
    AEMeasurable
      (fun p : B × Z => φ ((a, p.2), p.1))
      ((κ a).prod ρ))

/-- On a product realization, adding an independent tape to the conditioning
data leaves the conditional response law unchanged.  The tape's measurable
space is arbitrary. -/
theorem hasCondDistrib_product_tape
    {Ω A B Z : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → A) (Y : Ω → B)
    (hV : Measurable V) (hY : Measurable Y)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (hcond : HasCondDistrib Y V κ P)
    (ρ : Measure Z) [IsProbabilityMeasure ρ] :
    HasCondDistrib
      (fun p : Ω × Z => Y p.1)
      (fun p : Ω × Z => (V p.1, p.2))
      (κ.comap (Prod.fst : A × Z → A)
        (measurable_fst : Measurable (Prod.fst : A × Z → A)))
      (P.prod ρ) := by
  have hVY : Measurable (fun ω : Ω => (V ω, Y ω)) := hV.prodMk hY
  have hG : Measurable
      (fun p : Ω × Z => ((V p.1, Y p.1), p.2)) :=
    (hVY.comp measurable_fst).prodMk measurable_snd
  have hX : Measurable
      (fun p : Ω × Z => (V p.1, p.2)) :=
    (hV.comp measurable_fst).prodMk measurable_snd
  have hP1 :
      (P.prod ρ).map
        (fun p : Ω × Z => ((V p.1, Y p.1), p.2)) =
      (P.map (fun ω => (V ω, Y ω))).prod ρ := by
    have hfun :
        Prod.map (fun ω : Ω => (V ω, Y ω)) (id : Z → Z) =
          (fun p : Ω × Z => ((V p.1, Y p.1), p.2)) := by
      funext p
      cases p
      rfl
    simpa only [hfun, Measure.map_id] using
      (Measure.map_prod_map P ρ hVY measurable_id).symm
  have hP2 :
      (P.prod ρ).map
        (fun p : Ω × Z => (V p.1, p.2)) =
      (P.map V).prod ρ := by
    have hfun :
        Prod.map V (id : Z → Z) =
          (fun p : Ω × Z => (V p.1, p.2)) := by
      funext p
      cases p
      rfl
    simpa only [hfun, Measure.map_id] using
      (Measure.map_prod_map P ρ hV measurable_id).symm
  refine ⟨(hX.prodMk (hY.comp measurable_fst)).aemeasurable, ?_⟩
  change
    (P.prod ρ).map
      (fun p : Ω × Z => ((V p.1, p.2), Y p.1)) =
    ((P.prod ρ).map (fun p : Ω × Z => (V p.1, p.2))) ⊗ₘ
      (κ.comap (Prod.fst : A × Z → A)
        (measurable_fst : Measurable (Prod.fst : A × Z → A)))
  calc
    _ = ((P.prod ρ).map
          (fun p : Ω × Z => ((V p.1, Y p.1), p.2))).map
            (fun p : (A × B) × Z => ((p.1.1, p.2), p.1.2)) := by
          rw [Measure.map_map (by fun_prop) hG]
          rfl
    _ = ((P.map (fun ω => (V ω, Y ω))).prod ρ).map
          (fun p : (A × B) × Z => ((p.1.1, p.2), p.1.2)) := by
          rw [hP1]
    _ = (((P.map V) ⊗ₘ κ).prod ρ).map
          (fun p : (A × B) × Z => ((p.1.1, p.2), p.1.2)) := by
          rw [hcond.map_eq]
    _ = ((P.map V).prod ρ) ⊗ₘ
          (κ.comap (Prod.fst : A × Z → A)
            (measurable_fst : Measurable (Prod.fst : A × Z → A))) :=
          compProd_independent_tape (P.map V) κ ρ
    _ = ((P.prod ρ).map
          (fun p : Ω × Z => (V p.1, p.2))) ⊗ₘ
          (κ.comap (Prod.fst : A × Z → A)
            (measurable_fst : Measurable (Prod.fst : A × Z → A))) := by rw [hP2]

private theorem hasCondDistrib_pullback
    {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω') (Q : Measure Ω)
    (g : Ω' → Ω) (hg : Measurable g) (hmap : P.map g = Q)
    (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y)
    (κ : Kernel A B) (h : HasCondDistrib Y X κ Q) :
    HasCondDistrib (Y ∘ g) (X ∘ g) κ P := by
  refine ⟨((hX.comp hg).prodMk (hY.comp hg)).aemeasurable, ?_⟩
  change
    P.map (fun ω => (X (g ω), Y (g ω))) =
      (P.map (X ∘ g)) ⊗ₘ κ
  calc
    _ = (P.map g).map (fun ω => (X ω, Y ω)) := by
          rw [Measure.map_map (hX.prodMk hY) hg]
          rfl
    _ = Q.map (fun ω => (X ω, Y ω)) := by rw [hmap]
    _ = (Q.map X) ⊗ₘ κ := h.map_eq
    _ = ((P.map g).map X) ⊗ₘ κ := by rw [hmap]
    _ = (P.map (X ∘ g)) ⊗ₘ κ := by
          rw [Measure.map_map hX hg]

/-- The private tape need only be independent of the final frame/state U.
No independence from any raw variables used to construct U is assumed. -/
theorem hasCondDistrib_independent_tape
    {Ω F A B Z : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → F) (Zvar : Ω → Z)
    (hU : Measurable U) (hZ : Measurable Zvar)
    (hInd : U ⟂ᵢ[P] Zvar)
    (V : F → A) (Y : F → B)
    (hV : Measurable V) (hY : Measurable Y)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (hFrame : HasCondDistrib Y V κ (P.map U)) :
    HasCondDistrib
      (fun ω => Y (U ω))
      (fun ω => (V (U ω), Zvar ω))
      (κ.comap (Prod.fst : A × Z → A)
        (measurable_fst : Measurable (Prod.fst : A × Z → A)))
      P := by
  let Q : Measure F := P.map U
  let ρ : Measure Z := P.map Zvar
  have hPair :
      P.map (fun ω => (U ω, Zvar ω)) = Q.prod ρ := by
    exact hInd.map_prod_eq_prod_map_map hU.aemeasurable hZ.aemeasurable
  have hProd :
      HasCondDistrib
        (fun p : F × Z => Y p.1)
        (fun p : F × Z => (V p.1, p.2))
        (κ.comap (Prod.fst : A × Z → A)
          (measurable_fst : Measurable (Prod.fst : A × Z → A)))
        (Q.prod ρ) :=
    hasCondDistrib_product_tape Q V Y hV hY κ hFrame ρ
  have h := hasCondDistrib_pullback P (Q.prod ρ)
    (fun ω => (U ω, Zvar ω)) (hU.prodMk hZ) hPair
    (fun p : F × Z => (V p.1, p.2))
    (fun p : F × Z => Y p.1)
    ((hV.comp measurable_fst).prodMk measurable_snd)
    (hY.comp measurable_fst)
    (κ.comap (Prod.fst : A × Z → A)
      (measurable_fst : Measurable (Prod.fst : A × Z → A)))
    hProd
  simpa [Function.comp_def] using h

/-- Any measurable history computed from the revealed prefix and an
independent tape may be added to the conditioning data.  A stopped
pre-response history is an instance once its concrete factorization through
that prefix and tape has been proved. -/
theorem hasCondDistrib_independent_history
    {Ω F A B Z H : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → F) (Zvar : Ω → Z)
    (hU : Measurable U) (hZ : Measurable Zvar)
    (hInd : U ⟂ᵢ[P] Zvar)
    (V : F → A) (Y : F → B)
    (hV : Measurable V) (hY : Measurable Y)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (hFrame : HasCondDistrib Y V κ (P.map U))
    (history : A × Z → H) (hh : Measurable history) :
    HasCondDistrib
      (fun ω => Y (U ω))
      (fun ω => (V (U ω), history (V (U ω), Zvar ω)))
      (κ.comap (Prod.fst : A × H → A)
        (measurable_fst : Measurable (Prod.fst : A × H → A)))
      P := by
  let f : A × Z → A × H := fun p => (p.1, history p)
  have hf : Measurable f := measurable_fst.prodMk hh
  let κH : Kernel (A × H) B :=
    κ.comap (Prod.fst : A × H → A)
      (measurable_fst : Measurable (Prod.fst : A × H → A))
  have hK :
      κH.comap f hf =
        κ.comap (Prod.fst : A × Z → A)
          (measurable_fst : Measurable (Prod.fst : A × Z → A)) := by
    ext p s hs
    simp [κH, f, Kernel.comap_apply]
  have hbase := hasCondDistrib_independent_tape
    P U Zvar hU hZ hInd V Y hV hY κ hFrame
  have hlarge :
      HasCondDistrib
        (fun ω => Y (U ω))
        (fun ω => (V (U ω), Zvar ω))
        (κH.comap f hf) P := by
    simpa only [hK] using hbase
  have hsmall := HasCondDistrib.comp_right hlarge
  simpa [f, κH, Function.comp_def] using hsmall

/-- Contract for a concrete stopped pre-response history.  The substantive
application obligation is to prove the factorization for the ideal process,
including its value on paths where the stage never starts. -/
theorem hasCondDistrib_history_of_factorization
    {Ω F A B Z H : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    [MeasurableSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → F) (Zvar : Ω → Z)
    (hU : Measurable U) (hZ : Measurable Zvar)
    (hInd : U ⟂ᵢ[P] Zvar)
    (V : F → A) (Y : F → B)
    (hV : Measurable V) (hY : Measurable Y)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (hFrame : HasCondDistrib Y V κ (P.map U))
    (history : Ω → H) (factor : A × Z → H)
    (hfactorMeas : Measurable factor)
    (hfactor : ∀ ω, history ω = factor (V (U ω), Zvar ω)) :
    HasCondDistrib
      (fun ω => Y (U ω))
      (fun ω => (V (U ω), history ω))
      (κ.comap (Prod.fst : A × H → A)
        (measurable_fst : Measurable (Prod.fst : A × H → A)))
      P := by
  simpa only [hfactor] using
    (hasCondDistrib_independent_history P U Zvar hU hZ hInd
      V Y hV hY κ hFrame factor hfactorMeas)

lemma measurable_frameSnoc (d j : ℕ) :
    Measurable
      (fun p : (Fin j → Point d) × Point d =>
        Fin.snoc (α := fun _ : Fin (j + 1) => Point d) p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      ((measurable_pi_apply k).comp
        (measurable_fst :
          Measurable (Prod.fst :
            (Fin j → Point d) × Point d → (Fin j → Point d))))
  · simpa only [Fin.snoc_last] using
      (measurable_snd :
        Measurable (Prod.snd :
          (Fin j → Point d) × Point d → Point d))

/-- A single law selected from d and T, obtained by successively sampling
the projected-Gaussian transition kernels.  Its orthonormal support and
intrinsic sphere law at every valid prefix are separate geometric obligations. -/
def preselectedProjectedGaussianLaw (d : ℕ) :
    (T : ℕ) → Measure (Fin T → Point d)
  | 0 => Measure.dirac (fun i : Fin 0 => Fin.elim0 i)
  | T + 1 =>
      ((preselectedProjectedGaussianLaw d T) ⊗ₘ
        frameNextKernel d T).map
          (fun p => Fin.snoc (α := fun _ : Fin (T + 1) => Point d) p.1 p.2)

theorem preselectedProjectedGaussianLaw_probability (d T : ℕ) :
    IsProbabilityMeasure (preselectedProjectedGaussianLaw d T) := by
  induction T with
  | zero =>
      change IsProbabilityMeasure
        (Measure.dirac (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Point d))
      infer_instance
  | succ T ih =>
      letI : IsProbabilityMeasure
        (preselectedProjectedGaussianLaw d T) := ih
      change IsProbabilityMeasure
        (((preselectedProjectedGaussianLaw d T) ⊗ₘ
          frameNextKernel d T).map
            (fun p => Fin.snoc (α := fun _ : Fin (T + 1) => Point d) p.1 p.2))
      infer_instance

/-- Removing the final column from the length-(T+1) law recovers the
composition-product of the length-T law and its next-direction kernel. -/
theorem preselectedProjectedGaussianLaw_step (d T : ℕ) :
    (preselectedProjectedGaussianLaw d (T + 1)).map
      (fun u => (Fin.init u, u (Fin.last T))) =
      (preselectedProjectedGaussianLaw d T) ⊗ₘ frameNextKernel d T := by
  have hInit : Measurable
      (fun u : Fin (T + 1) → Point d => Fin.init u) := by
    apply measurable_pi_iff.mpr
    intro i
    simpa [Fin.init] using
      (measurable_pi_apply i.castSucc :
        Measurable (fun u : Fin (T + 1) → Point d => u i.castSucc))
  have hPair : Measurable
      (fun u : Fin (T + 1) → Point d =>
        (Fin.init u, u (Fin.last T))) :=
    hInit.prodMk (measurable_pi_apply (Fin.last T))
  change
    (((preselectedProjectedGaussianLaw d T) ⊗ₘ
      frameNextKernel d T).map
        (fun p => Fin.snoc (α := fun _ : Fin (T + 1) => Point d) p.1 p.2)).map
          (fun u => (Fin.init u, u (Fin.last T))) =
    (preselectedProjectedGaussianLaw d T) ⊗ₘ frameNextKernel d T
  rw [Measure.map_map hPair (measurable_frameSnoc d T)]
  have hfun :
      (fun u : Fin (T + 1) → Point d =>
        (Fin.init u, u (Fin.last T))) ∘
          (fun p : (Fin T → Point d) × Point d =>
            Fin.snoc (α := fun _ : Fin (T + 1) => Point d) p.1 p.2) = id := by
    funext p
    rcases p with ⟨v, z⟩
    simp [Function.comp_def]
  rw [hfun, Measure.map_id]

theorem preselectedProjectedGaussianLaw_init (d T : ℕ) :
    (preselectedProjectedGaussianLaw d (T + 1)).map Fin.init =
      preselectedProjectedGaussianLaw d T := by
  have hInit : Measurable
      (fun u : Fin (T + 1) → Point d => Fin.init u) := by
    apply measurable_pi_iff.mpr
    intro i
    simpa [Fin.init] using
      (measurable_pi_apply i.castSucc :
        Measurable (fun u : Fin (T + 1) → Point d => u i.castSucc))
  have hPair : Measurable
      (fun u : Fin (T + 1) → Point d =>
        (Fin.init u, u (Fin.last T))) :=
    hInit.prodMk (measurable_pi_apply (Fin.last T))
  calc
    (preselectedProjectedGaussianLaw d (T + 1)).map Fin.init =
        ((preselectedProjectedGaussianLaw d (T + 1)).map
          (fun u => (Fin.init u, u (Fin.last T)))).map Prod.fst := by
            rw [Measure.map_map measurable_fst hPair]
            rfl
    _ = ((preselectedProjectedGaussianLaw d T) ⊗ₘ
          frameNextKernel d T).map Prod.fst := by
            rw [preselectedProjectedGaussianLaw_step]
    _ = preselectedProjectedGaussianLaw d T := by
          letI : IsProbabilityMeasure
            (preselectedProjectedGaussianLaw d T) :=
            preselectedProjectedGaussianLaw_probability d T
          simpa [Measure.fst] using
            (Measure.fst_compProd
              (preselectedProjectedGaussianLaw d T)
              (frameNextKernel d T))

theorem preselectedProjectedGaussianLaw_last_hasCondDistrib
    (d T : ℕ) :
    HasCondDistrib
      (fun u : Fin (T + 1) → Point d => u (Fin.last T))
      Fin.init (frameNextKernel d T)
      (preselectedProjectedGaussianLaw d (T + 1)) := by
  have hInit : Measurable
      (fun u : Fin (T + 1) → Point d => Fin.init u) := by
    apply measurable_pi_iff.mpr
    intro i
    simpa [Fin.init] using
      (measurable_pi_apply i.castSucc :
        Measurable (fun u : Fin (T + 1) → Point d => u i.castSucc))
  refine ⟨(hInit.prodMk
    (measurable_pi_apply (Fin.last T))).aemeasurable, ?_⟩
  change
    (preselectedProjectedGaussianLaw d (T + 1)).map
      (fun u => (Fin.init u, u (Fin.last T))) =
    ((preselectedProjectedGaussianLaw d (T + 1)).map Fin.init) ⊗ₘ
      frameNextKernel d T
  rw [preselectedProjectedGaussianLaw_init]
  exact preselectedProjectedGaussianLaw_step d T

/-- For the concrete preselected tuple law, any independent private tape and
any measurable history built from the revealed prefix and that tape preserve
the final-column transition kernel. -/
theorem preselectedProjectedGaussianLaw_last_independent_history
    {Ω Z H : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace H] (P : Measure Ω) [IsProbabilityMeasure P]
    (d T : ℕ)
    (U : Ω → (Fin (T + 1) → Point d)) (Zvar : Ω → Z)
    (hU : Measurable U) (hZ : Measurable Zvar)
    (hInd : U ⟂ᵢ[P] Zvar)
    (hLaw : P.map U = preselectedProjectedGaussianLaw d (T + 1))
    (history : (Fin T → Point d) × Z → H)
    (hh : Measurable history) :
    HasCondDistrib
      (fun ω => U ω (Fin.last T))
      (fun ω => (Fin.init (U ω),
        history (Fin.init (U ω), Zvar ω)))
      ((frameNextKernel d T).comap
        (Prod.fst : ((Fin T → Point d) × H) → (Fin T → Point d))
        (measurable_fst :
          Measurable (Prod.fst :
            ((Fin T → Point d) × H) → (Fin T → Point d))))
      P := by
  have hInit : Measurable
      (fun u : Fin (T + 1) → Point d => Fin.init u) := by
    apply measurable_pi_iff.mpr
    intro i
    simpa [Fin.init] using
      (measurable_pi_apply i.castSucc :
        Measurable (fun u : Fin (T + 1) → Point d => u i.castSucc))
  have hBase :
      HasCondDistrib
        (fun u : Fin (T + 1) → Point d => u (Fin.last T))
        Fin.init (frameNextKernel d T) (P.map U) := by
    rw [hLaw]
    exact preselectedProjectedGaussianLaw_last_hasCondDistrib d T
  exact hasCondDistrib_independent_history
    P U Zvar hU hZ hInd
    Fin.init (fun u => u (Fin.last T))
    hInit (measurable_pi_apply (Fin.last T))
    (frameNextKernel d T) hBase history hh

/-- The first j entries of a length-T tuple. -/
def framePrefix {d j T : ℕ} (h : j ≤ T)
    (u : Fin T → Point d) : Fin j → Point d :=
  fun i => u (i.castLE h)

lemma measurable_framePrefix {d j T : ℕ} (h : j ≤ T) :
    Measurable (framePrefix (d := d) h) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply (i.castLE h)

/-- The recursively selected laws are projectively consistent: every
initial segment has the same law as if sampling had stopped at that length. -/
theorem preselectedProjectedGaussianLaw_prefix
    (d j T : ℕ) (h : j ≤ T) :
    (preselectedProjectedGaussianLaw d T).map
      (framePrefix (d := d) h) =
      preselectedProjectedGaussianLaw d j := by
  induction T generalizing j with
  | zero =>
      have hj : j = 0 := Nat.eq_zero_of_le_zero h
      subst j
      have hfun : framePrefix (d := d) h = id := by
        funext u
        funext i
        exact Fin.elim0 i
      rw [hfun, Measure.map_id]
  | succ T ih =>
      rcases Nat.lt_or_eq_of_le h with hlt | heq
      · have hjT : j ≤ T := Nat.le_of_lt_succ hlt
        have hfun :
            framePrefix (d := d) h =
              framePrefix (d := d) hjT ∘ Fin.init := by
          funext u
          funext i
          apply congrArg u
          apply Fin.ext
          rfl
        have hInit : Measurable
            (fun u : Fin (T + 1) → Point d => Fin.init u) := by
          apply measurable_pi_iff.mpr
          intro i
          simpa [Fin.init] using
            (measurable_pi_apply i.castSucc :
              Measurable (fun u : Fin (T + 1) → Point d => u i.castSucc))
        rw [hfun, ← Measure.map_map
          (measurable_framePrefix hjT) hInit]
        rw [preselectedProjectedGaussianLaw_init]
        exact ih j hjT
      · subst j
        have hfun : framePrefix (d := d) h = id := by
          funext u
          funext i
          rfl
        rw [hfun, Measure.map_id]

/-- Every column of one fixed length-T prior has the next-direction kernel
given its revealed prefix.  This is kernel-level sequentiality; intrinsic
sphere uniformity of the kernel on valid prefixes is still a geometric leaf. -/
theorem preselectedProjectedGaussianLaw_column_hasCondDistrib
    (d j T : ℕ) (h : j + 1 ≤ T) :
    HasCondDistrib
      ((fun u : Fin (j + 1) → Point d =>
        u (Fin.last j)) ∘ framePrefix (d := d) h)
      (Fin.init ∘ framePrefix (d := d) h)
      (frameNextKernel d j)
      (preselectedProjectedGaussianLaw d T) := by
  have hInit : Measurable
      (fun u : Fin (j + 1) → Point d => Fin.init u) := by
    apply measurable_pi_iff.mpr
    intro i
    simpa [Fin.init] using
      (measurable_pi_apply i.castSucc :
        Measurable (fun u : Fin (j + 1) → Point d => u i.castSucc))
  exact hasCondDistrib_pullback
    (preselectedProjectedGaussianLaw d T)
    (preselectedProjectedGaussianLaw d (j + 1))
    (framePrefix (d := d) h)
    (measurable_framePrefix h)
    (preselectedProjectedGaussianLaw_prefix d (j + 1) T h)
    Fin.init
    (fun u : Fin (j + 1) → Point d => u (Fin.last j))
    hInit (measurable_pi_apply (Fin.last j))
    (frameNextKernel d j)
    (preselectedProjectedGaussianLaw_last_hasCondDistrib d j)

/-- Every column of one preselected length-T law retains its conditional
transition kernel after revealing its prefix and any history computed from
that prefix and an independent private tape. -/
theorem preselectedProjectedGaussianLaw_column_independent_history
    {Ω Z H : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace H] (P : Measure Ω) [IsProbabilityMeasure P]
    (d j T : ℕ) (h : j + 1 ≤ T)
    (U : Ω → (Fin T → Point d)) (Zvar : Ω → Z)
    (hU : Measurable U) (hZ : Measurable Zvar)
    (hInd : U ⟂ᵢ[P] Zvar)
    (hLaw : P.map U = preselectedProjectedGaussianLaw d T)
    (history : (Fin j → Point d) × Z → H)
    (hh : Measurable history) :
    HasCondDistrib
      (fun ω => (framePrefix h (U ω)) (Fin.last j))
      (fun ω =>
        (Fin.init (framePrefix h (U ω)),
          history (Fin.init (framePrefix h (U ω)), Zvar ω)))
      ((frameNextKernel d j).comap
        (Prod.fst : ((Fin j → Point d) × H) → (Fin j → Point d))
        (measurable_fst :
          Measurable (Prod.fst :
            ((Fin j → Point d) × H) → (Fin j → Point d))))
      P := by
  have hInit : Measurable
      (fun u : Fin (j + 1) → Point d => Fin.init u) := by
    apply measurable_pi_iff.mpr
    intro i
    simpa [Fin.init] using
      (measurable_pi_apply i.castSucc :
        Measurable (fun u : Fin (j + 1) → Point d => u i.castSucc))
  have hV : Measurable
      (Fin.init ∘ framePrefix (d := d) h) :=
    hInit.comp (measurable_framePrefix h)
  have hY : Measurable
      ((fun u : Fin (j + 1) → Point d => u (Fin.last j)) ∘
        framePrefix (d := d) h) :=
    (measurable_pi_apply (Fin.last j)).comp
      (measurable_framePrefix h)
  have hBase :
      HasCondDistrib
        ((fun u : Fin (j + 1) → Point d => u (Fin.last j)) ∘
          framePrefix (d := d) h)
        (Fin.init ∘ framePrefix (d := d) h)
        (frameNextKernel d j) (P.map U) := by
    rw [hLaw]
    exact preselectedProjectedGaussianLaw_column_hasCondDistrib d j T h
  exact hasCondDistrib_independent_history
    P U Zvar hU hZ hInd
    (Fin.init ∘ framePrefix (d := d) h)
    ((fun u : Fin (j + 1) → Point d => u (Fin.last j)) ∘
      framePrefix (d := d) h)
    hV hY (frameNextKernel d j) hBase history hh

/-- Orthogonal projection of an ambient standard Gaussian has the standard
Gaussian law on the fixed target subspace. -/
theorem stdGaussian_orthogonalProjection_law
    (d : ℕ) (W : Submodule ℝ (Point d))
    [W.HasOrthogonalProjection] :
    (stdGaussian (Point d)).map W.orthogonalProjectionOnto =
      stdGaussian W := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [W.inner_orthogonalProjectionOnto_eq_of_mem_right]
  change charFun (stdGaussian (Point d)) (t : Point d) =
    charFun (stdGaussian W) t
  rw [charFun_stdGaussian, charFun_stdGaussian]
  simp

/-- A nontrivial finite-dimensional subspace Gaussian assigns zero mass to
the origin.  This transports the already proved Point-m statement through
an orthonormal coordinate isometry. -/
theorem stdGaussian_submodule_zero_null
    (d : ℕ) (W : Submodule ℝ (Point d)) [Nontrivial W] :
    (stdGaussian W) ({0} : Set W) = 0 := by
  let n := Module.finrank ℝ W
  have hn : 0 < n := Module.finrank_pos
  let e : Point n ≃ₗᵢ[ℝ] W :=
    (stdOrthonormalBasis ℝ W).repr.symm
  have hmap : (stdGaussian (Point n)).map e = stdGaussian W := by
    exact stdGaussian_map e
  rw [← hmap, Measure.map_apply e.continuous.measurable
    (measurableSet_singleton (0 : W))]
  have hpre : e ⁻¹' ({0} : Set W) = ({0} : Set (Point n)) := by
    ext x
    simp [e.injective.eq_iff]
  rw [hpre]
  exact stdGaussian_point_zero_null hn

lemma frameResidual_inner_zero {d j : ℕ}
    (v : Fin j → Point d) (hv : Orthonormal ℝ v)
    (z : Point d) (i : Fin j) :
    inner ℝ (v i) (frameResidual v z) = 0 := by
  unfold frameResidual
  rw [inner_sub_right]
  rw [hv.inner_right_fintype
    (fun k : Fin j => inner ℝ (v k) z) i]
  simp

/-- For an orthonormal prefix the explicit residual is the actual
orthogonal projection onto its complement. -/
theorem frameResidual_eq_orthogonalProjection {d j : ℕ}
    (v : Fin j → Point d) (hv : Orthonormal ℝ v)
    (z : Point d) :
    frameResidual v z =
      (((Submodule.span ℝ (Set.range v))ᗮ).orthogonalProjectionOnto z :
        Point d) := by
  let S : Submodule ℝ (Point d) := Submodule.span ℝ (Set.range v)
  let W : Submodule ℝ (Point d) := Sᗮ
  have hmem : frameResidual v z ∈ W := by
    apply (S.mem_orthogonal (frameResidual v z)).2
    intro w hw
    have hle : S ≤ (ℝ ∙ frameResidual v z)ᗮ := by
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact (Submodule.mem_orthogonal_singleton_iff_inner_left).2
        (frameResidual_inner_zero v hv z i)
    exact (Submodule.mem_orthogonal_singleton_iff_inner_left).1
      (hle hw)
  have herr : ∀ w ∈ W, inner ℝ (z - frameResidual v z) w = 0 := by
    intro w hw
    have hsum :
        z - frameResidual v z =
          ∑ i : Fin j, inner ℝ (v i) z • v i := by
      simp [frameResidual]
    rw [hsum, sum_inner]
    apply Finset.sum_eq_zero
    intro i hi
    have hiS : v i ∈ S :=
      Submodule.subset_span (Set.mem_range_self i)
    have hzero : inner ℝ (v i) w = 0 :=
      (S.mem_orthogonal w).1 hw (v i) hiS
    rw [inner_smul_left, hzero]
    simp
  have hproj := W.eq_starProjection_of_mem_of_inner_eq_zero hmem herr
  simpa only [Submodule.starProjection_apply] using hproj.symm

/-- At every valid short prefix the next projected Gaussian residual is
nonzero almost surely.  This includes a one-dimensional complement. -/
theorem frameResidual_ne_zero_ae {d j : ℕ} (hj : j < d)
    (v : Fin j → Point d) (hv : Orthonormal ℝ v) :
    ∀ᵐ z ∂stdGaussian (Point d), frameResidual v z ≠ 0 := by
  let S : Submodule ℝ (Point d) :=
    Submodule.span ℝ (Set.range v)
  let W : Submodule ℝ (Point d) := Sᗮ
  have hS : Module.finrank ℝ S = j := by
    simpa [S] using finrank_span_eq_card hv.linearIndependent
  have hE : Module.finrank ℝ (Point d) = d := by
    simpa [Point] using
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := d))
  have hWpos : 0 < Module.finrank ℝ W := by
    have hsum : Module.finrank ℝ S + Module.finrank ℝ W = d := by
      simpa [W, hE] using S.finrank_add_finrank_orthogonal
    omega
  letI : Nontrivial W := Module.nontrivial_of_finrank_pos hWpos
  have hZero :
      (stdGaussian (Point d))
        {z | W.orthogonalProjectionOnto z = 0} = 0 := by
    have hLaw := stdGaussian_orthogonalProjection_law d W
    have hh := congrArg
      (fun μ : Measure W => μ ({0} : Set W)) hLaw
    rw [Measure.map_apply (by fun_prop)
      (measurableSet_singleton (0 : W))] at hh
    exact hh.trans (stdGaussian_submodule_zero_null d W)
  have hSet :
      {z : Point d | frameResidual v z = 0} =
        {z | W.orthogonalProjectionOnto z = 0} := by
    ext z
    change frameResidual v z = 0 ↔ W.orthogonalProjectionOnto z = 0
    have hp : frameResidual v z =
        (W.orthogonalProjectionOnto z : Point d) :=
      frameResidual_eq_orthogonalProjection v hv z
    constructor
    · intro hz
      apply Subtype.ext
      change (W.orthogonalProjectionOnto z : Point d) = 0
      rw [← hp]
      exact hz
    · intro hz
      rw [hp, hz]
      simp
  apply ae_iff.mpr
  rw [show {z : Point d | ¬frameResidual v z ≠ 0} =
      {z : Point d | frameResidual v z = 0} by ext z; simp]
  rw [hSet]
  exact hZero

lemma frameNextDirection_mem_complement {d j : ℕ}
    (v : Fin j → Point d) (hv : Orthonormal ℝ v)
    (z : Point d) :
    frameNextDirection v z ∈
      (Submodule.span ℝ (Set.range v))ᗮ := by
  let W : Submodule ℝ (Point d) :=
    (Submodule.span ℝ (Set.range v))ᗮ
  have hp : frameResidual v z =
      (W.orthogonalProjectionOnto z : Point d) :=
    frameResidual_eq_orthogonalProjection v hv z
  change (‖frameResidual v z‖⁻¹ : ℝ) •
    frameResidual v z ∈ W
  rw [hp]
  exact W.smul_mem _ (W.orthogonalProjectionOnto z).property

lemma frameNextDirection_norm_one_of_ne_zero {d j : ℕ}
    (v : Fin j → Point d) (z : Point d)
    (hz : frameResidual v z ≠ 0) :
    ‖frameNextDirection v z‖ = 1 := by
  unfold frameNextDirection gaussianDirection
  exact norm_smul_inv_norm hz

/-- The next projected direction extends any valid prefix to an
orthonormal prefix whenever its residual is nonzero. -/
theorem frameSnoc_orthonormal_of_residual_ne_zero {d j : ℕ}
    (v : Fin j → Point d) (hv : Orthonormal ℝ v)
    (z : Point d) (hz : frameResidual v z ≠ 0) :
    Orthonormal ℝ
      (Fin.snoc (α := fun _ : Fin (j + 1) => Point d)
        v (frameNextDirection v z)) := by
  let S : Submodule ℝ (Point d) :=
    Submodule.span ℝ (Set.range v)
  have hW := frameNextDirection_mem_complement v hv z
  have hNorm := frameNextDirection_norm_one_of_ne_zero v z hz
  have hCross (i : Fin j) :
      inner ℝ (v i) (frameNextDirection v z) = 0 := by
    exact (S.mem_orthogonal _).1 hW (v i)
      (Submodule.subset_span (Set.mem_range_self i))
  constructor
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using hv.norm_eq_one k
    · simpa only [Fin.snoc_last] using hNorm
  · intro i k hik
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
      · have hne : i' ≠ k' := by
          intro heq
          exact hik (by simpa [heq])
        simpa only [Fin.snoc_castSucc] using hv.inner_eq_zero hne
      · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hCross i'
    · rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
      · rw [Fin.snoc_last, Fin.snoc_castSucc, inner_eq_zero_symm]
        exact hCross k'
      · exact (hik rfl).elim

lemma measurableSet_orthonormal_fin (d j : ℕ) :
    MeasurableSet
      {v : Fin j → Point d | Orthonormal ℝ v} := by
  classical
  have hEq :
      {v : Fin j → Point d | Orthonormal ℝ v} =
      (⋂ i : Fin j, {v | ‖v i‖ = 1}) ∩
      (⋂ i : Fin j, ⋂ k : Fin j,
        {v | i ≠ k → inner ℝ (v i) (v k) = 0}) := by
    ext v
    simp [Orthonormal, Pairwise]
  rw [hEq]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro k
    by_cases hik : i = k
    · simp [hik]
    · simpa [hik] using
        (measurableSet_eq_fun
          (by fun_prop :
            Measurable (fun v : Fin j → Point d =>
              inner ℝ (v i) (v k)))
          measurable_const)

/-- When T≤d, the recursively preselected tuple law is supported on
orthonormal T-frames. -/
theorem preselectedProjectedGaussianLaw_orthonormal_ae
    (d T : ℕ) (hT : T ≤ d) :
    ∀ᵐ u ∂preselectedProjectedGaussianLaw d T,
      Orthonormal ℝ u := by
  induction T with
  | zero =>
      exact Filter.Eventually.of_forall
        (fun u => Orthonormal.of_isEmpty u)
  | succ T ih =>
      have hprev : T ≤ d := Nat.le_of_succ_le hT
      have hj : T < d := Nat.lt_of_succ_le hT
      have hprevAE := ih hprev
      change ∀ᵐ u ∂(((preselectedProjectedGaussianLaw d T) ⊗ₘ
        frameNextKernel d T).map
          (fun p => Fin.snoc
            (α := fun _ : Fin (T + 1) => Point d) p.1 p.2)),
        Orthonormal ℝ u
      apply (ae_map_iff (measurable_frameSnoc d T).aemeasurable
        (measurableSet_orthonormal_fin d (T + 1))).2
      have hmeas :
          MeasurableSet
            {p : (Fin T → Point d) × Point d |
              Orthonormal ℝ
                (Fin.snoc
                  (α := fun _ : Fin (T + 1) => Point d) p.1 p.2)} :=
        (measurable_frameSnoc d T)
          (measurableSet_orthonormal_fin d (T + 1))
      apply Measure.ae_compProd_of_ae_ae hmeas
      filter_upwards [hprevAE] with v hv
      rw [frameNextKernel_apply]
      have hsnoc : Measurable
          (fun y : Point d =>
            Fin.snoc
              (α := fun _ : Fin (T + 1) => Point d) v y) := by
        simpa [Function.comp_def] using
          (measurable_frameSnoc d T).comp
            (measurable_const.prodMk measurable_id :
              Measurable (fun y : Point d => (v, y)))
      apply (ae_map_iff
        (measurable_frameNextDirection_fixed v).aemeasurable
        (hsnoc (measurableSet_orthonormal_fin d (T + 1)))).2
      filter_upwards [frameResidual_ne_zero_ae hj v hv] with z hz
      exact frameSnoc_orthonormal_of_residual_ne_zero v hv z hz

/-- A fixed default orthonormal frame, used only to totalize a null bad set. -/
def standardFrame (d T : ℕ) (h : T ≤ d) : Fin T → Point d :=
  fun i => EuclideanSpace.basisFun (Fin d) ℝ (i.castLE h)

theorem standardFrame_orthonormal (d T : ℕ) (h : T ≤ d) :
    Orthonormal ℝ (standardFrame d T h) := by
  change Orthonormal ℝ
    ((EuclideanSpace.basisFun (Fin d) ℝ) ∘ Fin.castLE h)
  exact (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp
    (Fin.castLE h) (Fin.castLE_injective h)

/-- Make the a.s. frame-valued tuple map total by replacing the null
nonorthonormal set with a fixed coordinate frame. -/
def repairedOrthonormalFrame (d T : ℕ) (h : T ≤ d)
    (u : Fin T → Point d) :
    {v : Fin T → Point d // Orthonormal ℝ v} := by
  classical
  exact if hu : Orthonormal ℝ u then ⟨u, hu⟩
    else ⟨standardFrame d T h, standardFrame_orthonormal d T h⟩

lemma measurable_repairedOrthonormalFrame (d T : ℕ) (h : T ≤ d) :
    Measurable (repairedOrthonormalFrame d T h) := by
  classical
  have hval : Measurable
      (fun u : Fin T → Point d =>
        (repairedOrthonormalFrame d T h u).1) := by
    have hfun :
        (fun u : Fin T → Point d =>
          (repairedOrthonormalFrame d T h u).1) =
        (fun u : Fin T → Point d =>
          if Orthonormal ℝ u then u else standardFrame d T h) := by
      funext u
      by_cases hu : Orthonormal ℝ u
      · simp [repairedOrthonormalFrame, hu]
      · simp [repairedOrthonormalFrame, hu]
    rw [hfun]
    exact Measurable.ite (measurableSet_orthonormal_fin d T)
      measurable_id measurable_const
  exact Measurable.subtype_mk hval

/-- A single probability law on actual orthonormal frames, selected from
d and T before any algorithm. -/
def preselectedOrthonormalFrameLaw (d T : ℕ) (h : T ≤ d) :
    Measure {v : Fin T → Point d // Orthonormal ℝ v} :=
  (preselectedProjectedGaussianLaw d T).map
    (repairedOrthonormalFrame d T h)

instance (d T : ℕ) (h : T ≤ d) :
    IsProbabilityMeasure (preselectedOrthonormalFrameLaw d T h) := by
  unfold preselectedOrthonormalFrameLaw
  letI : IsProbabilityMeasure (preselectedProjectedGaussianLaw d T) :=
    preselectedProjectedGaussianLaw_probability d T
  infer_instance

theorem preselectedOrthonormalFrameLaw_map_val
    (d T : ℕ) (h : T ≤ d) :
    (preselectedOrthonormalFrameLaw d T h).map Subtype.val =
      preselectedProjectedGaussianLaw d T := by
  have hae := preselectedProjectedGaussianLaw_orthonormal_ae d T h
  have heq :
      (fun u : Fin T → Point d =>
        ((repairedOrthonormalFrame d T h u :
          {v : Fin T → Point d // Orthonormal ℝ v}) :
          Fin T → Point d)) =ᵐ[preselectedProjectedGaussianLaw d T]
        id := by
    filter_upwards [hae] with u hu
    simp [repairedOrthonormalFrame, hu]
  have heq' :
      (Subtype.val ∘ repairedOrthonormalFrame d T h)
        =ᵐ[preselectedProjectedGaussianLaw d T] id := by
    simpa [Function.comp_def] using heq
  unfold preselectedOrthonormalFrameLaw
  rw [Measure.map_map measurable_subtype_coe
    (measurable_repairedOrthonormalFrame d T h)]
  rw [Measure.map_congr heq']
  simp

/-- The unit-sphere map induced by a linear isometry equivalence. -/
private def sphereMap {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) :
    Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1 :=
  fun x => ⟨e x.1, by
    have hx : ‖(x : E)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp x.2
    apply mem_sphere_zero_iff_norm.mpr
    simpa using hx⟩

private lemma measurable_sphereMap {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F) : Measurable (sphereMap e) := by
  exact Measurable.subtype_mk
    (e.continuous.measurable.comp measurable_subtype_coe)

private lemma sphereMap_symm_apply {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (x : Metric.sphere (0 : F) 1) :
    sphereMap e (sphereMap e.symm x) = x := by
  apply Subtype.ext
  simp [sphereMap]

private lemma cone_preimage_sphereMap {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F)
    (B : Set (Metric.sphere (0 : F) 1)) :
    e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' B)) =
      Ioo (0 : ℝ) 1 •
        (Subtype.val '' (sphereMap e ⁻¹' B)) := by
  ext x
  simp only [mem_preimage, ← image2_smul, mem_image2, mem_image]
  constructor
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, hry⟩
    let uE : Metric.sphere (0 : E) 1 := sphereMap e.symm u
    refine ⟨r, hr, (uE : E), ⟨uE, ?_, rfl⟩, ?_⟩
    · change sphereMap e uE ∈ B
      simpa [uE, sphereMap_symm_apply] using hu
    · apply e.injective
      calc
        e (r • (uE : E)) = r • e (uE : E) := e.map_smul r _
        _ = r • (u : F) := by simp [uE, sphereMap]
        _ = e x := hry
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, hry⟩
    refine ⟨r, hr, (sphereMap e u : F),
      ⟨sphereMap e u, hu, rfl⟩, ?_⟩
    calc
      r • (sphereMap e u : F) = r • e (u : E) := rfl
      _ = e (r • (u : E)) := (e.map_smul r _).symm
      _ = e x := congrArg e hry

/-- Canonical polar surface measure is natural under finite-dimensional
linear isometry equivalences. -/
theorem toSphere_map_linearIsometryEquiv {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F) :
    ((volume : Measure E).toSphere).map (sphereMap e) =
      (volume : Measure F).toSphere := by
  have hdim :
      Module.finrank ℝ E = Module.finrank ℝ F :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  have hvol (C : Set F) :
      (volume : Measure F) C =
        (volume : Measure E) (e ⁻¹' C) := by
    rw [← e.measurePreserving.map_eq]
    exact (e.toHomeomorph.measurableEmbedding.map_apply
      (volume : Measure E) C)
  apply Measure.ext
  intro B hB
  have hpre : MeasurableSet (sphereMap e ⁻¹' B) :=
    (measurable_sphereMap e) hB
  rw [Measure.map_apply (measurable_sphereMap e) hB,
    Measure.toSphere_apply' (μ := (volume : Measure E)) hpre,
    Measure.toSphere_apply' (μ := (volume : Measure F)) hB,
    hdim]
  rw [hvol, cone_preimage_sphereMap e B]

/-- The Point-m Gaussian-direction theorem transported to any nontrivial
finite-dimensional real inner-product space. -/
theorem stdGaussian_direction_eq_normalized_toSphere_generic
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [Nontrivial F] :
    (stdGaussian F).map (fun x : F => ‖x‖⁻¹ • x) =
      (((volume : Measure F).toSphere Set.univ)⁻¹ •
        ((volume : Measure F).toSphere)).map
          (Subtype.val : Metric.sphere (0 : F) 1 → F) := by
  let n := Module.finrank ℝ F
  have hn : 0 < n := Module.finrank_pos
  let e : Point n ≃ₗᵢ[ℝ] F :=
    (stdOrthonormalBasis ℝ F).repr.symm
  let τP : Measure (Metric.sphere (0 : Point n) 1) :=
    (volume : Measure (Point n)).toSphere
  let τF : Measure (Metric.sphere (0 : F) 1) :=
    (volume : Measure F).toSphere
  have hτ : τP.map (sphereMap e) = τF := by
    exact toSphere_map_linearIsometryEquiv e
  have hmass : τP Set.univ = τF Set.univ := by
    have hh := congrArg
      (fun μ : Measure (Metric.sphere (0 : F) 1) => μ Set.univ) hτ
    simpa [Measure.map_apply (measurable_sphereMap e)] using hh
  have hcomm (x : Point n) :
      (‖e x‖⁻¹ : ℝ) • e x =
        e (gaussianDirection (m := n) x) := by
    simp [gaussianDirection, e.map_smul]
  calc
    (stdGaussian F).map (fun x : F => ‖x‖⁻¹ • x) =
        ((stdGaussian (Point n)).map e).map
          (fun x : F => ‖x‖⁻¹ • x) := by
          rw [stdGaussian_map e]
    _ = ((stdGaussian (Point n)).map
          (gaussianDirection (m := n))).map e := by
          rw [Measure.map_map (by fun_prop) e.continuous.measurable,
            Measure.map_map e.continuous.measurable
              (measurable_gaussianDirection n)]
          congr 1
          funext x
          exact hcomm x
    _ = (((τP Set.univ)⁻¹ • τP).map
          (Subtype.val :
            Metric.sphere (0 : Point n) 1 → Point n)).map e := by
          rw [stdGaussian_direction_eq_normalized_toSphere n hn]
    _ = (((τP Set.univ)⁻¹ • τP).map (sphereMap e)).map
          (Subtype.val : Metric.sphere (0 : F) 1 → F) := by
          rw [Measure.map_map e.continuous.measurable measurable_subtype_coe,
            Measure.map_map measurable_subtype_coe
              (measurable_sphereMap e)]
          rfl
    _ = (((τP Set.univ)⁻¹ • τF)).map
          (Subtype.val : Metric.sphere (0 : F) 1 → F) := by
          rw [Measure.map_smul (τP Set.univ)⁻¹
            (measurable_sphereMap e).aemeasurable, hτ]
    _ = (((τF Set.univ)⁻¹ • τF)).map
          (Subtype.val : Metric.sphere (0 : F) 1 → F) := by
          rw [hmass]
    _ = _ := rfl

/-- At every valid short prefix, the concrete transition kernel is exactly
the probability-normalized intrinsic surface measure on the unit sphere of
the orthogonal complement, pushed into the ambient space. -/
theorem frameNextKernel_eq_normalized_complementSphere
    {d j : ℕ} (hj : j < d)
    (v : Fin j → Point d) (hv : Orthonormal ℝ v) :
    frameNextKernel d j v =
      (((volume : Measure
        ((Submodule.span ℝ (Set.range v))ᗮ)).toSphere Set.univ)⁻¹ •
        ((volume : Measure
          ((Submodule.span ℝ (Set.range v))ᗮ)).toSphere)).map
          (fun x : Metric.sphere
            (0 : (Submodule.span ℝ (Set.range v))ᗮ) 1 =>
            ((x.1 : (Submodule.span ℝ (Set.range v))ᗮ) : Point d)) := by
  let S : Submodule ℝ (Point d) :=
    Submodule.span ℝ (Set.range v)
  let W : Submodule ℝ (Point d) := Sᗮ
  have hS : Module.finrank ℝ S = j := by
    simpa [S] using finrank_span_eq_card hv.linearIndependent
  have hE : Module.finrank ℝ (Point d) = d := by
    simpa [Point] using
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := d))
  have hWpos : 0 < Module.finrank ℝ W := by
    have hsum : Module.finrank ℝ S + Module.finrank ℝ W = d := by
      simpa [W, hE] using S.finrank_add_finrank_orthogonal
    omega
  letI : Nontrivial W := Module.nontrivial_of_finrank_pos hWpos
  let τ : Measure (Metric.sphere (0 : W) 1) :=
    (volume : Measure W).toSphere
  have hProj :
      (stdGaussian (Point d)).map W.orthogonalProjectionOnto =
        stdGaussian W :=
    stdGaussian_orthogonalProjection_law d W
  have hDir :
      (stdGaussian W).map (fun x : W => ‖x‖⁻¹ • x) =
        ((τ Set.univ)⁻¹ • τ).map
          (Subtype.val : Metric.sphere (0 : W) 1 → W) := by
    exact stdGaussian_direction_eq_normalized_toSphere_generic
  have hfun (z : Point d) :
      frameNextDirection v z =
        (((‖W.orthogonalProjectionOnto z‖⁻¹ : ℝ) •
          W.orthogonalProjectionOnto z : W) : Point d) := by
    have hp : frameResidual v z =
        (W.orthogonalProjectionOnto z : Point d) :=
      frameResidual_eq_orthogonalProjection v hv z
    dsimp [frameNextDirection, gaussianDirection]
    rw [hp]
    rfl
  calc
    frameNextKernel d j v =
        (stdGaussian (Point d)).map (frameNextDirection v) :=
          frameNextKernel_apply d j v
    _ = (stdGaussian (Point d)).map
          ((fun x : W =>
            (((‖x‖⁻¹ : ℝ) • x : W) : Point d)) ∘
            W.orthogonalProjectionOnto) := by
          congr 1
          funext z
          exact hfun z
    _ = ((stdGaussian (Point d)).map
          W.orthogonalProjectionOnto).map
            (fun x : W => (((‖x‖⁻¹ : ℝ) • x : W) : Point d)) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = (stdGaussian W).map
          (fun x : W => (((‖x‖⁻¹ : ℝ) • x : W) : Point d)) := by
          rw [hProj]
    _ = ((stdGaussian W).map
          (fun x : W => (‖x‖⁻¹ : ℝ) • x)).map
            (Subtype.val : W → Point d) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = (((τ Set.univ)⁻¹ • τ).map
          (Subtype.val : Metric.sphere (0 : W) 1 → W)).map
            (Subtype.val : W → Point d) := by
          rw [hDir]
    _ = ((τ Set.univ)⁻¹ • τ).map
          (fun x : Metric.sphere (0 : W) 1 =>
            ((x.1 : W) : Point d)) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = _ := rfl

/-- Under the actual preselected orthonormal-frame law, every column has
the measurable next-direction kernel conditional on its revealed prefix.
For every realized prefix, the preceding theorem identifies this kernel
with normalized intrinsic surface measure on its orthogonal complement. -/
theorem preselectedOrthonormalFrameLaw_column_hasCondDistrib
    (d j T : ℕ) (hT : T ≤ d) (hj : j + 1 ≤ T) :
    HasCondDistrib
      (fun u : {v : Fin T → Point d // Orthonormal ℝ v} =>
        (framePrefix hj u.1) (Fin.last j))
      (fun u : {v : Fin T → Point d // Orthonormal ℝ v} =>
        Fin.init (framePrefix hj u.1))
      (frameNextKernel d j)
      (preselectedOrthonormalFrameLaw d T hT) := by
  have hInit : Measurable
      (fun u : Fin (j + 1) → Point d => Fin.init u) := by
    apply measurable_pi_iff.mpr
    intro i
    simpa [Fin.init] using
      (measurable_pi_apply i.castSucc :
        Measurable (fun u : Fin (j + 1) → Point d => u i.castSucc))
  exact hasCondDistrib_pullback
    (preselectedOrthonormalFrameLaw d T hT)
    (preselectedProjectedGaussianLaw d T)
    (Subtype.val :
      {v : Fin T → Point d // Orthonormal ℝ v} →
        (Fin T → Point d))
    measurable_subtype_coe
    (preselectedOrthonormalFrameLaw_map_val d T hT)
    (Fin.init ∘ framePrefix (d := d) hj)
    ((fun w : Fin (j + 1) → Point d =>
      w (Fin.last j)) ∘ framePrefix (d := d) hj)
    (hInit.comp (measurable_framePrefix hj))
    ((measurable_pi_apply (Fin.last j)).comp
      (measurable_framePrefix hj))
    (frameNextKernel d j)
    (preselectedProjectedGaussianLaw_column_hasCondDistrib
      d j T hj)

/-- Under any realization of the preselected orthonormal-frame prior with
an independent private tape, revealing the prefix and any measurable history
computed from that prefix and tape leaves the next-column kernel unchanged.
The kernel is intrinsically uniform on the complement sphere by
frameNextKernel_eq_normalized_complementSphere. -/
theorem preselectedOrthonormalFrameLaw_column_independent_history
    {Ω Z H : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace H] (P : Measure Ω) [IsProbabilityMeasure P]
    (d j T : ℕ) (hT : T ≤ d) (hj : j + 1 ≤ T)
    (U : Ω →
      {v : Fin T → Point d // Orthonormal ℝ v})
    (Zvar : Ω → Z)
    (hU : Measurable U) (hZ : Measurable Zvar)
    (hInd : U ⟂ᵢ[P] Zvar)
    (hLaw : P.map U = preselectedOrthonormalFrameLaw d T hT)
    (history : (Fin j → Point d) × Z → H)
    (hh : Measurable history) :
    HasCondDistrib
      (fun ω => (framePrefix hj (U ω).1) (Fin.last j))
      (fun ω =>
        (Fin.init (framePrefix hj (U ω).1),
          history (Fin.init (framePrefix hj (U ω).1), Zvar ω)))
      ((frameNextKernel d j).comap
        (Prod.fst : ((Fin j → Point d) × H) → (Fin j → Point d))
        (measurable_fst :
          Measurable (Prod.fst :
            ((Fin j → Point d) × H) → (Fin j → Point d))))
      P := by
  have hInit : Measurable
      (fun u : Fin (j + 1) → Point d => Fin.init u) := by
    apply measurable_pi_iff.mpr
    intro i
    simpa [Fin.init] using
      (measurable_pi_apply i.castSucc :
        Measurable (fun u : Fin (j + 1) → Point d => u i.castSucc))
  have hV : Measurable
      (fun u : {v : Fin T → Point d // Orthonormal ℝ v} =>
        Fin.init (framePrefix hj u.1)) :=
    (hInit.comp (measurable_framePrefix hj)).comp
      measurable_subtype_coe
  have hY : Measurable
      (fun u : {v : Fin T → Point d // Orthonormal ℝ v} =>
        (framePrefix hj u.1) (Fin.last j)) :=
    ((measurable_pi_apply (Fin.last j)).comp
      (measurable_framePrefix hj)).comp measurable_subtype_coe
  have hBase :
      HasCondDistrib
        (fun u : {v : Fin T → Point d // Orthonormal ℝ v} =>
          (framePrefix hj u.1) (Fin.last j))
        (fun u : {v : Fin T → Point d // Orthonormal ℝ v} =>
          Fin.init (framePrefix hj u.1))
        (frameNextKernel d j) (P.map U) := by
    rw [hLaw]
    exact preselectedOrthonormalFrameLaw_column_hasCondDistrib
      d j T hT hj
  exact hasCondDistrib_independent_history
    P U Zvar hU hZ hInd
    (fun u : {v : Fin T → Point d // Orthonormal ℝ v} =>
      Fin.init (framePrefix hj u.1))
    (fun u : {v : Fin T → Point d // Orthonormal ℝ v} =>
      (framePrefix hj u.1) (Fin.last j))
    hV hY (frameNextKernel d j) hBase history hh

end HeavyTailedNoise
