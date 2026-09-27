import HeavyTailedNoise.Probability.GaussianKL

/-!
The direction of a finite-dimensional standard Gaussian, expressed through
mathlib's polar surface measure.  No frame or algorithm state is introduced.
-/

open MeasureTheory ProbabilityTheory WithLp
open scoped ENNReal

noncomputable section

namespace HeavyTailedNoise

private lemma map_withDensity_equiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    (μ.withDensity f).map e =
      (μ.map e).withDensity (fun y => f (e.symm y)) := by
  apply Measure.ext
  intro s hs
  calc
    ((μ.withDensity f).map e) s =
        ∫⁻ x in e ⁻¹' s, f x ∂μ := by
          rw [Measure.map_apply e.measurable hs,
            withDensity_apply _ (hs.preimage e.measurable)]
    _ = ∫⁻ y in s, f (e.symm y) ∂(μ.map e) := by
          have h := setLIntegral_map (μ := μ) hs
            (hf.comp e.symm.measurable) e.measurable
          simpa [Function.comp_def] using h.symm
    _ = ((μ.map e).withDensity (fun y => f (e.symm y))) s := by
          rw [withDensity_apply _ hs]

private lemma comap_withDensity_subtype {α : Type*} [MeasurableSpace α]
    {s : Set α} (hs : MeasurableSet s) (μ : Measure α)
    (f : α → ℝ≥0∞) :
    (μ.withDensity f).comap (Subtype.val : s → α) =
      (μ.comap (Subtype.val : s → α)).withDensity
        (fun x : s => f x.1) := by
  let i : MeasurableEmbedding (Subtype.val : s → α) :=
    MeasurableEmbedding.subtype_coe hs
  apply Measure.ext
  intro t ht
  rw [i.comap_apply,
    withDensity_apply _ (i.measurableSet_image.mpr ht),
    withDensity_apply _ ht]
  exact (setLIntegral_subtype hs t f).symm

/-- The product-Gaussian density, transported through the canonical
coordinate/Euclidean measurable equivalence. -/
lemma stdGaussian_point_eq_withDensity (m : ℕ) :
    stdGaussian (Point m) =
      (volume : Measure (Point m)).withDensity
        (fun x : Point m =>
          ENNReal.ofReal
            (∏ i : Fin m, gaussianPDFReal 0 1 (x i))) := by
  let e : (Fin m → ℝ) ≃ᵐ Point m :=
    MeasurableEquiv.toLp 2 (Fin m → ℝ)
  let V : Measure (Fin m → ℝ) :=
    Measure.pi (fun _ : Fin m => (volume : Measure ℝ))
  have hV : V.map e = (volume : Measure (Point m)) := by
    change (volume : Measure (Fin m → ℝ)).map (toLp 2) =
      (volume : Measure (WithLp 2 (Fin m → ℝ)))
    exact (PiLp.volume_preserving_toLp (Fin m)).map_eq
  have hP := pi_gaussianReal_eq_withDensity
    (m := fun _ : Fin m => 0) (v := (1 : NNReal)) (by norm_num)
  have hD : (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map e =
      (V.map e).withDensity
        (fun y => ENNReal.ofReal
          (∏ i : Fin m, gaussianPDFReal 0 1 ((e.symm y) i))) := by
    rw [hP]
    exact map_withDensity_equiv e V (by fun_prop)
  rw [hV] at hD
  simpa [e, MeasurableEquiv.coe_toLp_symm] using
    (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin m)).symm.trans hD

/-- Positive dimension is essential: the zero-dimensional standard Gaussian
is a point mass at the origin. -/
lemma stdGaussian_point_zero_null {m : ℕ} (hm : 0 < m) :
    stdGaussian (Point m) ({0} : Set (Point m)) = 0 := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nontrivial (Point m) := inferInstance
  rw [stdGaussian_point_eq_withDensity m]
  exact (withDensity_absolutelyContinuous _ _) (measure_singleton 0)

/-- Totalized normalization: the value at zero is zero. -/
def gaussianDirection {m : ℕ} (x : Point m) : Point m := ‖x‖⁻¹ • x

lemma measurable_gaussianDirection (m : ℕ) :
    Measurable (gaussianDirection (m := m)) := by
  unfold gaussianDirection
  fun_prop

private lemma gaussianPDFReal_product_radial (m : ℕ) (x : Point m) :
    (∏ i : Fin m, gaussianPDFReal 0 1 (x i)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ m *
        Real.exp (-(‖x‖ ^ 2) / 2) := by
  simp_rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 1
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.sum_neg_distrib, neg_mul]

/-- The coordinate product density is radial, with the normalizing constant
left in a form convenient for the polar argument. -/
lemma stdGaussian_point_eq_withDensity_radial (m : ℕ) :
    stdGaussian (Point m) =
      (volume : Measure (Point m)).withDensity
        (fun x : Point m =>
          ENNReal.ofReal
            ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
              Real.exp (-(‖x‖ ^ 2) / 2))) := by
  rw [stdGaussian_point_eq_withDensity]
  congr 1
  funext x
  rw [gaussianPDFReal_product_radial]

private lemma radial_withDensity_polar (m : ℕ) (hm : 0 < m)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (((volume : Measure (Point m)).withDensity
      (fun x : Point m => f ‖x‖)).comap
        (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).map
          (homeomorphUnitSphereProd (Point m)) =
      ((volume : Measure (Point m)).toSphere).prod
        ((Measure.volumeIoiPow (Module.finrank ℝ (Point m) - 1)).withDensity
          (fun r => f (r : ℝ))) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nontrivial (Point m) := inferInstance
  have hcompl : MeasurableSet ({0}ᶜ : Set (Point m)) :=
    (measurableSet_singleton (0 : Point m)).compl
  let e := (homeomorphUnitSphereProd (Point m)).toMeasurableEquiv
  have hbase :
      ((volume : Measure (Point m)).comap
        (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).map e =
      ((volume : Measure (Point m)).toSphere).prod
        (Measure.volumeIoiPow (Module.finrank ℝ (Point m) - 1)) := by
    simpa [e] using
      ((volume : Measure (Point m)).measurePreserving_homeomorphUnitSphereProd).map_eq
  have hnorm
      (p : Metric.sphere (0 : Point m) 1 × Set.Ioi (0 : ℝ)) :
      ‖(e.symm p).1‖ = (p.2 : ℝ) := by
    have h := homeomorphUnitSphereProd_apply_snd_coe
      (E := Point m) (e.symm p)
    simpa [e] using h.symm
  calc
    _ = (((volume : Measure (Point m)).comap
          (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).withDensity
            (fun x => f ‖(x : Point m)‖)).map e := by
          rw [comap_withDensity_subtype hcompl]
          rfl
    _ = (((volume : Measure (Point m)).comap
          (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).map e).withDensity
            (fun p => f ‖(e.symm p).1‖) := by
          exact map_withDensity_equiv e _ (by fun_prop)
    _ = (((volume : Measure (Point m)).toSphere).prod
          (Measure.volumeIoiPow (Module.finrank ℝ (Point m) - 1))).withDensity
            (fun p => f (p.2 : ℝ)) := by
          rw [hbase]
          congr 1
          funext p
          exact congrArg f (hnorm p)
    _ = ((volume : Measure (Point m)).toSphere).prod
          ((Measure.volumeIoiPow (Module.finrank ℝ (Point m) - 1)).withDensity
            (fun r => f (r : ℝ))) := by
          have hfRad : Measurable
              (fun r : Set.Ioi (0 : ℝ) => f (r : ℝ)) :=
            hf.comp measurable_subtype_coe
          exact (prod_withDensity_right
            (μ := (volume : Measure (Point m)).toSphere)
            (ν := Measure.volumeIoiPow (Module.finrank ℝ (Point m) - 1))
            hfRad).symm

/-- The direction of a nondegenerate finite-dimensional standard Gaussian is
exactly probability-normalized polar surface measure.  The normalization is
deduced from total mass, so no gamma integral is needed. -/
theorem stdGaussian_direction_eq_normalized_toSphere
    (m : ℕ) (hm : 0 < m) :
    (stdGaussian (Point m)).map (gaussianDirection (m := m)) =
      (((volume : Measure (Point m)).toSphere Set.univ)⁻¹ •
        ((volume : Measure (Point m)).toSphere)).map
          (Subtype.val :
            Metric.sphere (0 : Point m) 1 → Point m) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nontrivial (Point m) := inferInstance
  let τ : Measure (Metric.sphere (0 : Point m) 1) :=
    (volume : Measure (Point m)).toSphere
  let ρ : Measure (Set.Ioi (0 : ℝ)) :=
    Measure.volumeIoiPow (Module.finrank ℝ (Point m) - 1)
  let f : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ m *
        Real.exp (-(r ^ 2) / 2))
  let δ : Measure (Set.Ioi (0 : ℝ)) :=
    ρ.withDensity (fun r => f (r : ℝ))
  let h := homeomorphUnitSphereProd (Point m)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hγ :
      stdGaussian (Point m) =
        (volume : Measure (Point m)).withDensity
          (fun x : Point m => f ‖x‖) := by
    simpa [f] using stdGaussian_point_eq_withDensity_radial m
  have hpolar :
      ((stdGaussian (Point m)).comap
        (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).map h =
        τ.prod δ := by
    rw [hγ]
    simpa [τ, ρ, δ, h] using radial_withDensity_polar m hm f hf
  have hcompl : MeasurableSet ({0}ᶜ : Set (Point m)) :=
    (measurableSet_singleton (0 : Point m)).compl
  have hae :
      ∀ᵐ x ∂stdGaussian (Point m),
        x ∈ ({0}ᶜ : Set (Point m)) := by
    apply ae_iff.mpr
    simpa using (stdGaussian_point_zero_null hm)
  have hγ0 :
      ((stdGaussian (Point m)).comap
        (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).map
        (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m) =
          stdGaussian (Point m) := by
    rw [map_comap_subtype_coe hcompl]
    exact Measure.restrict_eq_self_of_ae_mem hae
  have hdirpoint (x : ({0}ᶜ : Set (Point m))) :
      gaussianDirection (m := m) x.1 = ((h x).1 : Point m) := by
    simpa [gaussianDirection, h] using
      (homeomorphUnitSphereProd_apply_fst_coe (E := Point m) x).symm
  have hdir :
      (stdGaussian (Point m)).map (gaussianDirection (m := m)) =
        δ Set.univ • τ.map
          (Subtype.val :
            Metric.sphere (0 : Point m) 1 → Point m) := by
    calc
      _ = (((stdGaussian (Point m)).comap
          (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).map
            (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).map
              (gaussianDirection (m := m)) := by rw [hγ0]
      _ = ((stdGaussian (Point m)).comap
          (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).map
            (fun x : ({0}ᶜ : Set (Point m)) =>
              gaussianDirection (m := m) x.1) := by
            rw [Measure.map_map (measurable_gaussianDirection m)
              measurable_subtype_coe]
            rfl
      _ = ((stdGaussian (Point m)).comap
          (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).map
            (fun x : ({0}ᶜ : Set (Point m)) => ((h x).1 : Point m)) := by
            congr 1
            funext x
            exact hdirpoint x
      _ = (((stdGaussian (Point m)).comap
          (Subtype.val : ({0}ᶜ : Set (Point m)) → Point m)).map h).map
            (fun p => (p.1 : Point m)) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
      _ = (τ.prod δ).map (fun p => (p.1 : Point m)) := by
            rw [hpolar]
      _ = δ Set.univ • τ.map
          (Subtype.val :
            Metric.sphere (0 : Point m) 1 → Point m) := by
            have hfun :
                (fun p : Metric.sphere (0 : Point m) 1 × Set.Ioi (0 : ℝ) =>
                  (p.1 : Point m)) = Subtype.val ∘ Prod.fst := rfl
            rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
              Measure.map_fst_prod,
              Measure.map_smul (δ Set.univ) (by fun_prop)]
  have hmass : δ Set.univ * τ Set.univ = 1 := by
    have hleft :
        ((stdGaussian (Point m)).map
          (gaussianDirection (m := m))) Set.univ = 1 := by
      rw [Measure.map_apply (measurable_gaussianDirection m)
        MeasurableSet.univ]
      simp
    have hright :
        (δ Set.univ • τ.map
          (Subtype.val :
            Metric.sphere (0 : Point m) 1 → Point m)) Set.univ =
          δ Set.univ * τ Set.univ := by
      rw [Measure.smul_apply,
        Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
      simp
    calc
      δ Set.univ * τ Set.univ =
          (δ Set.univ • τ.map
            (Subtype.val :
              Metric.sphere (0 : Point m) 1 → Point m)) Set.univ := hright.symm
      _ = ((stdGaussian (Point m)).map
          (gaussianDirection (m := m))) Set.univ := by rw [hdir]
      _ = 1 := hleft
  have hscale : δ Set.univ = (τ Set.univ)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left hmass
  calc
    (stdGaussian (Point m)).map (gaussianDirection (m := m)) =
        δ Set.univ • τ.map
          (Subtype.val :
            Metric.sphere (0 : Point m) 1 → Point m) := hdir
    _ = (τ Set.univ)⁻¹ • τ.map
          (Subtype.val :
            Metric.sphere (0 : Point m) 1 → Point m) := by rw [hscale]
    _ = ((τ Set.univ)⁻¹ • τ).map
          (Subtype.val :
            Metric.sphere (0 : Point m) 1 → Point m) := by
          exact (Measure.map_smul (τ Set.univ)⁻¹ (by fun_prop)).symm
    _ = _ := rfl

end HeavyTailedNoise
