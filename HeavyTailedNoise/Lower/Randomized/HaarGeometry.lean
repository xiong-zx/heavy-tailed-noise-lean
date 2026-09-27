import HeavyTailedNoise.Lower.Gated.HaarCapBound

/-!
Geometry and actual prior symmetries used by the Bernoulli lift.
These results do not identify a conditional law after adaptive observations.
In particular, prefix conditioning is never substituted for full-history
conditioning here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace HeavyTailedNoise.RandomizedLift

/-- Ambient rotation of every column of a fixed frame. -/
def frameAction {d T : ℕ} (W : Point d ≃ₗᵢ[ℝ] Point d)
    (U : Fin T → Point d) : Fin T → Point d := fun i => W (U i)

theorem measurable_frameAction {d T : ℕ} (W : Point d ≃ₗᵢ[ℝ] Point d) :
    Measurable (frameAction (T := T) W) := by
  apply measurable_pi_iff.mpr
  intro i
  exact W.continuous.measurable.comp (measurable_pi_apply i)

theorem frameResidual_frameAction {d j : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (v : Fin j → Point d) (z : Point d) :
    frameResidual (frameAction W v) (W z) = W (frameResidual v z) := by
  simp [frameResidual, frameAction, W.inner_map_map, map_sum]

theorem frameNextDirection_frameAction {d j : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (v : Fin j → Point d) (z : Point d) :
    frameNextDirection (frameAction W v) (W z) = W (frameNextDirection v z) := by
  rw [frameNextDirection, frameResidual_frameAction]
  simp [frameNextDirection, gaussianDirection, W.norm_map]

/-- Covariance of the explicit projected-Gaussian next-column kernel. -/
theorem frameNextKernel_frameAction {d j : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (v : Fin j → Point d) :
    frameNextKernel d j (frameAction W v) = (frameNextKernel d j v).map W := by
  rw [frameNextKernel_apply, frameNextKernel_apply]
  conv_lhs => rw [← stdGaussian_map W]
  rw [Measure.map_map (measurable_frameNextDirection_fixed _) W.continuous.measurable,
    Measure.map_map W.continuous.measurable (measurable_frameNextDirection_fixed _)]
  congr 1
  funext z
  exact frameNextDirection_frameAction W v z

theorem frameStep_frameAction {d j : ℕ}
    (W : Point d ≃ₗᵢ[ℝ] Point d) (q : Measure (Fin j → Point d))
    [IsProbabilityMeasure q] :
    (q ⊗ₘ frameNextKernel d j).map
        (fun p : (Fin j → Point d) × Point d =>
          (frameAction W p.1, W p.2)) =
      (q.map (frameAction W)) ⊗ₘ frameNextKernel d j := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hF : Measurable
      (fun p : (Fin j → Point d) × Point d =>
        (frameAction W p.1, W p.2)) :=
    ((measurable_frameAction W).comp measurable_fst).prodMk
      (W.continuous.measurable.comp measurable_snd)
  have hI : Measurable
      (fun v : Fin j → Point d => ∫⁻ y, φ (v, y) ∂frameNextKernel d j v) :=
    hφ.lintegral_kernel_prod_right'
  have hφF : Measurable
      (fun p : (Fin j → Point d) × Point d => φ (frameAction W p.1, W p.2)) :=
    hφ.comp hF
  rw [lintegral_map hφ hF,
    Measure.lintegral_compProd hφF,
    Measure.lintegral_compProd hφ,
    lintegral_map hI (measurable_frameAction W)]
  apply lintegral_congr
  intro v
  change (∫⁻ y, φ (frameAction W v, W y) ∂frameNextKernel d j v) =
    ∫⁻ y, φ (frameAction W v, y) ∂frameNextKernel d j (frameAction W v)
  rw [frameNextKernel_frameAction]
  exact (lintegral_map
    (hφ.comp (measurable_const.prodMk measurable_id))
    W.continuous.measurable).symm

/-- The law is chosen from d,T before the algorithm and is invariant under
every fixed ambient rotation. This is the concrete sequential Gaussian
frame prior, not a replacement prior sampled after observing queries. -/
theorem preselectedProjectedGaussianLaw_frameAction (d T : ℕ)
    (W : Point d ≃ₗᵢ[ℝ] Point d) :
    (preselectedProjectedGaussianLaw d T).map (frameAction W) =
      preselectedProjectedGaussianLaw d T := by
  induction T with
  | zero =>
    rw [preselectedProjectedGaussianLaw, Measure.map_dirac' (measurable_frameAction W)]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ T ih =>
    letI := preselectedProjectedGaussianLaw_probability d T
    have hF : Measurable
        (fun p : (Fin T → Point d) × Point d =>
          (frameAction W p.1, W p.2)) :=
      ((measurable_frameAction W).comp measurable_fst).prodMk
        (W.continuous.measurable.comp measurable_snd)
    have hs : (frameAction W : (Fin (T + 1) → Point d) → _) ∘
        (fun p : (Fin T → Point d) × Point d => Fin.snoc p.1 p.2) =
      (fun p : (Fin T → Point d) × Point d => Fin.snoc p.1 p.2) ∘
        (fun p => (frameAction W p.1, W p.2)) := by
      funext p i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
      · simp [frameAction, Function.comp_def]
      · simp [frameAction, Function.comp_def]
    rw [preselectedProjectedGaussianLaw,
      Measure.map_map (measurable_frameAction W) (measurable_frameSnoc d T), hs,
      ← Measure.map_map (measurable_frameSnoc d T) hF,
      frameStep_frameAction, ih]

/-- Only the span of observations costs dimension. The finite generating
list need not be linearly independent. -/
theorem observationSpan_finrank_le {d j n : ℕ}
    (v : Fin j → Point d) (q : Fin n → Point d) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range v ∪ Set.range q)) ≤ j + n := by
  classical
  have hs : Set.range v ∪ Set.range q = Set.range (Sum.elim v q) := by
    ext x
    simp
  rw [hs]
  calc
    _ ≤ (Set.range (Sum.elim v q)).toFinset.card := finrank_span_le_card _
    _ = Fintype.card (Set.range (Sum.elim v q)) := Set.toFinset_card _
    _ ≤ Fintype.card (Fin j ⊕ Fin n) := Fintype.card_range_le _
    _ = j + n := by simp

/-- A conditional complement direction has zero correlation with a vector
already contained in the observed span. This is purely geometric. -/
theorem inner_eq_zero_of_in_observed_span {d j : ℕ}
    (v : Fin j → Point d) (y u : Point d)
    (hy : y ∈ Submodule.span ℝ (Set.range v))
    (hu : u ∈ (Submodule.span ℝ (Set.range v))ᗮ) :
    inner ℝ y u = 0 :=
  Submodule.inner_right_of_mem_orthogonal hy hu

/-- Finite spherical cap union under the explicit kernel. The vectors may
be deterministic sections of a conditioning record, but that record's
actual conditional law must be proved separately before this is applied. -/
theorem kernel_small_coordinate_union {d j n : ℕ} (hj : j < d)
    (v : Fin j → Point d) (hv : Orthonormal ℝ v)
    {R : ℝ} (hR : 1 ≤ R)
    (hm : 4096 * R ^ 2 ≤ ((d - j - 1 : ℕ) : ℝ))
    (y : Fin n → Point d) (hy : ∀ i, ‖y i‖ ≤ R) :
    (frameNextKernel d j v).real (⋃ i,
      {u : Point d | (1 / 32 : ℝ) ≤ |inner ℝ (y i) u|}) ≤
      2 * n * Real.exp (-((d - j : ℕ) : ℝ) / (2048 * R ^ 2)) := by
  have hb (i : Fin n) : (frameNextKernel d j v).real
      {u : Point d | (1 / 32 : ℝ) ≤ |inner ℝ (y i) u|} ≤
      2 * Real.exp (-((d - j : ℕ) : ℝ) / (2048 * R ^ 2)) := by
    have ht := frameNextKernel_small_coordinate_bound hj v hv hR hm (y i) (hy i)
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity :
      0 ≤ 2 * Real.exp (-((d - j : ℕ) : ℝ) / (2048 * R ^ 2)))] using hh
  have hu := measureReal_iUnion_fintype_le (μ := frameNextKernel d j v)
    (fun i : Fin n => {u : Point d | (1 / 32 : ℝ) ≤ |inner ℝ (y i) u|})
  calc
    _ ≤ ∑ i : Fin n, (frameNextKernel d j v).real
        {u : Point d | (1 / 32 : ℝ) ≤ |inner ℝ (y i) u|} := hu
    _ ≤ ∑ _ : Fin n, 2 * Real.exp (-((d - j : ℕ) : ℝ) / (2048 * R ^ 2)) :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp; ring

end HeavyTailedNoise.RandomizedLift
