import HeavyTailedNoise.Lower.Randomized.AdaptiveHaar

/-!
Finite-measure continuity and countable-to-all reflection invariance.
These are ordinary measure/geometry results, independent of any actual
oracle, stopped record, or assumed conditional Haar law.
-/

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology ProbabilityTheory ENNReal

noncomputable section

namespace HeavyTailedNoise.RandomizedLift

theorem continuous_frameAction {d T : ℕ} (W : Point d ≃ₗᵢ[ℝ] Point d) :
    Continuous (frameAction (T := T) W) := by
  apply continuous_pi
  intro i
  exact W.continuous.comp (continuous_apply i)

theorem continuousAt_householder_apply {d : ℕ} (w x : Point d) (hw : w ≠ 0) :
    ContinuousAt (fun v : Point d => householder v x) w := by
  simp only [householder_apply]
  have hnum : ContinuousAt (fun v : Point d => inner ℝ v x) w :=
    continuousAt_id.inner continuousAt_const
  have hden : ContinuousAt (fun v : Point d => ‖v‖ ^ 2) w :=
    continuousAt_id.norm.pow 2
  have hne : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hg : ContinuousAt (fun v : Point d => (inner ℝ v x / ‖v‖ ^ 2) • v) w :=
    (hnum.div hden hne).smul continuousAt_id
  exact continuousAt_const.sub (hg.const_smul (2 : ℝ))

theorem tendsto_householder_frameAction {d T : ℕ}
    (w : ℕ → Point d) (v : Point d) (hv : v ≠ 0)
    (hw : Tendsto w atTop (𝓝 v)) (U : Fin T → Point d) :
    Tendsto (fun k => frameAction (householder (w k)) U) atTop
      (𝓝 (frameAction (householder v) U)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact (continuousAt_householder_apply v (U i) hv).tendsto.comp hw

/-- Bounded-continuous test integrals give weak continuity at nonzero
normals. No support condition on the finite frame measure is needed. -/
theorem frameHouseholder_integral_tendsto {d T : ℕ}
    (μ : Measure (Fin T → Point d)) [IsFiniteMeasure μ]
    (w : ℕ → Point d) (v : Point d) (hv : v ≠ 0)
    (hw : Tendsto w atTop (𝓝 v)) (φ : BoundedContinuousFunction (Fin T → Point d) ℝ) :
    Tendsto (fun k => ∫ U, φ (frameAction (householder (w k)) U) ∂μ)
      atTop (𝓝 (∫ U, φ (frameAction (householder v) U) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro k
    exact (φ.continuous.comp (continuous_frameAction (householder (w k)))).aestronglyMeasurable
  · exact integrable_const ‖φ‖
  · intro k
    exact Filter.Eventually.of_forall (fun U => φ.norm_coe_le_norm _)
  · exact Filter.Eventually.of_forall (fun U =>
      φ.continuous.continuousAt.tendsto.comp (tendsto_householder_frameAction w v hv hw U))

/-- The same convergence stated in the standard weak topology of
probability measures, rather than only as a test-integral formula. -/
theorem frameHouseholder_pushforward_tendsto {d T : ℕ}
    (μ : ProbabilityMeasure (Fin T → Point d))
    (w : ℕ → Point d) (v : Point d) (hv : v ≠ 0)
    (hw : Tendsto w atTop (𝓝 v)) :
    Tendsto (fun k => μ.map (frameAction (householder (w k)))) atTop
      (𝓝 (μ.map (frameAction (householder v)))) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  change Tendsto
    (fun k => ∫ U, φ U ∂(μ : Measure (Fin T → Point d)).map (frameAction (householder (w k))))
    atTop (𝓝 (∫ U, φ U ∂(μ : Measure (Fin T → Point d)).map (frameAction (householder v))))
  have hseq : (fun k => ∫ U, φ U ∂(μ : Measure (Fin T → Point d)).map
      (frameAction (householder (w k)))) =
      (fun k => ∫ U, φ (frameAction (householder (w k)) U) ∂(μ : Measure (Fin T → Point d))) := by
    funext k
    exact integral_map (measurable_frameAction _).aemeasurable φ.continuous.aestronglyMeasurable
  rw [hseq, integral_map (measurable_frameAction _).aemeasurable φ.continuous.aestronglyMeasurable]
  exact frameHouseholder_integral_tendsto (μ : Measure (Fin T → Point d)) w v hv hw φ

/-- Invariant finite measures remain invariant at a nonzero limit normal. -/
theorem householder_invariance_of_normal_tendsto {d T : ℕ}
    (μ : Measure (Fin T → Point d)) [IsFiniteMeasure μ]
    (w : ℕ → Point d) (v : Point d) (hv : v ≠ 0)
    (hw : Tendsto w atTop (𝓝 v))
    (hinvariant : ∀ k, μ.map (frameAction (householder (w k))) = μ) :
    μ.map (frameAction (householder v)) = μ := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map (measurable_frameAction _).aemeasurable φ.continuous.aestronglyMeasurable]
  have hlim := frameHouseholder_integral_tendsto μ w v hv hw φ
  have hconst : (fun k => ∫ U, φ (frameAction (householder (w k)) U) ∂μ) =
      (fun _ : ℕ => ∫ U, φ U ∂μ) := by
    funext k
    rw [← integral_map (measurable_frameAction _).aemeasurable φ.continuous.aestronglyMeasurable,
      hinvariant k]
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem frameAction_householder_zero_eq_id (d T : ℕ) :
    (frameAction (householder (0 : Point d)) : (Fin T → Point d) → _) = id := by
  funext U i
  simp [frameAction, householder_apply]

theorem continuous_observedResidual_fixed {d n : ℕ} (v : Fin n → Point d) :
    Continuous (observedResidual v) := by
  have heq : observedResidual v =
      ((Submodule.span ℝ (Set.range v))ᗮ).starProjection := by
    funext x
    exact observedResidual_eq_starProjection v x
  rw [heq]
  exact ((Submodule.span ℝ (Set.range v))ᗮ).starProjection.continuous

/-- Ambient density suffices: the image sequence need not enumerate an
orthonormal basis or avoid zero projected normals. -/
theorem residual_householder_invariance_of_dense {d T n : ℕ}
    (μ : Measure (Fin T → Point d)) [IsFiniteMeasure μ]
    (v : Fin n → Point d) (D : Set (Point d)) (hD : Dense D)
    (hinvariant : ∀ r ∈ D,
      μ.map (frameAction (householder (observedResidual v r))) = μ) :
    ∀ r : Point d, μ.map (frameAction (householder (observedResidual v r))) = μ := by
  intro r
  by_cases hr : observedResidual v r = 0
  · rw [hr, frameAction_householder_zero_eq_id, Measure.map_id]
  · have hclosure : r ∈ closure D := by rw [hD.closure_eq]; trivial
    obtain ⟨s, hs, hsr⟩ := mem_closure_iff_seq_limit.mp hclosure
    apply householder_invariance_of_normal_tendsto μ
      (fun k => observedResidual v (s k)) (observedResidual v r) hr
      ((continuous_observedResidual_fixed v).continuousAt.tendsto.comp hsr)
    intro k
    exact hinvariant (s k) (hs k)

theorem residual_householder_invariance_of_denseSeq {d T n : ℕ}
    (μ : Measure (Fin T → Point d)) [IsFiniteMeasure μ]
    (v : Fin n → Point d)
    (hinvariant : ∀ k : ℕ, μ.map
      (frameAction (householder (observedResidual v (denseSeq (Point d) k)))) = μ) :
    ∀ r : Point d, μ.map (frameAction (householder (observedResidual v r))) = μ := by
  apply residual_householder_invariance_of_dense μ v (Set.range (denseSeq (Point d)))
    (denseRange_denseSeq (Point d))
  rintro r ⟨k, rfl⟩
  exact hinvariant k

/-- Countably many pointwise-in-normal a.e. claims become one common
conull set on which every normal is allowed. The observation list may vary
arbitrarily with the record; its measurability belongs to the application. -/
theorem ae_residual_householder_invariance_of_denseSeq
    {Ω : Type*} [MeasurableSpace Ω] {d T n : ℕ}
    (P : Measure Ω) (κ : Kernel Ω (Fin T → Point d)) [IsFiniteKernel κ]
    (v : Ω → Fin n → Point d)
    (hinvariant : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (κ ω).map (frameAction
        (householder (observedResidual (v ω) (denseSeq (Point d) k)))) = κ ω) :
    ∀ᵐ ω ∂P, ∀ r : Point d,
      (κ ω).map (frameAction (householder (observedResidual (v ω) r))) = κ ω := by
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ,
      (κ ω).map (frameAction
        (householder (observedResidual (v ω) (denseSeq (Point d) k)))) = κ ω :=
    ae_all_iff.mpr hinvariant
  filter_upwards [hall] with ω hω
  exact residual_householder_invariance_of_denseSeq (κ ω) (v ω) hω

end HeavyTailedNoise.RandomizedLift
