import HeavyTailedNoise.Lower.Gated.NextDirectionFrozenKernel

/-!
For every valid short revealed prefix, the checked Haar next-direction kernel
is supported on directions that extend it orthonormally. A fixed valid
default direction totalizes invalid, zero-measure inputs without altering the
actual conditional law.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem measurableSet_validNextDirection
    {d j : ℕ} (v : Fin j → Point d) :
    MeasurableSet {θ : Point d | Orthonormal ℝ (Fin.snoc v θ)} := by
  have hsnoc : Measurable (fun θ : Point d =>
      (Fin.snoc v θ : Fin (j + 1) → Point d)) := by
    simpa only [Function.comp_def, id_eq] using
      (measurable_frameSnoc d j).comp
        ((measurable_const : Measurable (fun _ : Point d => v)).prodMk
          measurable_id)
  exact hsnoc (measurableSet_orthonormal_fin d (j + 1))

theorem frameNextKernel_validNextDirection_ae
    {d j : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) :
    ∀ᵐ θ ∂frameNextKernel d j v,
      Orthonormal ℝ (Fin.snoc v θ) := by
  rw [frameNextKernel_apply]
  apply (ae_map_iff
    (measurable_frameNextDirection_fixed v).aemeasurable
    (measurableSet_validNextDirection v)).2
  filter_upwards [frameResidual_ne_zero_ae hj v hv] with z hz
  exact frameSnoc_orthonormal_of_residual_ne_zero v hv z hz

theorem exists_validNextDirection
    {d j : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) :
    ∃ θ : Point d, Orthonormal ℝ (Fin.snoc v θ) :=
  (frameNextKernel_validNextDirection_ae hj v hv).exists

def chosenValidNextDirection
    {d j : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) : Point d :=
  Classical.choose (exists_validNextDirection hj v hv)

theorem chosenValidNextDirection_orthonormal
    {d j : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (Fin.snoc v (chosenValidNextDirection hj v hv)) :=
  Classical.choose_spec (exists_validNextDirection hj v hv)

def repairNextDirection
    {d j : ℕ} (v : Fin j → Point d) (θ₀ θ : Point d) : Point d := by
  classical
  exact if Orthonormal ℝ (Fin.snoc v θ) then θ else θ₀

theorem measurable_repairNextDirection
    {d j : ℕ} (v : Fin j → Point d) (θ₀ : Point d) :
    Measurable (repairNextDirection v θ₀) := by
  classical
  unfold repairNextDirection
  exact Measurable.ite (measurableSet_validNextDirection v)
    measurable_id measurable_const

theorem repairNextDirection_valid
    {d j : ℕ} (v : Fin j → Point d) (θ₀ θ : Point d)
    (hθ₀ : Orthonormal ℝ (Fin.snoc v θ₀)) :
    Orthonormal ℝ (Fin.snoc v (repairNextDirection v θ₀ θ)) := by
  classical
  by_cases hθ : Orthonormal ℝ (Fin.snoc v θ)
  · simpa [repairNextDirection, hθ] using hθ
  · simpa [repairNextDirection, hθ] using hθ₀

theorem repairNextDirection_ae_eq_self
    {d j : ℕ} (hj : j < d) (v : Fin j → Point d)
    (hv : Orthonormal ℝ v) (θ₀ : Point d) :
    repairNextDirection v θ₀ =ᵐ[frameNextKernel d j v] id := by
  classical
  filter_upwards [frameNextKernel_validNextDirection_ae hj v hv] with θ hθ
  simp [repairNextDirection, hθ]

end

end HeavyTailedNoise
