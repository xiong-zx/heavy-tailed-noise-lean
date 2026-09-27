import HeavyTailedNoise.Model.Basic

namespace HeavyTailedNoise

open Set Filter
open scoped BigOperators Topology Classical
noncomputable section

def frameCoordinates {d T : ℕ} (U : Fin T → Point d) (y : Point d) (i : Fin T) : ℝ :=
  inner ℝ (U i) y

/-- Span of any selected finite set of frame vectors. -/
def selectedFrameSpan {d T : ℕ} (U : Fin T → Point d) (s : Finset (Fin T)) :
    Submodule ℝ (Point d) := Submodule.span ℝ (U '' (s : Set (Fin T)))

/-- Explicit residual after removing the selected frame coordinates. Its
orthogonal-projection interpretation requires and is proved from orthonormality. -/
def frameOrthogonalResidual {d T : ℕ} (U : Fin T → Point d) (s : Finset (Fin T))
    (y : Point d) : Point d :=
  y - ∑ i ∈ s, frameCoordinates U y i • U i

theorem selectedFrame_sum_mem {d T : ℕ} (U : Fin T → Point d) (s : Finset (Fin T))
    (y : Point d) :
    (∑ i ∈ s, frameCoordinates U y i • U i) ∈ selectedFrameSpan U s := by
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, hi, rfl⟩

theorem frameOrthogonalResidual_mem_orthogonal {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (y : Point d) :
    frameOrthogonalResidual U s y ∈ (selectedFrameSpan U s)ᗮ := by
  have hinner : ∀ i ∈ s, inner ℝ (U i) (frameOrthogonalResidual U s y) = 0 := by
    intro i hi
    unfold frameOrthogonalResidual
    rw [inner_sub_right, hU.inner_right_sum (frameCoordinates U y) hi]
    simp [frameCoordinates]
  have hle : selectedFrameSpan U s ≤
      (innerSL ℝ (frameOrthogonalResidual U s y)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change inner ℝ (frameOrthogonalResidual U s y) (U i) = 0
    rw [real_inner_comm]
    exact hinner i hi
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro w hw
  exact hle hw

/-- Exact identification with the manuscript's orthogonal-complement projector. -/
theorem frameOrthogonalResidual_eq_starProjection {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (y : Point d) :
    frameOrthogonalResidual U s y = ((selectedFrameSpan U s)ᗮ).starProjection y := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (frameOrthogonalResidual_mem_orthogonal hU s y)
  intro w hw
  have heq : y - frameOrthogonalResidual U s y =
      ∑ i ∈ s, frameCoordinates U y i • U i := by
    simp [frameOrthogonalResidual]
  rw [heq]
  exact Submodule.inner_right_of_mem_orthogonal (selectedFrame_sum_mem U s y) hw

theorem frameOrthogonalResidual_norm_sq {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (s : Finset (Fin T)) (y : Point d) :
    ‖frameOrthogonalResidual U s y‖ ^ 2 =
      ‖y‖ ^ 2 - ∑ i ∈ s, (frameCoordinates U y i) ^ 2 := by
  have hnorm : ‖∑ i ∈ s, frameCoordinates U y i • U i‖ ^ 2 =
      ∑ i ∈ s, (frameCoordinates U y i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa [pow_two] using hU.inner_sum (frameCoordinates U y) (frameCoordinates U y) s
  have hcross : inner ℝ y (∑ i ∈ s, frameCoordinates U y i • U i) =
      ∑ i ∈ s, (frameCoordinates U y i) ^ 2 := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_smul_right, real_inner_comm (U i) y]
    simp [frameCoordinates, pow_two]
  unfold frameOrthogonalResidual
  rw [norm_sub_sq_real, hcross, hnorm]
  ring

/-- The exact manuscript residual σ, with the prefix indexed inclusively. -/
theorem contDiff_frameCoordinates_two {d T : ℕ} (U : Fin T → Point d) :
    ContDiff ℝ 2 (frameCoordinates U) := by
  unfold frameCoordinates
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.inner ℝ contDiff_id

theorem contDiff_frameOrthogonalResidual_two {d T : ℕ} (U : Fin T → Point d)
    (s : Finset (Fin T)) : ContDiff ℝ 2 (frameOrthogonalResidual U s) := by
  unfold frameOrthogonalResidual
  apply contDiff_id.sub
  apply ContDiff.sum
  intro i hi
  exact ((contDiff_pi.mp (contDiff_frameCoordinates_two U)) i).smul contDiff_const


end

end HeavyTailedNoise
