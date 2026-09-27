import HeavyTailedNoise.Model.Basic

/-! Finite shared-seed reveal counts. No algorithm, stopping time, or mask
hypothesis is hidden in these elementary probability identities. -/

namespace HeavyTailedNoise
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false

def revealCount {n : ℕ} (ξ : Fin n → Bool) : ℕ :=
  ∑ i, if ξ i then 1 else 0

theorem revealCount_succ {n : ℕ} (ξ : Fin (n+1) → Bool) :
    revealCount ξ = revealCount (fun i : Fin n => ξ i.castSucc) +
      (if ξ (Fin.last n) then 1 else 0) := by
  unfold revealCount
  exact Fin.sum_univ_castSucc (fun i => if ξ i then 1 else 0)

theorem revealCount_cast {n : ℕ} (ξ : Fin n → Bool) :
    (revealCount ξ : ℝ) = ∑ i : Fin n, if ξ i then (1 : ℝ) else 0 := by
  simp [revealCount]

theorem integrable_revealCount (n : ℕ) (θ : unitInterval) :
    Integrable (fun ξ : Fin n → Bool => (revealCount ξ : ℝ))
      (Measure.pi (fun _ => bernoulliMeasure true false θ)) := by
  simp_rw [revealCount_cast]
  apply integrable_finsetSum
  intro i hi
  exact integrable_comp_eval (μ := fun _ : Fin n => bernoulliMeasure true false θ)
    (i := i) (f := fun b : Bool => if b then (1 : ℝ) else 0)
    (integrable_bernoulliMeasure true false θ
    (fun b : Bool => if b then (1 : ℝ) else 0))

theorem integral_revealCount (n : ℕ) (θ : unitInterval) :
    (∫ ξ : Fin n → Bool, (revealCount ξ : ℝ)
      ∂Measure.pi (fun _ => bernoulliMeasure true false θ)) = (n : ℝ)*(θ : ℝ) := by
  simp_rw [revealCount_cast]
  rw [integral_finsetSum]
  · have hi (i : Fin n) :
        (∫ ξ : Fin n → Bool, (if ξ i then (1 : ℝ) else 0)
          ∂Measure.pi (fun _ => bernoulliMeasure true false θ)) = (θ : ℝ) := by
      rw [integral_comp_eval (μ := fun _ : Fin n => bernoulliMeasure true false θ)
        (i := i) (f := fun b : Bool => if b then (1 : ℝ) else 0)
        (measurable_of_finite
        (fun b : Bool => if b then (1 : ℝ) else 0)).aestronglyMeasurable]
      simp [integral_bernoulliMeasure, smul_eq_mul]
    simp_rw [hi]
    simp
  · intro i hi
    exact integrable_comp_eval (μ := fun _ : Fin n => bernoulliMeasure true false θ)
      (i := i) (f := fun b : Bool => if b then (1 : ℝ) else 0)
      (integrable_bernoulliMeasure true false θ
      (fun b : Bool => if b then (1 : ℝ) else 0))

theorem revealCount_tail_le (n : ℕ) (θ : unitInterval)
    {T : ℝ} (hT : 0 < T) :
    (Measure.pi (fun _ : Fin n => bernoulliMeasure true false θ)).real
      {ξ | T ≤ (revealCount ξ : ℝ)} ≤ (n : ℝ)*(θ : ℝ)/T := by
  apply (le_div_iff₀ hT).2
  rw [mul_comm]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := Measure.pi (fun _ : Fin n => bernoulliMeasure true false θ))
    (f := fun ξ => (revealCount ξ : ℝ))
    (Filter.Eventually.of_forall fun ξ => Nat.cast_nonneg (revealCount ξ))
    (integrable_revealCount n θ) T
  simpa only [integral_revealCount] using hm

theorem revealCount_tail_le_quarter (n : ℕ) (θ : unitInterval)
    {T : ℝ} (hT : 0 < T) (hbudget : 4*(n : ℝ)*(θ : ℝ) ≤ T) :
    (Measure.pi (fun _ : Fin n => bernoulliMeasure true false θ)).real
      {ξ | T ≤ (revealCount ξ : ℝ)} ≤ 1/4 := by
  apply (revealCount_tail_le n θ hT).trans
  apply (div_le_iff₀ hT).2
  linarith

end
end HeavyTailedNoise
