import HeavyTailedNoise.Upper.K1.KernelDriftMomentInterpolation

/-!
The outer-history scale in the source-mean drift is a deterministic noise
floor plus two tracker errors.  This probability-space inequality uses
their `p` moments and `s ≤ p`; it does not require an `(s+1)` moment because
the q-WAS displacement factor is capped pathwise by the actual center step.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem integral_two_errors_rpow_le_lpNorm
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (e₀ e₁ : α → ℝ) (he₀m : Measurable e₀) (he₁m : Measurable e₁)
    (he₀nonneg : ∀ a, 0 ≤ e₀ a) (he₁nonneg : ∀ a, 0 ≤ e₁ a)
    {p s c : ℝ} (hp : 1 ≤ p) (hs : 0 < s) (hsp : s ≤ p)
    (hc : 0 ≤ c)
    (he₀p : MemLp e₀ (ENNReal.ofReal p) μ)
    (he₁p : MemLp e₁ (ENNReal.ofReal p) μ) :
    (∫ a, ((c + e₀ a) + e₁ a) ^ s ∂μ) ≤
      (c + lpNorm e₀ (ENNReal.ofReal p) μ +
        lpNorm e₁ (ENNReal.ofReal p) μ) ^ s := by
  let A : α → ℝ := fun a => (c + e₀ a) + e₁ a
  have hpPos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpENN : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hcMem : MemLp (fun _ : α => c)
      (ENNReal.ofReal p) μ := memLp_const _
  have hAf : A = ((fun _ : α => c) + e₀) + e₁ := by
    funext a
    rfl
  have hAmeas : Measurable A :=
    (measurable_const.add he₀m).add he₁m
  have hAMem : MemLp A (ENNReal.ofReal p) μ := by
    rw [hAf]
    exact (hcMem.add he₀p).add he₁p
  have hAnonneg (a : α) : 0 ≤ A a :=
    add_nonneg (add_nonneg hc (he₀nonneg a)) (he₁nonneg a)
  have hInterp : (∫ a, A a ^ s ∂μ) ≤
      (lpNorm A (ENNReal.ofReal p) μ) ^ s :=
    integral_rpow_le_lpNorm_rpow_of_probability
      μ A hAmeas hAnonneg hs hsp hAMem
  have hcLp : lpNorm (fun _ : α => c)
      (ENNReal.ofReal p) μ = c := by
    rw [lpNorm_const' (ENNReal.ofReal_ne_zero_iff.mpr hpPos)
      ENNReal.ofReal_ne_top c]
    simp [hc]
  have hLpA : lpNorm A (ENNReal.ofReal p) μ ≤
      c + lpNorm e₀ (ENNReal.ofReal p) μ +
        lpNorm e₁ (ENNReal.ofReal p) μ := by
    rw [hAf]
    calc
      lpNorm (((fun _ : α => c) + e₀) + e₁)
          (ENNReal.ofReal p) μ ≤
        lpNorm ((fun _ : α => c) + e₀)
            (ENNReal.ofReal p) μ +
          lpNorm e₁ (ENNReal.ofReal p) μ :=
        lpNorm_add_le (hcMem.add he₀p) hpENN
      _ ≤ (lpNorm (fun _ : α => c) (ENNReal.ofReal p) μ +
            lpNorm e₀ (ENNReal.ofReal p) μ) +
          lpNorm e₁ (ENNReal.ofReal p) μ :=
        add_le_add (lpNorm_add_le hcMem hpENN) le_rfl
      _ = c + lpNorm e₀ (ENNReal.ofReal p) μ +
          lpNorm e₁ (ENNReal.ofReal p) μ := by rw [hcLp]
  calc
    (∫ a, ((c + e₀ a) + e₁ a) ^ s ∂μ) =
        ∫ a, A a ^ s ∂μ := rfl
    _ ≤ (lpNorm A (ENNReal.ofReal p) μ) ^ s := hInterp
    _ ≤ (c + lpNorm e₀ (ENNReal.ofReal p) μ +
        lpNorm e₁ (ENNReal.ofReal p) μ) ^ s :=
      Real.rpow_le_rpow lpNorm_nonneg hLpA hs.le

end

end HeavyTailedNoise.UpperK1
