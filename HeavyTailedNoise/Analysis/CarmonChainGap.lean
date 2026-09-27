import HeavyTailedNoise.Analysis.CarmonChain
import HeavyTailedNoise.Analysis.CarmonScalarBounds

/-!
Quantitative lower bound for the exact finite Carmon chain.  The Gaussian
integral is bounded by its full-line integral before estimating each link.
-/

namespace HeavyTailedNoise

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem carmonPhi_lt_414 (t : ℝ) : carmonPhi t < (207 / 50 : ℝ) := by
  have hkernel : 0 ≤ᵐ[volume] (fun s : ℝ => Real.exp (-s ^ 2 / 2)) :=
    Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le)
  have hInt :
      (∫ s in Set.Iic t, Real.exp (-s ^ 2 / 2)) ≤
        ∫ s : ℝ, Real.exp (-s ^ 2 / 2) :=
    setIntegral_le_integral integrable_carmonPhi_kernel hkernel
  have hGaussian :
      (∫ s : ℝ, Real.exp (-s ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
    have hfun : (fun s : ℝ => Real.exp (-s ^ 2 / 2)) =
        (fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s ^ 2)) := by
      funext s
      congr 1
      ring
    rw [hfun, integral_gaussian]
    congr 1
    ring
  have hpi : Real.sqrt (2 * Real.pi) < (627 / 250 : ℝ) := by
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
    have hnonneg := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith [Real.pi_lt_d4]
  unfold carmonPhi
  calc
    Real.sqrt (Real.exp 1) * ∫ s in Set.Iic t, Real.exp (-s ^ 2 / 2)
        ≤ Real.sqrt (Real.exp 1) * ∫ s : ℝ, Real.exp (-s ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hInt (Real.sqrt_nonneg _)
    _ = Real.sqrt (Real.exp 1) * Real.sqrt (2 * Real.pi) := by rw [hGaussian]
    _ < (33 / 20 : ℝ) * (627 / 250 : ℝ) := by
      calc
        _ < (33 / 20 : ℝ) * Real.sqrt (2 * Real.pi) :=
          mul_lt_mul_of_pos_right carmonPhi_sqrt_exp_one_lt
            (Real.sqrt_pos.mpr (by positivity))
        _ < (33 / 20 : ℝ) * (627 / 250 : ℝ) :=
          mul_lt_mul_of_pos_left hpi (by norm_num)
    _ < 207 / 50 := by norm_num

private theorem carmonPsi_mul_carmonPhi_lt_12 (a b : ℝ) :
    carmonPsi a * carmonPhi b < 12 := by
  have hψ := carmonPsi_lt_exp_one a
  have hφ := carmonPhi_lt_414 b
  have hψ0 := carmonPsi_nonneg a
  have hφ0 := (carmonPhi_pos b).le
  have he : Real.exp 1 < (14 / 5 : ℝ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  calc
    carmonPsi a * carmonPhi b
        < Real.exp 1 * carmonPhi b :=
          mul_lt_mul_of_pos_right hψ (carmonPhi_pos b)
    _ < Real.exp 1 * (207 / 50 : ℝ) :=
      mul_lt_mul_of_pos_left hφ (Real.exp_pos 1)
    _ < (14 / 5 : ℝ) * (207 / 50 : ℝ) :=
      mul_lt_mul_of_pos_right he (by norm_num)
    _ < 12 := by norm_num

private theorem carmonChain_link_gt_neg12 (a b : ℝ) :
    -(12 : ℝ) <
      carmonPsi (-a) * carmonPhi (-b) - carmonPsi a * carmonPhi b := by
  have hplus : 0 ≤ carmonPsi (-a) * carmonPhi (-b) :=
    mul_nonneg (carmonPsi_nonneg _) (carmonPhi_pos _).le
  linarith [carmonPsi_mul_carmonPhi_lt_12 a b]

theorem carmonChain_lower_bound {T : ℕ} (z : Fin T → ℝ) :
    -(12 : ℝ) * T ≤ carmonChain z := by
  have hsum :
      (∑ _k : Fin T, (-(12 : ℝ))) ≤ carmonChain z := by
    unfold carmonChain
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with hzero
    · rw [carmonPsi_one]
      have hφ := carmonPhi_lt_414 (z k)
      linarith
    · exact (carmonChain_link_gt_neg12 (chainPredecessor z k) (z k)).le
  simpa [mul_comm] using hsum

theorem carmonChain_zero_nonpos (T : ℕ) :
    carmonChain (fun _ : Fin T => (0 : ℝ)) ≤ 0 := by
  unfold carmonChain
  apply Finset.sum_nonpos
  intro k hk
  by_cases hzero : k.val = 0
  · simp only [hzero, ↓reduceIte]
    rw [carmonPsi_one]
    have hφ := (carmonPhi_pos 0).le
    simpa using neg_nonpos.mpr hφ
  · simp only [hzero, ↓reduceIte]
    have hpred : chainPredecessor (fun _ : Fin T => (0 : ℝ)) k = 0 := by
      simp [chainPredecessor, hzero]
    rw [hpred, carmonPsi_zero_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      carmonPsi_zero_of_le (by norm_num : -(0 : ℝ) ≤ 1 / 2)]
    simp

/-- The exact scalar chain satisfies the frozen manuscript's `12T` gap. -/
theorem carmonChain_gap_le_12T {T : ℕ} :
    carmonChain (fun _ : Fin T => (0 : ℝ)) -
      sInf (Set.range (carmonChain (T := T))) ≤ 12 * T := by
  have hbdd : BddBelow (Set.range (carmonChain (T := T))) := by
    refine ⟨-(12 : ℝ) * T, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact carmonChain_lower_bound z
  have hne : (Set.range (carmonChain (T := T))).Nonempty :=
    ⟨carmonChain (fun _ => 0), ⟨fun _ => 0, rfl⟩⟩
  have hinf : -(12 : ℝ) * T ≤ sInf (Set.range (carmonChain (T := T))) :=
    le_csInf hne (by rintro _ ⟨z, rfl⟩; exact carmonChain_lower_bound z)
  linarith [carmonChain_zero_nonpos T]

end

end HeavyTailedNoise
