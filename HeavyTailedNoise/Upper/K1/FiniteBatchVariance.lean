import HeavyTailedNoise.Upper.K1.ActualBatchOrthogonality

/-!
Finite-time `L²` accounting for deterministic linear combinations of whole
shared-kernel runtime-batch errors. Cross-time terms vanish by the proved
full-prebatch-filtration orthogonality; within one response, all clipping
scales remain inside the same vector `kernelPhi`.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

variable {q : ℝ} (P : Schedule q)

private theorem measurable_actualKernelBatchError {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ) :
    Measurable (actualKernelBatchError P O u k) :=
  (measurable_kernelBatchErrorAtHistory P O u k).comp
    ((measurable_batchHistoryOfRun P O u).prodMk
      ((measurable_batchSeedBlock P u).comp measurable_snd))

private theorem actualKernelBatchError_inner_integrable
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u v : Fin P.T) (ku kv : ℕ) :
    Integrable (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
      ⟪actualKernelBatchError P O u ku z,
        actualKernelBatchError P O v kv z⟫_ℝ)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P))) := by
  letI : ENNReal.HolderTriple 2 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw O (responseCount P))
  let f := actualKernelBatchError P O u ku
  let g := actualKernelBatchError P O v kv
  have hf : MemLp f 2 μ := actualKernelBatchError_memLp_two P O u ku
  have hg : MemLp g 2 μ := actualKernelBatchError_memLp_two P O v kv
  have hprod : MemLp (fun z => ‖f z‖ * ‖g z‖) 1 μ :=
    hf.norm.mul hg.norm
  have hprodInt : Integrable (fun z => ‖f z‖ * ‖g z‖) μ :=
    memLp_one_iff_integrable.mp hprod
  have hinnerMeas : Measurable (fun z => ⟪f z, g z⟫_ℝ) :=
    Measurable.inner (𝕜 := ℝ)
      (measurable_actualKernelBatchError P O u ku)
      (measurable_actualKernelBatchError P O v kv)
  apply Integrable.mono' hprodInt hinnerMeas.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _)

/-- Exact Pythagorean identity in expectation for finitely many runtime
batches with public deterministic coefficients and fixed (possibly distinct)
kernel lags. -/
theorem finite_actualKernelBatchError_sq_eq_sum
    {d m : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (hm : m ≤ P.T)
    (a : Fin m → ℝ) (k : Fin m → ℕ) :
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ‖∑ i : Fin m,
        a i • actualKernelBatchError P O (i.castLE hm) (k i) z‖ ^ 2
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) =
      ∑ i : Fin m, (a i) ^ 2 *
        ∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖actualKernelBatchError P O (i.castLE hm) (k i) z‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw O (responseCount P))) := by
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw O (responseCount P))
  let e : Fin m →
      (Fin P.T × (Fin (responseCount P) → Seed)) → Point d :=
    fun i z => actualKernelBatchError P O (i.castLE hm) (k i) z
  have hinnerInt (i j : Fin m) :
      Integrable (fun z => ⟪e i z, e j z⟫_ℝ) μ :=
    actualKernelBatchError_inner_integrable P O (i.castLE hm)
      (j.castLE hm) (k i) (k j)
  have hcross (i j : Fin m) (hij : i ≠ j) :
      (∫ z, ⟪e i z, e j z⟫_ℝ ∂μ) = 0 := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hlt' : (i.castLE hm).val < (j.castLE hm).val := by
        simpa only [Fin.val_castLE] using (Fin.lt_iff_val_lt_val.mp hlt)
      exact actualKernelBatchError_crossTime_inner_zero P O
        (i.castLE hm) (j.castLE hm) hlt' (k i) (k j)
    · have hgt' : (j.castLE hm).val < (i.castLE hm).val := by
        simpa only [Fin.val_castLE] using (Fin.lt_iff_val_lt_val.mp hgt)
      calc
        (∫ z, ⟪e i z, e j z⟫_ℝ ∂μ) =
            ∫ z, ⟪e j z, e i z⟫_ℝ ∂μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (fun z => real_inner_comm _ _)
        _ = 0 := actualKernelBatchError_crossTime_inner_zero P O
          (j.castLE hm) (i.castLE hm) hgt' (k j) (k i)
  have hpoint (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      ‖∑ i : Fin m, a i • e i z‖ ^ 2 =
        ∑ i : Fin m, ∑ j : Fin m,
          a i * a j * ⟪e i z, e j z⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hweightedInt (i j : Fin m) : Integrable
      (fun z => a i * a j * ⟪e i z, e j z⟫_ℝ) μ :=
    (hinnerInt i j).const_mul (a i * a j)
  calc
    (∫ z, ‖∑ i : Fin m, a i • e i z‖ ^ 2 ∂μ) =
        ∫ z, ∑ i : Fin m, ∑ j : Fin m,
          a i * a j * ⟪e i z, e j z⟫_ℝ ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ = ∑ i : Fin m, ∑ j : Fin m,
          a i * a j * ∫ z, ⟪e i z, e j z⟫_ℝ ∂μ := by
            rw [integral_finsetSum]
            · apply Finset.sum_congr rfl
              intro i hi
              rw [integral_finsetSum]
              · apply Finset.sum_congr rfl
                intro j hj
                rw [integral_const_mul]
              · intro j hj
                exact hweightedInt i j
            · intro i hi
              apply integrable_finsetSum
              intro j hj
              exact hweightedInt i j
    _ = ∑ i : Fin m, (a i) ^ 2 *
          ∫ z, ‖e i z‖ ^ 2 ∂μ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_eq_single i]
            · simp_rw [real_inner_self_eq_norm_sq]
              ring
            · intro j hj hji
              rw [hcross i j hji.symm]
              ring
            · simp

/-- Combining exact cross-time cancellation with each batch's whole-vector
`1/n` second-moment input. -/
theorem finite_actualKernelBatchError_sq_le_sources
    {d m : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (hm : m ≤ P.T)
    (a : Fin m → ℝ) (k : Fin m → ℕ) :
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ‖∑ i : Fin m,
        a i • actualKernelBatchError P O (i.castLE hm) (k i) z‖ ^ 2
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) ≤
      ∑ i : Fin m, (a i) ^ 2 * (P.n : ℝ)⁻¹ *
        ∫ H : BatchHistory P d (i.castLE hm),
          ∫ ξ : Seed,
            ‖kernelPhi P (k i)
              (O.response (batchDecision P (i.castLE hm) H) ξ -
                batchCenter P (i.castLE hm) H)‖ ^ 2
            ∂O.law ∂batchPastHistoryLaw P O (i.castLE hm) := by
  rw [finite_actualKernelBatchError_sq_eq_sum P O hm a k]
  apply Finset.sum_le_sum
  intro i hi
  have h := actualKernelBatchError_secondMoment_le P O
    (i.castLE hm) (k i)
  calc
    (a i) ^ 2 *
        (∫ z, ‖actualKernelBatchError P O (i.castLE hm) (k i) z‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw O (responseCount P)))) ≤
      (a i) ^ 2 * ((P.n : ℝ)⁻¹ *
        ∫ H : BatchHistory P d (i.castLE hm),
          ∫ ξ : Seed,
            ‖kernelPhi P (k i)
              (O.response (batchDecision P (i.castLE hm) H) ξ -
                batchCenter P (i.castLE hm) H)‖ ^ 2
            ∂O.law ∂batchPastHistoryLaw P O (i.castLE hm)) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by ring

end

end HeavyTailedNoise.UpperK1
