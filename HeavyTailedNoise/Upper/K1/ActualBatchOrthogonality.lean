import HeavyTailedNoise.Upper.K1.ActualBatchOrthogonalityFoundations

/-!
Cross-time orthogonality of complete shared-kernel runtime-batch errors.
The earlier error is measurable from the later batch's full pre-batch
transcript; the later error has zero conditional mean at that exact boundary.
No independence is asserted among clipping scales within one response.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {q : ℝ} (P : Schedule q)

private def realInnerBilin (d : ℕ) :
    Point d →L[ℝ] Point d →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (innerₗ (Point d)) 1 (fun x y => by
    simpa only [innerₗ_apply_apply, one_mul] using
      (norm_inner_le_norm x y))

/-- Distinct runtime batches are orthogonal in expectation as whole-vector
centered `Φ` errors. The lags may differ; within a batch every clipping scale
continues to share the same oracle responses. -/
theorem actualKernelBatchError_crossTime_inner_zero
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u v : Fin P.T)
    (huv : u.val < v.val) (ku kv : ℕ) :
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ⟪actualKernelBatchError P O u ku z,
        actualKernelBatchError P O v kv z⟫_ℝ
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) = 0 := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw O (responseCount P)) :=
    freshSeedLaw_probability O (responseCount P)
  letI : MeasurableSpace (Fin P.T × (Fin (responseCount P) → Seed)) :=
    Prod.instMeasurableSpace
  letI : MeasurableSpace (BatchHistory P d v) :=
    Prod.instMeasurableSpace
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw O (responseCount P))
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let m := MeasurableSpace.comap
    (batchHistoryOfRun (d := d) P O v)
    (Prod.instMeasurableSpace : MeasurableSpace (BatchHistory P d v))
  let early := actualKernelBatchError P O u ku
  let late := actualKernelBatchError P O v kv
  have hm : m ≤ (Prod.instMeasurableSpace : MeasurableSpace
      (Fin P.T × (Fin (responseCount P) → Seed))) := by
    change MeasurableSpace.comap (batchHistoryOfRun (d := d) P O v)
      (Prod.instMeasurableSpace : MeasurableSpace (BatchHistory P d v)) ≤ _
    exact (measurable_batchHistoryOfRun P O v).comap_le
  have hEarlyMeas : Measurable[m] early :=
    actualEarlierKernelError_measurable_prebatch P O u v huv ku
  have hEarlyLp : MemLp early 2 μ := actualKernelBatchError_memLp_two P O u ku
  have hLateLp : MemLp late 2 μ := actualKernelBatchError_memLp_two P O v kv
  letI : ENNReal.HolderTriple 2 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have hnormProd : MemLp (fun z => ‖early z‖ * ‖late z‖) 1 μ := by
    exact hEarlyLp.norm.mul hLateLp.norm
  have hnormProdInt : Integrable (fun z => ‖early z‖ * ‖late z‖) μ :=
    memLp_one_iff_integrable.mp hnormProd
  have hEarlyAmbient : @Measurable
      (Fin P.T × (Fin (responseCount P) → Seed)) (Point d)
      (Prod.instMeasurableSpace : MeasurableSpace
        (Fin P.T × (Fin (responseCount P) → Seed)))
      (inferInstance : MeasurableSpace (Point d)) early :=
    hEarlyMeas.mono hm le_rfl
  have hLateAmbient : @Measurable
      (Fin P.T × (Fin (responseCount P) → Seed)) (Point d)
      (Prod.instMeasurableSpace : MeasurableSpace
        (Fin P.T × (Fin (responseCount P) → Seed)))
      (inferInstance : MeasurableSpace (Point d)) late :=
    (measurable_kernelBatchErrorAtHistory P O v kv).comp
      ((measurable_batchHistoryOfRun P O v).prodMk
        ((measurable_batchSeedBlock P v).comp measurable_snd))
  have hinnerMeas : @Measurable
      (Fin P.T × (Fin (responseCount P) → Seed)) ℝ
      (Prod.instMeasurableSpace : MeasurableSpace
        (Fin P.T × (Fin (responseCount P) → Seed)))
      (inferInstance : MeasurableSpace ℝ)
      (fun z => ⟪early z, late z⟫_ℝ) :=
    Measurable.inner (𝕜 := ℝ) hEarlyAmbient hLateAmbient
  have hinnerInt : Integrable (fun z => ⟪early z, late z⟫_ℝ) μ := by
    apply Integrable.mono' hnormProdInt hinnerMeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs]
      exact abs_real_inner_le_norm _ _)
  have hLateInt : Integrable late μ :=
    memLp_one_iff_integrable.mp
      (hLateLp.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2))
  let B := realInnerBilin (d := d)
  have hpull := condExp_bilin_of_aestronglyMeasurable_left B
    hEarlyMeas.aestronglyMeasurable hinnerInt hLateInt
  have hlateZero := actualKernelBatchError_condExp_prebatch_zero P O v kv
  have hcondZero :
      μ[(fun z => ⟪early z, late z⟫_ℝ) | m] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hlateZero] with z hp hz
    change (μ[(fun z => ⟪early z, late z⟫_ℝ) | m]) z = (0 : ℝ)
    change (μ[(fun z => ⟪early z, late z⟫_ℝ) | m]) z =
      ⟪early z, (μ[late | m]) z⟫_ℝ at hp
    rw [hz] at hp
    simpa only [Pi.zero_apply, inner_zero_right] using hp
  calc
    (∫ z, ⟪early z, late z⟫_ℝ ∂μ) =
        ∫ z, (μ[(fun z => ⟪early z, late z⟫_ℝ) | m]) z ∂μ :=
          (integral_condExp (μ := μ)
            (f := fun z => ⟪early z, late z⟫_ℝ) hm).symm
    _ = 0 := by
      rw [integral_congr_ae hcondZero]
      simp

end

end HeavyTailedNoise.UpperK1
