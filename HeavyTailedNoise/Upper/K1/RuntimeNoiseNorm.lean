import HeavyTailedNoise.Upper.K1.RuntimeNoiseTimeAverage
import HeavyTailedNoise.Upper.Foundations.FiniteAverageL2

/-!
Convert the actual complete shared-source runtime-kernel seed-only `L²`
average to the `ENNReal` expected `L¹` average used in selected-output risk.
The generic finite-average inequality is reused; no second Cauchy proof or
new temporal-independence assumption is introduced.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem measurable_runtimeKernelNoise
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ) (ht : t ≤ P.T) :
    Measurable (runtimeKernelNoise P O t ht) := by
  unfold runtimeKernelNoise
  apply Finset.measurable_sum
  intro u hu
  exact (measurable_kernelBatchErrorAtHistory P O
    (u.castLE ht) (t - 1 - u.val)).comp
      ((measurable_batchHistoryOfRun P O (u.castLE ht)).prodMk
        ((measurable_batchSeedBlock P (u.castLE ht)).comp measurable_snd))

/-- At every fixed output time, the complete actual runtime kernel has a
second moment under the original seed law with a fixed private anchor. -/
theorem runtimeKernelNoise_seed_memLp_two
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (t : ℕ) (ht : t ≤ P.T) (r₀ : Fin P.T) :
    MemLp (fun seeds : Fin (responseCount P) → Seed =>
      runtimeKernelNoise P O t ht (r₀, seeds)) 2
      (freshSeedLaw O (responseCount P)) := by
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw O (responseCount P))
  let E := runtimeKernelNoise P O t ht
  let f : Fin P.T × (Fin (responseCount P) → Seed) → ENNReal :=
    fun z => ENNReal.ofReal (‖E z‖ ^ 2)
  have hEmeas : Measurable E := measurable_runtimeKernelNoise P O t ht
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp (hEmeas.norm.pow_const 2)
  have hind (r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
      f (r, seeds) = f (r₀, seeds) := by
    dsimp [f, E]
    rw [runtimeKernelNoise_private_independent P O t ht r r₀ seeds]
  have htransport := lintegral_private_independent P O f hf r₀ hind
  have hmem : MemLp E 2 μ := runtimeKernelNoise_memLp_two P O t ht
  have hsqInt : Integrable (fun z => ‖E z‖ ^ 2) μ :=
    hmem.norm.integrable_sq
  have hsqNonneg : 0 ≤ᵐ[μ] (fun z => ‖E z‖ ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg _)
  have hfiniteJoint : (∫⁻ z, f z ∂μ) < ⊤ := by
    change (∫⁻ z, ENNReal.ofReal (‖E z‖ ^ 2) ∂μ) < ⊤
    rw [← ofReal_integral_eq_lintegral_ofReal hsqInt hsqNonneg]
    finiteness
  have hfiniteSeed :
      (∫⁻ seeds, ENNReal.ofReal (‖E (r₀, seeds)‖ ^ 2)
        ∂freshSeedLaw O (responseCount P)) < ⊤ := by
    change (∫⁻ seeds, f (r₀, seeds)
      ∂freshSeedLaw O (responseCount P)) < ⊤
    rw [← htransport]
    exact hfiniteJoint
  have hseedMeas : Measurable
      (fun seeds : Fin (responseCount P) → Seed => E (r₀, seeds)) :=
    hEmeas.comp (measurable_const.prodMk measurable_id)
  have hseedSqInt : Integrable
      (fun seeds : Fin (responseCount P) → Seed =>
        ‖E (r₀, seeds)‖ ^ 2)
      (freshSeedLaw O (responseCount P)) := by
    have hsqMeas : Measurable
        (fun seeds : Fin (responseCount P) → Seed =>
          ‖E (r₀, seeds)‖ ^ 2) := hseedMeas.norm.pow_const 2
    refine ⟨hsqMeas.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun seeds => sq_nonneg _))).2
        hfiniteSeed
  apply (integrable_norm_rpow_iff hseedMeas.aestronglyMeasurable
    (p := (2 : ENNReal)) (by norm_num) (by norm_num)).mp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hseedSqInt

/-- A coefficient budget of `1/32²` gives the final seed-only runtime-noise
mean norm budget `ε/32`.  Root's deterministic constant choice discharges
the displayed scalar premise. -/
theorem Admissible.paperSchedule_runtimeKernelNoise_norm_seed_average_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    (hbudget :
      (2 * (1 + physicalResidualTrackerConstant p) *
        physicalKernelNoiseConstant p q κ) / Cb ≤ (1 / 32 : ℝ) ^ 2) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    (P.T : ENNReal)⁻¹ *
      (∫⁻ seeds : Fin (responseCount P) → Seed,
        ENNReal.ofReal
          (∑ t : Fin P.T,
            ‖runtimeKernelNoise P I.oracle (t.val + 1)
              (Nat.succ_le_iff.mpr t.isLt)
              (⟨0, P.T_pos⟩, seeds)‖)
        ∂freshSeedLaw I.oracle (responseCount P)) ≤
      ENNReal.ofReal (ε / 32) := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let μ := freshSeedLaw I.oracle (responseCount P)
  let E : Fin P.T → (Fin (responseCount P) → Seed) → Point d :=
    fun t seeds => runtimeKernelNoise P I.oracle (t.val + 1)
      (Nat.succ_le_iff.mpr t.isLt) (⟨0, P.T_pos⟩, seeds)
  letI : IsProbabilityMeasure μ :=
    freshSeedLaw_probability I.oracle (responseCount P)
  have hmem (t : Fin P.T) : MemLp (E t) 2 μ :=
    runtimeKernelNoise_seed_memLp_two P I.oracle
      (t.val + 1) (Nat.succ_le_iff.mpr t.isLt) ⟨0, P.T_pos⟩
  have hsecondBase :=
    Admissible.paperSchedule_runtimeKernelNoise_sq_seed_average_le
      I ε Ctail κ Cb CI hε hκ hCb hCI
  change (P.T : ℝ)⁻¹ *
    (∑ t : Fin P.T, ∫ seeds, ‖E t seeds‖ ^ 2 ∂μ) ≤
    (2 * (1 + physicalResidualTrackerConstant p) *
      physicalKernelNoiseConstant p q κ) * ε ^ 2 / Cb at hsecondBase
  have hscale :
      (2 * (1 + physicalResidualTrackerConstant p) *
        physicalKernelNoiseConstant p q κ) * ε ^ 2 / Cb ≤
      (ε / 32) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hbudget (sq_nonneg ε)
    calc
      _ = ((2 * (1 + physicalResidualTrackerConstant p) *
          physicalKernelNoiseConstant p q κ) / Cb) * ε ^ 2 := by ring
      _ ≤ (1 / 32 : ℝ) ^ 2 * ε ^ 2 := hmul
      _ = (ε / 32) ^ 2 := by ring
  have hsecond :
      (∑ t : Fin P.T, ∫ seeds, ‖E t seeds‖ ^ 2 ∂μ) /
        (P.T : ℝ) ≤ (ε / 32) ^ 2 := by
    have hreal : (P.T : ℝ)⁻¹ *
      (∑ t : Fin P.T, ∫ seeds, ‖E t seeds‖ ^ 2 ∂μ) =
      (∑ t : Fin P.T, ∫ seeds, ‖E t seeds‖ ^ 2 ∂μ) /
        (P.T : ℝ) := by ring
    rw [← hreal]
    exact hsecondBase.trans hscale
  have hmain := finite_average_l2_to_l1 μ P.T_pos E hmem
    (a := ε / 32) (by positivity) hsecond
  simpa only [E, μ] using hmain

end

end HeavyTailedNoise.UpperK1
