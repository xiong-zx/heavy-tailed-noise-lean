import HeavyTailedNoise.Upper.K1.InitialMemoryVariance
import HeavyTailedNoise.Upper.K1.InitialMemoryFirstSeedMoment
import HeavyTailedNoise.Upper.K1.InitialMemoryPhysicalScale

/-!
The literal initial batch makes the complete same-seed high-band sample
error uniformly small in L². This is an unconditional estimate under the
model's original centered p moment and the exact `nI` schedule.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

/-- A fixed first-response center: one combined high-band batch error costs
the residual p moment times the terminal cutoff factor. -/
theorem Admissible.paperSchedule_initialMemory_fixedBatch_secondMoment_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    (t : ℕ) (w : Point d) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    (hpos : 0 < initialResponses P) →
    (∫ seeds : Fin (initialResponses P) → Seed,
      ‖upperResidualBatchMean I.oracle (initialMemoryKernel P t) 0 w seeds -
        upperResidualSourceMean I.oracle (initialMemoryKernel P t) 0 w‖ ^ 2
      ∂freshSeedLaw I.oracle (initialResponses P)) ≤
      (initialResponses P : ℝ)⁻¹ *
        (P.tau ⟨P.J, Nat.lt_succ_self P.J⟩) ^ (2 - p) *
          ∫ ξ : Seed, ‖I.oracle.response 0 ξ - w‖ ^ p ∂I.oracle.law := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  dsimp only
  intro hpos
  let φ : Point d → Point d := initialMemoryKernel P t
  let τ : ℝ := P.tau ⟨P.J, Nat.lt_succ_self P.J⟩
  let a : ℝ := 2 - p
  have hτ : 0 < τ := P.tau_pos _
  have ha : 0 ≤ a := by dsimp [a]; linarith [I.p_range.2]
  have hscale : 0 ≤ τ ^ a := Real.rpow_nonneg hτ.le _
  have hRmem := Admissible.residual_memLp I 0 w
  have hp : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hRint : Integrable
      (fun ξ : Seed => ‖I.oracle.response 0 ξ - w‖ ^ p)
      I.oracle.law := by
    simpa only [ENNReal.toReal_ofReal hp.le] using
      (hRmem.integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top)
  have hresponse : Measurable (I.oracle.response 0) :=
    I.oracle.measurable_response.comp
      (measurable_const.prodMk measurable_id)
  have hWmeas : Measurable
      (fun ξ : Seed => φ (I.oracle.response 0 ξ - w)) :=
    (measurable_initialMemoryKernel P t).comp
      (hresponse.sub measurable_const)
  have hWsqMeas : Measurable
      (fun ξ : Seed => ‖φ (I.oracle.response 0 ξ - w)‖ ^ 2) :=
    hWmeas.norm.pow_const 2
  have hpoint (ξ : Seed) :
      ‖φ (I.oracle.response 0 ξ - w)‖ ^ 2 ≤
        τ ^ a * ‖I.oracle.response 0 ξ - w‖ ^ p := by
    exact paperSchedule_initialMemoryKernel_sq_le_residual_p
      p q Δ σ Lbar ε Ctail ch κ Cb CI I.p_range
      hε hch hκ hCb hCI t _
  have hWsqInt : Integrable
      (fun ξ : Seed => ‖φ (I.oracle.response 0 ξ - w)‖ ^ 2)
      I.oracle.law :=
    Integrable.mono_nonneg (hRint.const_mul (τ ^ a))
      hWsqMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => sq_nonneg _))
      (Filter.Eventually.of_forall hpoint)
  have hWbound :
      (∫ ξ : Seed, ‖φ (I.oracle.response 0 ξ - w)‖ ^ 2
        ∂I.oracle.law) ≤
      τ ^ a * ∫ ξ : Seed,
        ‖I.oracle.response 0 ξ - w‖ ^ p ∂I.oracle.law := by
    calc
      (∫ ξ : Seed, ‖φ (I.oracle.response 0 ξ - w)‖ ^ 2
        ∂I.oracle.law) ≤
          ∫ ξ : Seed,
            τ ^ a * ‖I.oracle.response 0 ξ - w‖ ^ p
            ∂I.oracle.law :=
        integral_mono hWsqInt (hRint.const_mul _) hpoint
      _ = _ := by rw [integral_const_mul]
  have href := upperResidualBatchMean_secondMoment_le_reference
    I.oracle φ (measurable_initialMemoryKernel P t)
    (initialMemoryKernelBound P t)
    (initialMemoryKernel_norm_le P t) 0 w w hpos
  have hφ0 : φ 0 = 0 := initialMemoryKernel_zero P t
  simp only [sub_self, hφ0, sub_zero] at href
  simpa only [mul_assoc] using
    href.trans (mul_le_mul_of_nonneg_left hWbound
      (inv_nonneg.mpr (Nat.cast_nonneg _)))

/-- For every fixed runtime time, the actual decaying initialization sample
error has the manuscript's physical L² scale. One seed supplies all bands. -/
theorem Admissible.paperSchedule_actualInitialMemory_secondMoment_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    (t : ℕ) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ‖actualInitialMemorySampleError P I.oracle z.2 t‖ ^ 2
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P)))) ≤
      4 * ε ^ 2 / CI := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  dsimp only
  by_cases hpos : 0 < initialResponses P
  · let τ : ℝ := P.tau ⟨P.J, Nat.lt_succ_self P.J⟩
    let a : ℝ := 2 - p
    let m : ℕ := initialResponses P
    letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
    letI : IsProbabilityMeasure (freshSeedLaw I.oracle m) :=
      freshSeedLaw_probability I.oracle m
    have hused : useInitialBatch P := by
      by_contra h
      have hzero : initialResponses P = 0 := by
        simp [initialResponses, h]
      omega
    have hm : m = P.nI := by
      simp [m, initialResponses, hused]
    let errorSq : Seed × (Fin m → Seed) → ℝ := fun z =>
      ‖initialMemoryErrorAtPair P I.oracle t z‖ ^ 2
    have hErrorInt : Integrable errorSq
        (I.oracle.law.prod (freshSeedLaw I.oracle m)) :=
      initialMemoryErrorAtPair_sq_integrable P I.oracle t
    have hLeftInt : Integrable
        (fun ξ₀ : Seed => ∫ seeds : Fin m → Seed,
          errorSq (ξ₀, seeds) ∂freshSeedLaw I.oracle m)
        I.oracle.law := hErrorInt.integral_prod_left
    have hResidualInt := Admissible.initialTwoSeedResidual_p_integrable I
    have hRightInt : Integrable
        (fun ξ₀ : Seed =>
          (m : ℝ)⁻¹ * τ ^ a *
            ∫ ξ : Seed,
              ‖I.oracle.response 0 ξ - I.oracle.response 0 ξ₀‖ ^ p
              ∂I.oracle.law)
        I.oracle.law :=
      hResidualInt.integral_prod_left.const_mul ((m : ℝ)⁻¹ * τ ^ a)
    have hfixed (ξ₀ : Seed) :
        (∫ seeds : Fin m → Seed,
          errorSq (ξ₀, seeds) ∂freshSeedLaw I.oracle m) ≤
        (m : ℝ)⁻¹ * τ ^ a *
          ∫ ξ : Seed,
            ‖I.oracle.response 0 ξ - I.oracle.response 0 ξ₀‖ ^ p
            ∂I.oracle.law := by
      exact Admissible.paperSchedule_initialMemory_fixedBatch_secondMoment_le I
        ε Ctail ch κ Cb CI hε hch hκ hCb hCI t
        (I.oracle.response 0 ξ₀) hpos
    have hpairBound := Admissible.initialTwoSeedResidual_p_integral_le I
    have hν : 0 < paperNu σ ε := paperNu_pos hε
    have hσpow : σ ^ p ≤ (paperNu σ ε) ^ p :=
      Real.rpow_le_rpow I.sigma_nonneg (le_max_left σ ε)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) I.p_range.1.le)
    have hmoment :
        (∫ z : Seed × Seed,
          ‖I.oracle.response 0 z.2 - I.oracle.response 0 z.1‖ ^ p
          ∂I.oracle.law.prod I.oracle.law) ≤
          4 * (paperNu σ ε) ^ p :=
      hpairBound.trans
        (mul_le_mul_of_nonneg_left hσpow (by norm_num))
    have hτpow : 0 ≤ τ ^ a := Real.rpow_nonneg (P.tau_pos _).le _
    have hcoef : 0 ≤ (m : ℝ)⁻¹ * τ ^ a :=
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hτpow
    have hscalar := paperSchedule_initialVarianceScale_le_epsilon_sq
      p q Δ σ Lbar ε Ctail ch κ Cb CI I.p_range
      hε hch hCb hCI
    rw [actualInitialMemorySampleError_secondMoment_eq_pair
      P I.oracle t hpos]
    calc
      (∫ ξ₀ : Seed,
        ∫ seeds : Fin m → Seed,
          errorSq (ξ₀, seeds) ∂freshSeedLaw I.oracle m
          ∂I.oracle.law) ≤
          ∫ ξ₀ : Seed,
            (m : ℝ)⁻¹ * τ ^ a *
              ∫ ξ : Seed,
                ‖I.oracle.response 0 ξ - I.oracle.response 0 ξ₀‖ ^ p
                ∂I.oracle.law ∂I.oracle.law :=
        integral_mono hLeftInt hRightInt hfixed
      _ = ((m : ℝ)⁻¹ * τ ^ a) *
          ∫ z : Seed × Seed,
            ‖I.oracle.response 0 z.2 - I.oracle.response 0 z.1‖ ^ p
            ∂I.oracle.law.prod I.oracle.law := by
        rw [integral_const_mul, integral_prod _ hResidualInt]
      _ ≤ ((m : ℝ)⁻¹ * τ ^ a) *
          (4 * (paperNu σ ε) ^ p) :=
        mul_le_mul_of_nonneg_left hmoment hcoef
      _ ≤ 4 * ε ^ 2 / CI := by
        rw [hm]
        dsimp only at hscalar
        calc
          ((P.nI : ℝ)⁻¹ * τ ^ a) *
              (4 * (paperNu σ ε) ^ p) =
              4 * ((paperNu σ ε) ^ p *
                (P.tau ⟨P.J, Nat.lt_succ_self P.J⟩) ^ (2 - p) *
                (P.nI : ℝ)⁻¹) := by dsimp [τ, a]; ring
          _ ≤ 4 * (ε ^ 2 / CI) :=
            mul_le_mul_of_nonneg_left hscalar (by norm_num)
          _ = 4 * ε ^ 2 / CI := by ring
  · have hzero : initialResponses P = 0 := Nat.eq_zero_of_not_pos hpos
    have hfun : (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        ‖actualInitialMemorySampleError P I.oracle z.2 t‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext z
      rw [actualInitialMemorySampleError_zero_of_no_initial P I.oracle
        z.2 t hzero]
      simp
    rw [hfun]
    have hzeroIntegral :
        (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          (0 : ℝ)
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw I.oracle (responseCount P)))) = 0 :=
      MeasureTheory.integral_zero _ ℝ
    calc
      (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
        (0 : ℝ)
        ∂((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw I.oracle (responseCount P)))) = 0 := hzeroIntegral
      _ ≤ 4 * ε ^ 2 / CI :=
        div_nonneg (mul_nonneg (by norm_num) (sq_nonneg ε)) hCI.le

/-- Uniformly average the decaying initial contribution over the exact
runtime horizon. The elapsed-time coefficient is inside the sample error at
each time; the average adds no hidden log or response. -/
theorem Admissible.paperSchedule_actualInitialMemory_average_secondMoment_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hκ : 0 < κ)
    (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    (P.T : ℝ)⁻¹ *
      ∑ u : Fin P.T,
        (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖actualInitialMemorySampleError P I.oracle z.2 (u.val + 1)‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw I.oracle (responseCount P)))) ≤
      4 * ε ^ 2 / CI := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  have hsum :
      (∑ u : Fin P.T,
        (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖actualInitialMemorySampleError P I.oracle z.2 (u.val + 1)‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw I.oracle (responseCount P))))) ≤
      ∑ _u : Fin P.T, (4 * ε ^ 2 / CI) := by
    apply Finset.sum_le_sum
    intro u hu
    exact Admissible.paperSchedule_actualInitialMemory_secondMoment_le I
      ε Ctail ch κ Cb CI hε hch hκ hCb hCI (u.val + 1)
  have hTpos : (0 : ℝ) < P.T := Nat.cast_pos.mpr P.T_pos
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr hTpos.le)
  calc
    (P.T : ℝ)⁻¹ *
      (∑ u : Fin P.T,
        (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖actualInitialMemorySampleError P I.oracle z.2 (u.val + 1)‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw I.oracle (responseCount P))))) ≤
      (P.T : ℝ)⁻¹ * ∑ _u : Fin P.T, (4 * ε ^ 2 / CI) := hscaled
    _ = 4 * ε ^ 2 / CI := by
      simp only [Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul]
      field_simp [ne_of_gt hTpos, ne_of_gt hCI] <;> ring

end

end HeavyTailedNoise.UpperK1
