import HeavyTailedNoise.Upper.K1.InitialMemoryRadial
import HeavyTailedNoise.Upper.K1.SameSeedMomentLp
import HeavyTailedNoise.Upper.K1.CoarseTrackerMomentFromExp

/-!
Two independent fresh seeds at the initial point give a residual about the
first observed response. Its unconditional p moment follows from the
original centered p-BCM alone, including `σ=0`; no moment of an adaptive
raw residual is postulated.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem Admissible.initialTwoSeedResidual_p_integrable
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar) :
    Integrable (fun z : Seed × Seed =>
      ‖I.oracle.response 0 z.2 - I.oracle.response 0 z.1‖ ^ p)
      (I.oracle.law.prod I.oracle.law) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  let G : Seed → Point d := fun ξ =>
    I.oracle.response 0 ξ - I.objective.grad 0
  have hGmem : MemLp G (ENNReal.ofReal p) I.oracle.law :=
    Admissible.centered_response_memLp I 0
  have hRmem : MemLp
      (fun z : Seed × Seed => G z.2 - G z.1)
      (ENNReal.ofReal p) (I.oracle.law.prod I.oracle.law) :=
    (hGmem.comp_snd I.oracle.law).sub
      (hGmem.comp_fst I.oracle.law)
  have hp : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hInt := hRmem.integrable_norm_rpow
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  have hfun : (fun z : Seed × Seed =>
      I.oracle.response 0 z.2 - I.oracle.response 0 z.1) =
      (fun z : Seed × Seed => G z.2 - G z.1) := by
    funext z
    dsimp [G]
    abel
  have hpoint (z : Seed × Seed) :
      I.oracle.response 0 z.2 - I.oracle.response 0 z.1 =
        G z.2 - G z.1 := congrFun hfun z
  simpa only [hpoint, ENNReal.toReal_ofReal hp.le] using hInt

/-- The seed-zero center and one independent seed have an unconditional
residual p moment at most `4 σ^p` for `1<p≤2`. -/
theorem Admissible.initialTwoSeedResidual_p_integral_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar) :
    (∫ z : Seed × Seed,
      ‖I.oracle.response 0 z.2 - I.oracle.response 0 z.1‖ ^ p
      ∂I.oracle.law.prod I.oracle.law) ≤ 4 * σ ^ p := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  let μ := I.oracle.law.prod I.oracle.law
  let G : Seed → Point d := fun ξ =>
    I.oracle.response 0 ξ - I.objective.grad 0
  let R : Seed × Seed → Point d := fun z => G z.2 - G z.1
  let F : Seed × Seed → ℝ := fun z => ‖R z‖ ^ p
  let B : Seed × Seed → ℝ := fun z =>
    2 * (‖G z.2‖ ^ p + ‖G z.1‖ ^ p)
  have hp : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hpENN : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal I.p_range.1.le
  have hGmem : MemLp G (ENNReal.ofReal p) I.oracle.law :=
    Admissible.centered_response_memLp I 0
  have hGint : Integrable (fun ξ : Seed => ‖G ξ‖ ^ p) I.oracle.law := by
    simpa only [ENNReal.toReal_ofReal hp.le] using
      (hGmem.integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top)
  have hfstMem : MemLp (fun z : Seed × Seed => G z.1)
      (ENNReal.ofReal p) μ := hGmem.comp_fst I.oracle.law
  have hsndMem : MemLp (fun z : Seed × Seed => G z.2)
      (ENNReal.ofReal p) μ := hGmem.comp_snd I.oracle.law
  have hRmem : MemLp R (ENNReal.ofReal p) μ := hsndMem.sub hfstMem
  have hFint : Integrable F μ := by
    simpa only [F, ENNReal.toReal_ofReal hp.le] using
      (hRmem.integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top)
  have hfstInt : Integrable (fun z : Seed × Seed => ‖G z.1‖ ^ p) μ :=
    hGint.comp_fst I.oracle.law
  have hsndInt : Integrable (fun z : Seed × Seed => ‖G z.2‖ ^ p) μ :=
    hGint.comp_snd I.oracle.law
  have hBint : Integrable B μ := (hsndInt.add hfstInt).const_mul 2
  have hpoint (z : Seed × Seed) : F z ≤ B z := by
    have hnorm : ‖R z‖ ≤ ‖G z.2‖ + ‖G z.1‖ :=
      norm_sub_le _ _
    have hpow : ‖R z‖ ^ p ≤ (‖G z.2‖ + ‖G z.1‖) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm hp.le
    exact hpow.trans (add_rpow_le_two_sum I.p_range.1.le
      I.p_range.2 (norm_nonneg _) (norm_nonneg _))
  have hGmeas : StronglyMeasurable (fun ξ : Seed => ‖G ξ‖ ^ p) := by
    have hresponse : Measurable (I.oracle.response 0) :=
      I.oracle.measurable_response.comp
        (measurable_const.prodMk measurable_id)
    have hG : Measurable G := hresponse.sub measurable_const
    exact ((Real.continuous_rpow_const hp.le).measurable.comp
      hG.norm).stronglyMeasurable
  have hfst :
      (∫ z : Seed × Seed, ‖G z.1‖ ^ p ∂μ) =
        ∫ ξ : Seed, ‖G ξ‖ ^ p ∂I.oracle.law := by
    have hmap : MeasurePreserving (Prod.fst : Seed × Seed → Seed)
        μ I.oracle.law := measurePreserving_fst
    rw [← hmap.map_eq]
    exact (integral_map_of_stronglyMeasurable
      hmap.measurable hGmeas).symm
  have hsnd :
      (∫ z : Seed × Seed, ‖G z.2‖ ^ p ∂μ) =
        ∫ ξ : Seed, ‖G ξ‖ ^ p ∂I.oracle.law := by
    have hmap : MeasurePreserving (Prod.snd : Seed × Seed → Seed)
        μ I.oracle.law := measurePreserving_snd
    rw [← hmap.map_eq]
    exact (integral_map_of_stronglyMeasurable
      hmap.measurable hGmeas).symm
  have hsingle : (∫ ξ : Seed, ‖G ξ‖ ^ p ∂I.oracle.law) ≤
      σ ^ p := by
    have hnonneg : 0 ≤ᵐ[I.oracle.law]
        (fun ξ : Seed => ‖G ξ‖ ^ p) :=
      Filter.Eventually.of_forall (fun ξ =>
        Real.rpow_nonneg (norm_nonneg _) _)
    have hreal : ENNReal.ofReal
        (∫ ξ : Seed, ‖G ξ‖ ^ p ∂I.oracle.law) =
        ∫⁻ ξ : Seed, ENNReal.ofReal (‖G ξ‖ ^ p) ∂I.oracle.law :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGint hnonneg
    apply (ENNReal.ofReal_le_ofReal_iff
      (Real.rpow_nonneg I.sigma_nonneg p)).mp
    rw [hreal]
    exact I.centered_moment 0
  have hrepr :
      (fun z : Seed × Seed =>
        ‖I.oracle.response 0 z.2 - I.oracle.response 0 z.1‖ ^ p) =
      F := by
    funext z
    congr 1
    dsimp [R, G]
    abel
  rw [hrepr]
  calc
    (∫ z : Seed × Seed, F z ∂μ) ≤ ∫ z, B z ∂μ :=
      integral_mono hFint hBint hpoint
    _ = 4 * ∫ ξ : Seed, ‖G ξ‖ ^ p ∂I.oracle.law := by
      dsimp only [B]
      rw [integral_const_mul, integral_add hsndInt hfstInt, hsnd, hfst]
      ring
    _ ≤ 4 * σ ^ p := mul_le_mul_of_nonneg_left hsingle (by norm_num)

end

end HeavyTailedNoise.UpperK1
