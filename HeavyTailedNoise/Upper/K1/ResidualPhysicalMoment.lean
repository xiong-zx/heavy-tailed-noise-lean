import HeavyTailedNoise.Upper.K1.CoarseTrackerPaperScheduleScale
import HeavyTailedNoise.Upper.K1.CoarseTrackerPredictableWeight
import HeavyTailedNoise.Upper.K1.CoarseTrackerMomentFromExp

/-!
The original centered oracle moment, rather than a new residual-oracle
assumption, supplies the residual moment on each actual pre-batch history
times one independent fresh seed.  The only outer random scale is the
canonical tracker error.  This includes `σ = 0`, `q = 1`, and `p = 2`.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

/-- The physical tracker-moment coefficient, depending only on `p`. -/
def physicalResidualTrackerConstant (p : ℝ) : ℝ :=
  4 * (1 + (36 : ℝ) ^ p + 815 * (243 / 8 : ℝ) ^ p)

/-- Fully applied readout of the actual pre-batch residual, kept opaque at
schedule-specialized theorem declarations to avoid expanding the entire
literal schedule while elaborating their dependent types. -/
def actualResidualPower
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (P : Schedule q)
    (I : Admissible d Seed p q Δ σ Lbar) (u : Fin P.T)
    (z : BatchHistory P d u × Seed) : ℝ :=
  ‖I.oracle.response (batchDecision P u z.1) z.2 -
    batchCenter P u z.1‖ ^ p

irreducible_def actualResidualMoment
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (P : Schedule q)
    (I : Admissible d Seed p q Δ σ Lbar) (u : Fin P.T) : ENNReal :=
  ∫⁻ z : BatchHistory P d u × Seed,
    ENNReal.ofReal (actualResidualPower P I u z)
    ∂((batchPastHistoryLaw P I.oracle u).prod I.oracle.law)

theorem actualResidualMoment_eq
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (P : Schedule q)
    (I : Admissible d Seed p q Δ σ Lbar) (u : Fin P.T) :
    actualResidualMoment P I u =
      ∫⁻ z : BatchHistory P d u × Seed,
        ENNReal.ofReal (actualResidualPower P I u z)
        ∂((batchPastHistoryLaw P I.oracle u).prod I.oracle.law) := by
  simp only [actualResidualMoment]

/-! The new generic Tonelli lemma has no schedule, algorithm, transcript, or
history-map dependency. -/
theorem Admissible.joint_residual_p_lintegral_le
    {d : ℕ} {Seed History : Type*}
    [MeasurableSpace Seed] [MeasurableSpace History]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (μ : Measure History) [IsProbabilityMeasure μ]
    (x w : History → Point d) (hx : Measurable x) (hw : Measurable w)
    (M : ENNReal)
    (htracker :
      (∫⁻ H, ENNReal.ofReal
        (‖w H - I.objective.grad (x H)‖ ^ p) ∂μ) ≤
        M) :
    (∫⁻ z : History × Seed,
      ENNReal.ofReal (‖I.oracle.response (x z.1) z.2 - w z.1‖ ^ p)
      ∂μ.prod I.oracle.law) ≤
      (2 : ENNReal) * (ENNReal.ofReal (σ ^ p) + M) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  let A : History × Seed → ℝ := fun z =>
    ‖I.oracle.response (x z.1) z.2 - I.objective.grad (x z.1)‖ ^ p
  let E : History → ℝ := fun H =>
    ‖w H - I.objective.grad (x H)‖ ^ p
  let F : History × Seed → ℝ := fun z =>
    ‖I.oracle.response (x z.1) z.2 - w z.1‖ ^ p
  have hp : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hresponse : Measurable (fun z : History × Seed =>
      I.oracle.response (x z.1) z.2) :=
    I.oracle.measurable_response.comp
      ((hx.comp measurable_fst).prodMk measurable_snd)
  have hgrad : Measurable (fun H => I.objective.grad (x H)) :=
    I.objective.continuous_grad.measurable.comp hx
  have hAmeas : Measurable (fun z => ENNReal.ofReal (A z)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_rpow_const hp.le).measurable.comp
        (hresponse.sub (hgrad.comp measurable_fst)).norm)
  have hEmeas : Measurable (fun H => ENNReal.ofReal (E H)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_rpow_const hp.le).measurable.comp
        (hw.sub hgrad).norm)
  have hFmeas : Measurable (fun z => ENNReal.ofReal (F z)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_rpow_const hp.le).measurable.comp
        (hresponse.sub (hw.comp measurable_fst)).norm)
  have hA0 (z : History × Seed) : 0 ≤ A z := by dsimp [A]; positivity
  have hE0 (H : History) : 0 ≤ E H := by dsimp [E]; positivity
  have hpoint (H : History) (ξ : Seed) :
      ENNReal.ofReal (F (H, ξ)) ≤
        (2 : ENNReal) *
          (ENNReal.ofReal (A (H, ξ)) + ENNReal.ofReal (E H)) := by
    have hvec : I.oracle.response (x H) ξ - w H =
        (I.oracle.response (x H) ξ - I.objective.grad (x H)) -
          (w H - I.objective.grad (x H)) := by abel
    have hnorm : ‖I.oracle.response (x H) ξ - w H‖ ≤
        ‖I.oracle.response (x H) ξ - I.objective.grad (x H)‖ +
          ‖w H - I.objective.grad (x H)‖ := by
      rw [hvec]
      exact norm_sub_le
          (I.oracle.response (x H) ξ - I.objective.grad (x H))
          (w H - I.objective.grad (x H))
    have hpow := Real.rpow_le_rpow
      (norm_nonneg (I.oracle.response (x H) ξ - w H)) hnorm hp.le
    have hadd := add_rpow_le_two_sum I.p_range.1.le I.p_range.2
      (norm_nonneg
        (I.oracle.response (x H) ξ - I.objective.grad (x H)))
      (norm_nonneg (w H - I.objective.grad (x H)))
    have hreal : F (H, ξ) ≤ 2 * (A (H, ξ) + E H) :=
      hpow.trans hadd
    calc
      ENNReal.ofReal (F (H, ξ)) ≤
          ENNReal.ofReal (2 * (A (H, ξ) + E H)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = (2 : ENNReal) *
          (ENNReal.ofReal (A (H, ξ)) + ENNReal.ofReal (E H)) := by
        rw [ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_add (hA0 (H, ξ)) (hE0 H)]
        norm_num
  have hinner (H : History) :
      (∫⁻ ξ : Seed, ENNReal.ofReal (F (H, ξ)) ∂I.oracle.law) ≤
        (2 : ENNReal) *
          (ENNReal.ofReal (σ ^ p) + ENNReal.ofReal (E H)) := by
    calc
      _ ≤ ∫⁻ ξ : Seed,
          (2 : ENNReal) *
            (ENNReal.ofReal (A (H, ξ)) + ENNReal.ofReal (E H))
          ∂I.oracle.law := lintegral_mono (hpoint H)
      _ = (2 : ENNReal) *
          ((∫⁻ ξ : Seed, ENNReal.ofReal (A (H, ξ)) ∂I.oracle.law) +
            ENNReal.ofReal (E H)) := by
        have hAm : Measurable
            (fun ξ : Seed => ENNReal.ofReal (A (H, ξ))) := by
          simpa only [Function.comp_def, id_eq] using
            (hAmeas.comp (measurable_const.prodMk measurable_id))
        rw [lintegral_const_mul' (2 : ENNReal) _ (by simp)]
        rw [lintegral_add_left hAm]
        simp
      _ ≤ (2 : ENNReal) *
          (ENNReal.ofReal (σ ^ p) + ENNReal.ofReal (E H)) := by
        have hcenter :
            (∫⁻ ξ : Seed, ENNReal.ofReal (A (H, ξ)) ∂I.oracle.law) ≤
              ENNReal.ofReal (σ ^ p) := by
          simpa only [A] using I.centered_moment (x H)
        exact mul_le_mul_of_nonneg_left
          (add_le_add hcenter le_rfl)
          (by simp)
  have houter :
      (∫⁻ H : History,
        (2 : ENNReal) *
          (ENNReal.ofReal (σ ^ p) + ENNReal.ofReal (E H)) ∂μ) ≤
        (2 : ENNReal) * (ENNReal.ofReal (σ ^ p) + M) := by
    calc
      _ = (2 : ENNReal) *
          (ENNReal.ofReal (σ ^ p) +
            ∫⁻ H : History, ENNReal.ofReal (E H) ∂μ) := by
        rw [lintegral_const_mul' (2 : ENNReal) _ (by simp)]
        rw [lintegral_add_left measurable_const]
        simp
      _ ≤ (2 : ENNReal) *
          (ENNReal.ofReal (σ ^ p) + M) := by
        have htrack :
            (∫⁻ H : History, ENNReal.ofReal (E H) ∂μ) ≤ M := by
          simpa only [E] using htracker
        exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl htrack) (by simp)
  change (∫⁻ z, ENNReal.ofReal (F z) ∂μ.prod I.oracle.law) ≤ _
  rw [lintegral_prod _ hFmeas.aemeasurable]
  exact (lintegral_mono hinner).trans houter

/-- Under the unchanged literal schedule, the original oracle and the
actual tracker imply the unconditional residual `p` moment. -/
theorem Admissible.paperSchedule_actualResidual_p_moment_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    ∀ u : Fin P.T,
      actualResidualMoment P I u ≤
        ENNReal.ofReal
          (2 * (1 + physicalResidualTrackerConstant p) *
            (paperNu σ ε) ^ p) := by
  dsimp only
  intro u
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let μpast := batchPastHistoryLaw P I.oracle u
  let μglobal := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  let x : BatchHistory P d u → Point d := batchDecision P u
  let w : BatchHistory P d u → Point d := batchCenter P u
  let E : BatchHistory P d u → ℝ := fun H =>
    ‖w H - I.objective.grad (x H)‖ ^ p
  let M := physicalResidualTrackerConstant p * (paperNu σ ε) ^ p
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure μpast := by
    dsimp [μpast, batchPastHistoryLaw]
    infer_instance
  have hx : Measurable x := measurable_batchDecision P u
  have hw : Measurable w := measurable_batchCenter P u
  have hp : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hEmeas : Measurable (fun H => ENNReal.ofReal (E H)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_rpow_const hp.le).measurable.comp
        (hw.sub (I.objective.continuous_grad.measurable.comp hx)).norm)
  have hEcomp (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      E (batchHistoryOfRun P I.oracle u z) =
        (actualTrackerAtBoundary P I u.val z) ^ p := by
    have h := actualTrackerAtBoundary_eq_history P I u z
    dsimp [E, x, w, trackerError]
    rw [h]
    rfl
  have hmap := measurePreserving_actualBatchHistory P I.oracle u
  have htracker := Admissible.paperSchedule_eighth_tracker_p_moment_le_nu
    I ε Ctail κ Cb CI hε hCb hCI u.val (Nat.le_of_lt u.isLt)
  change Integrable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        (actualTrackerAtBoundary P I u.val z) ^ p) μglobal ∧
    (∫ z, (actualTrackerAtBoundary P I u.val z) ^ p ∂μglobal) ≤
      M at htracker
  have hglobalNNR :
      (∫⁻ z, ENNReal.ofReal
        ((actualTrackerAtBoundary P I u.val z) ^ p) ∂μglobal) ≤
        ENNReal.ofReal M := by
    have hnonneg : 0 ≤ᵐ[μglobal]
        (fun z => (actualTrackerAtBoundary P I u.val z) ^ p) :=
      Filter.Eventually.of_forall fun z =>
        Real.rpow_nonneg (actualTrackerAtBoundary_nonneg P I u.val z) _
    rw [← ofReal_integral_eq_lintegral_ofReal htracker.1 hnonneg]
    exact ENNReal.ofReal_le_ofReal htracker.2
  have hhistoryNNR :
      (∫⁻ H, ENNReal.ofReal (E H) ∂μpast) ≤ ENNReal.ofReal M := by
    have htransport := hmap.lintegral_comp hEmeas
    rw [← htransport]
    simpa only [hEcomp] using hglobalNNR
  have hgeneric := Admissible.joint_residual_p_lintegral_le
    I μpast x w hx hw (ENNReal.ofReal M) hhistoryNNR
  have hσpow : σ ^ p ≤ (paperNu σ ε) ^ p :=
    Real.rpow_le_rpow I.sigma_nonneg (le_max_left σ ε) hp.le
  have hM0 : 0 ≤ M := by
    have hCR : 0 ≤ physicalResidualTrackerConstant p := by
      dsimp [physicalResidualTrackerConstant]
      positivity
    exact mul_nonneg hCR
      (Real.rpow_nonneg (paperNu_pos hε).le _)
  have hscalar : 2 * (σ ^ p + M) ≤
      2 * (1 + physicalResidualTrackerConstant p) *
        (paperNu σ ε) ^ p := by
    dsimp [M]
    nlinarith [hσpow]
  calc
    actualResidualMoment P I u =
        ∫⁻ z : BatchHistory P d u × Seed,
          ENNReal.ofReal (actualResidualPower P I u z)
          ∂((batchPastHistoryLaw P I.oracle u).prod I.oracle.law) :=
      actualResidualMoment_eq P I u
    _ ≤ (2 : ENNReal) *
        (ENNReal.ofReal (σ ^ p) + ENNReal.ofReal M) := by
      simpa only [actualResidualPower, x, w, μpast] using hgeneric
    _ = ENNReal.ofReal (2 * (σ ^ p + M)) := by
      have hsum : ENNReal.ofReal (σ ^ p + M) =
          ENNReal.ofReal (σ ^ p) + ENNReal.ofReal M :=
        ENNReal.ofReal_add (Real.rpow_nonneg I.sigma_nonneg _) hM0
      have htwo : ENNReal.ofReal (2 * (σ ^ p + M)) =
          (2 : ENNReal) * ENNReal.ofReal (σ ^ p + M) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      rw [← hsum]
      exact htwo.symm
    _ ≤ ENNReal.ofReal
        (2 * (1 + physicalResidualTrackerConstant p) *
          (paperNu σ ε) ^ p) := ENNReal.ofReal_le_ofReal hscalar

/-- Real-integral form of the same unconditional residual moment. -/
theorem Admissible.paperSchedule_actualResidual_p_integrable_bound
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    ∀ u : Fin P.T,
      Integrable (actualResidualPower P I u)
        ((batchPastHistoryLaw P I.oracle u).prod I.oracle.law) ∧
      (∫ z, actualResidualPower P I u z
          ∂((batchPastHistoryLaw P I.oracle u).prod I.oracle.law)) ≤
        2 * (1 + physicalResidualTrackerConstant p) *
          (paperNu σ ε) ^ p := by
  dsimp only
  intro u
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let μ := (batchPastHistoryLaw P I.oracle u).prod I.oracle.law
  let R : BatchHistory P d u × Seed → ℝ := fun z =>
    ‖I.oracle.response (batchDecision P u z.1) z.2 -
      batchCenter P u z.1‖ ^ p
  have hp : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hRmeas : Measurable R := by
    have hr : Measurable (fun z : BatchHistory P d u × Seed =>
        I.oracle.response (batchDecision P u z.1) z.2 -
          batchCenter P u z.1) :=
      (I.oracle.measurable_response.comp
        (((measurable_batchDecision P u).comp measurable_fst).prodMk
          measurable_snd)).sub
        ((measurable_batchCenter P u).comp measurable_fst)
    exact (Real.continuous_rpow_const hp.le).measurable.comp hr.norm
  have hRnonneg (z : BatchHistory P d u × Seed) : 0 ≤ R z := by
    dsimp [R]
    positivity
  have hmoment : (∫⁻ z, ENNReal.ofReal (R z) ∂μ) ≤
      ENNReal.ofReal
        (2 * (1 + physicalResidualTrackerConstant p) *
          (paperNu σ ε) ^ p) :=
    by
      have h := Admissible.paperSchedule_actualResidual_p_moment_le
        I ε Ctail κ Cb CI hε hCb hCI u
      rw [actualResidualMoment_eq] at h
      change (∫⁻ z, ENNReal.ofReal (R z) ∂μ) ≤ _ at h
      exact h
  have hfinite : (∫⁻ z, ENNReal.ofReal (R z) ∂μ) < (⊤ : ENNReal) :=
    lt_of_le_of_lt hmoment (by finiteness)
  have hRint : Integrable R μ :=
    ⟨hRmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall hRnonneg)).2 hfinite⟩
  have hboundNonneg : 0 ≤
      2 * (1 + physicalResidualTrackerConstant p) *
        (paperNu σ ε) ^ p := by
    have hCR : 0 ≤ physicalResidualTrackerConstant p := by
      dsimp [physicalResidualTrackerConstant]
      positivity
    exact mul_nonneg
      (mul_nonneg (by norm_num) (add_nonneg (by norm_num) hCR))
      (Real.rpow_nonneg (paperNu_pos hε).le _)
  have hRbound : (∫ z, R z ∂μ) ≤
      2 * (1 + physicalResidualTrackerConstant p) *
        (paperNu σ ε) ^ p := by
    apply (ENNReal.ofReal_le_ofReal_iff hboundNonneg).mp
    calc
      ENNReal.ofReal (∫ z, R z ∂μ) =
          ∫⁻ z, ENNReal.ofReal (R z) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hRint
          (Filter.Eventually.of_forall hRnonneg)
      _ ≤ _ := hmoment
  have hRreadout :
      (fun z : BatchHistory P d u × Seed => actualResidualPower P I u z) =
        R := by
    funext z
    rfl
  change Integrable
      (fun z : BatchHistory P d u × Seed => actualResidualPower P I u z) μ ∧
    (∫ z, actualResidualPower P I u z ∂μ) ≤
      2 * (1 + physicalResidualTrackerConstant p) *
        (paperNu σ ε) ^ p
  rw [hRreadout]
  exact ⟨hRint, hRbound⟩

end

end HeavyTailedNoise.UpperK1
