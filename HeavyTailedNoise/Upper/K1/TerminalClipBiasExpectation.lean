import HeavyTailedNoise.Upper.K1.TerminalClipBias
import HeavyTailedNoise.Upper.K1.ResidualPhysicalMoment
import HeavyTailedNoise.Upper.K1.RuntimeNoisePhysicalCoefficient
import HeavyTailedNoise.Upper.K1.RuntimeNoisePrivateIndependence

/-!
The expected terminal clipping bias on the literal actual run.  Only the
original centered oracle `p` moment and the already proved physical tracker
moment are used; no absolute residual `q` moment is required.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

/-- Exact normalization of the terminal target: its `S` factor cancels the
physical noise ratio without requiring `J > 0`. -/
theorem paper_terminal_target_ratio
    {p σ ε Ctail : ℝ}
    (hp : 1 < p) (hε : 0 < ε) (hCtail : 0 < Ctail) :
    (paperNu σ ε) ^ p /
        (paperNu σ ε * paperTailTarget p σ ε Ctail) ^ (p - 1) =
      ε / Ctail ^ (p - 1) := by
  let ν := paperNu σ ε
  let S := paperS σ ε
  let r := p - 1
  have hν : 0 < ν := paperNu_pos hε
  have hS : 0 < S := paperS_pos σ ε
  have hr : 0 < r := sub_pos.mpr hp
  have hνr : 0 < ν ^ r := Real.rpow_pos_of_pos hν _
  have hCr : 0 < Ctail ^ r := Real.rpow_pos_of_pos hCtail _
  have hSp : 0 < S ^ (1 / r) := Real.rpow_pos_of_pos hS _
  have hSroot : (S ^ (1 / r)) ^ r = S := by
    rw [← Real.rpow_mul hS.le]
    have hcancel : 1 / r * r = 1 := by field_simp [ne_of_gt hr]
    rw [hcancel, Real.rpow_one]
  have hνp : ν ^ p = ν ^ r * ν := by
    have hexp : p = r + 1 := by dsimp [r]; ring
    rw [hexp, Real.rpow_add hν]
    simp
  have hbpow :
      (ν * (Ctail * S ^ (1 / r))) ^ r = ν ^ r * Ctail ^ r * S := by
    rw [Real.mul_rpow hν.le (mul_nonneg hCtail.le hSp.le),
      Real.mul_rpow hCtail.le hSp.le, hSroot]
    ring
  have hνS : ν = ε * S := paperNu_eq_epsilon_mul_paperS hε
  change ν ^ p / (ν * (Ctail * S ^ (1 / r))) ^ r =
    ε / Ctail ^ r
  rw [hνp, hbpow]
  apply (div_eq_div_iff
    (ne_of_gt (mul_pos (mul_pos hνr hCr) hS))
    (ne_of_gt hCr)).2
  rw [hνS]
  ring

/-- Bias norm of the actual terminal clip at one pre-batch state. -/
def actualTerminalClipBiasNorm
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (P : Schedule q) (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) : ℝ :=
  let H := batchHistoryOfRun P I.oracle u z
  ‖batchCenter P u H +
      upperResidualSourceMean I.oracle
        (upperClip (P.tau (Fin.last P.J)))
        (batchDecision P u H) (batchCenter P u H) -
      I.objective.grad (batchDecision P u H)‖

theorem measurable_actualTerminalClipBiasNorm
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (P : Schedule q) (u : Fin P.T) :
    Measurable (actualTerminalClipBiasNorm I P u) := by
  have hhistory := measurable_batchHistoryOfRun P I.oracle u
  have hx := (measurable_batchDecision P u).comp hhistory
  have hw := (measurable_batchCenter P u).comp hhistory
  have hmean := measurable_upperResidualSourceMean I.oracle
    (upperClip (P.tau (Fin.last P.J)))
    (measurable_upperClip (P.tau_pos (Fin.last P.J)))
    (batchDecision P u) (batchCenter P u)
    (measurable_batchDecision P u) (measurable_batchCenter P u)
  exact ((hw.add (hmean.comp hhistory)).sub
    (I.objective.continuous_grad.measurable.comp hx)).norm

/-- The terminal-bias readout depends on the transcript, not on the private
index later used to select the output batch. -/
theorem actualTerminalClipBiasNorm_private_independent
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (P : Schedule q) (u : Fin P.T)
    (r r' : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    actualTerminalClipBiasNorm I P u (r, seeds) =
      actualTerminalClipBiasNorm I P u (r', seeds) := by
  have htrans := batchHistoryOfRun_transcript_private_independent
    P I.oracle u r r' seeds
  unfold actualTerminalClipBiasNorm batchDecision batchCenter
  simp only [htrans]

/-- Integrability of the actual terminal-bias norm under the literal paper
schedule follows from the original tracker `p` moment. -/
theorem Admissible.paperSchedule_actualTerminalClipBiasNorm_integrable
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    ∀ u : Fin P.T,
      Integrable (actualTerminalClipBiasNorm I P u)
        ((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw I.oracle (responseCount P))) := by
  dsimp only
  intro u
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle (responseCount P)) :=
    freshSeedLaw_probability I.oracle (responseCount P)
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let τ := P.tau (Fin.last P.J)
  let E := actualTrackerAtBoundary P I u.val
  let F := actualTerminalClipBiasNorm I P u
  let M : Fin P.T × (Fin (responseCount P) → Seed) → ℝ :=
    fun z => (4 / τ ^ (p - 1)) * (σ ^ p + (E z) ^ p)
  have hτ : 0 < τ := P.tau_pos (Fin.last P.J)
  have hτpow : 0 < τ ^ (p - 1) := Real.rpow_pos_of_pos hτ _
  have hEp : Integrable (fun z => (E z) ^ p) μ := by
    simpa only [E, μ] using
      (Admissible.paperSchedule_eighth_tracker_p_moment_le_nu
        I ε Ctail κ Cb CI hε hCb hCI u.val
        (Nat.le_of_lt u.isLt)).1
  have hMint : Integrable M μ := by
    exact ((integrable_const (σ ^ p)).add hEp).const_mul _
  have hpoint (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      F z ≤ M z := by
    let H := batchHistoryOfRun P I.oracle u z
    let x := batchDecision P u H
    let w := batchCenter P u H
    have hbase := Admissible.terminalClip_sourceMean_bias_le I hτ x w
    have hEeq : ‖I.objective.grad x - w‖ = E z := by
      change ‖I.objective.grad x - w‖ =
        actualTrackerAtBoundary P I u.val z
      rw [actualTrackerAtBoundary_eq_history P I u z]
      exact norm_sub_rev _ _
    have hE0 : 0 ≤ E z := actualTrackerAtBoundary_nonneg P I u.val z
    have hadd := add_rpow_le_two_sum I.p_range.1.le I.p_range.2
      I.sigma_nonneg hE0
    have hfac : 0 ≤ 2 / τ ^ (p - 1) := by positivity
    calc
      F z ≤ 2 * (σ + E z) ^ p / τ ^ (p - 1) := by
        simpa only [F, actualTerminalClipBiasNorm, H, x, w, hEeq]
          using hbase
      _ = (2 / τ ^ (p - 1)) * (σ + E z) ^ p := by ring
      _ ≤ (2 / τ ^ (p - 1)) *
          (2 * (σ ^ p + (E z) ^ p)) :=
        mul_le_mul_of_nonneg_left hadd hfac
      _ = M z := by dsimp [M]; ring
  have hFmeas : Measurable F :=
    measurable_actualTerminalClipBiasNorm I P u
  apply Integrable.mono' hMint hFmeas.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    have hF0 : 0 ≤ F z := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hF0]
    exact hpoint z

/-- A directly usable expected bias bound before the final scalar
normalization of the terminal threshold. -/
theorem Admissible.paperSchedule_actualTerminalClipBias_expectation_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCtail : 0 < Ctail)
    (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    ∀ u : Fin P.T,
      (∫ z, actualTerminalClipBiasNorm I P u z
        ∂((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw I.oracle (responseCount P)))) ≤
      4 * (1 + physicalResidualTrackerConstant p) *
        (paperNu σ ε) ^ p /
        (paperNu σ ε * paperTailTarget p σ ε Ctail) ^ (p - 1) := by
  dsimp only
  intro u
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  let b := paperNu σ ε * paperTailTarget p σ ε Ctail
  let F := actualTerminalClipBiasNorm I P u
  let E := actualTrackerAtBoundary P I u.val
  let M : Fin P.T × (Fin (responseCount P) → Seed) → ℝ :=
    fun z => 2 * (σ + E z) ^ p / b ^ (p - 1)
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle (responseCount P)) :=
    freshSeedLaw_probability I.oracle (responseCount P)
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hp : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hb : 0 < b := by
    dsimp [b, paperTailTarget]
    exact mul_pos (paperNu_pos hε)
      (mul_pos hCtail
        (Real.rpow_pos_of_pos (paperS_pos σ ε) _))
  have hbp : 0 < b ^ (p - 1) := Real.rpow_pos_of_pos hb _
  have hEmeas : Measurable E := measurable_actualTrackerAtBoundary P I u.val
  have hEp : Integrable (fun z => (E z) ^ p) μ := by
    simpa only [E, μ] using
      (Admissible.paperSchedule_eighth_tracker_p_moment_le_nu
        I ε Ctail κ Cb CI hε hCb hCI u.val
        (Nat.le_of_lt u.isLt)).1
  have hEbound : (∫ z, (E z) ^ p ∂μ) ≤
      physicalResidualTrackerConstant p * (paperNu σ ε) ^ p := by
    simpa only [E, μ, physicalResidualTrackerConstant] using
      (Admissible.paperSchedule_eighth_tracker_p_moment_le_nu
        I ε Ctail κ Cb CI hε hCb hCI u.val
        (Nat.le_of_lt u.isLt)).2
  have hEnonneg (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      0 ≤ E z := actualTrackerAtBoundary_nonneg P I u.val z
  have hpoint (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      F z ≤ M z := by
    dsimp [F, M, actualTerminalClipBiasNorm]
    have h := Admissible.paperSchedule_terminalClip_sourceMean_bias_le
      I ε Ctail (1 / 8) κ Cb CI hε hCtail (by norm_num) hCb hCI
      (batchDecision P u (batchHistoryOfRun P I.oracle u z))
      (batchCenter P u (batchHistoryOfRun P I.oracle u z))
    change _ ≤ 2 * (σ + ‖I.objective.grad
      (batchDecision P u (batchHistoryOfRun P I.oracle u z)) -
      batchCenter P u (batchHistoryOfRun P I.oracle u z)‖) ^ p /
      b ^ (p - 1) at h
    have hEeq :
        ‖I.objective.grad
          (batchDecision P u (batchHistoryOfRun P I.oracle u z)) -
          batchCenter P u (batchHistoryOfRun P I.oracle u z)‖ = E z := by
      change _ = actualTrackerAtBoundary P I u.val z
      rw [actualTrackerAtBoundary_eq_history P I u z]
      exact norm_sub_rev _ _
    simpa only [hEeq] using h
  have hMbound (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      M z ≤ (4 / b ^ (p - 1)) * (σ ^ p + (E z) ^ p) := by
    have hadd := add_rpow_le_two_sum I.p_range.1.le I.p_range.2
      I.sigma_nonneg (hEnonneg z)
    have hfac : 0 ≤ 2 / b ^ (p - 1) := by positivity
    change 2 * (σ + E z) ^ p / b ^ (p - 1) ≤ _
    calc
      2 * (σ + E z) ^ p / b ^ (p - 1) =
          (2 / b ^ (p - 1)) * (σ + E z) ^ p := by ring
      _ ≤ (2 / b ^ (p - 1)) *
          (2 * (σ ^ p + (E z) ^ p)) :=
        mul_le_mul_of_nonneg_left hadd hfac
      _ = _ := by ring
  have hMsmall : Integrable
      (fun z => (4 / b ^ (p - 1)) * (σ ^ p + (E z) ^ p)) μ :=
    ((integrable_const (σ ^ p)).add hEp).const_mul _
  have hFint : Integrable F μ := by
    simpa only [F, μ] using
      (Admissible.paperSchedule_actualTerminalClipBiasNorm_integrable
        I ε Ctail κ Cb CI hε hCb hCI u)
  have hMint : Integrable M μ := by
    have hMmeas : Measurable M := by
      dsimp [M]
      fun_prop
    apply Integrable.mono' hMsmall hMmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      have hM0 : 0 ≤ M z := by
        dsimp [M]
        exact div_nonneg
          (mul_nonneg (by norm_num)
            (Real.rpow_nonneg
              (add_nonneg I.sigma_nonneg (hEnonneg z)) _))
          hbp.le
      rw [Real.norm_eq_abs, abs_of_nonneg hM0]
      exact hMbound z
  calc
    (∫ z, F z ∂μ) ≤ ∫ z, M z ∂μ :=
      integral_mono hFint hMint hpoint
    _ ≤ (4 / b ^ (p - 1)) *
        (σ ^ p + ∫ z, (E z) ^ p ∂μ) := by
          have hupper := integral_mono hMint hMsmall hMbound
          rw [integral_const_mul, integral_add
            (integrable_const _) hEp] at hupper
          simpa using hupper
    _ ≤ 4 * (1 + physicalResidualTrackerConstant p) *
        (paperNu σ ε) ^ p / b ^ (p - 1) := by
          have hσ : σ ^ p ≤ (paperNu σ ε) ^ p :=
            Real.rpow_le_rpow I.sigma_nonneg (le_max_left σ ε) hp.le
          have hfac : 0 ≤ 4 / b ^ (p - 1) := by positivity
          have hmul := mul_le_mul_of_nonneg_left
            (add_le_add hσ hEbound) hfac
          calc
            (4 / b ^ (p - 1)) *
                (σ ^ p + ∫ z, (E z) ^ p ∂μ) ≤
                (4 / b ^ (p - 1)) *
                  ((paperNu σ ε) ^ p +
                    physicalResidualTrackerConstant p *
                      (paperNu σ ε) ^ p) := hmul
            _ = _ := by dsimp [b]; ring

/-- The expected actual terminal clipping bias is of order
`Ctail^(1-p) ε`, uniformly over the output batch. -/
theorem Admissible.paperSchedule_actualTerminalClipBias_expectation_le_epsilon
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCtail : 0 < Ctail)
    (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    ∀ u : Fin P.T,
      (∫ z, actualTerminalClipBiasNorm I P u z
        ∂((algorithm (d := d) P).privateLaw.prod
          (freshSeedLaw I.oracle (responseCount P)))) ≤
      4 * (1 + physicalResidualTrackerConstant p) *
        ε / Ctail ^ (p - 1) := by
  dsimp only
  intro u
  have hbase := Admissible.paperSchedule_actualTerminalClipBias_expectation_le
    I ε Ctail κ Cb CI hε hCtail hCb hCI u
  have hratio := paper_terminal_target_ratio (σ := σ)
    I.p_range.1 hε hCtail
  calc
    _ ≤ 4 * (1 + physicalResidualTrackerConstant p) *
        ((paperNu σ ε) ^ p /
          (paperNu σ ε * paperTailTarget p σ ε Ctail) ^ (p - 1)) := by
            convert hbase using 1 <;> ring
    _ = 4 * (1 + physicalResidualTrackerConstant p) *
        (ε / Ctail ^ (p - 1)) := by rw [hratio]
    _ = _ := by ring

/-- Seed-only normalized terminal-bias budget in the exact form used by the
selected-output risk bound.  The output index has been removed from every
readout before taking the uniform time average. -/
theorem Admissible.paperSchedule_actualTerminalClipBias_seed_average_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail κ Cb CI : ℝ)
    (hε : 0 < ε) (hCtail : 0 < Ctail)
    (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    (P.T : ENNReal)⁻¹ *
      (∫⁻ seeds : Fin (responseCount P) → Seed,
        ENNReal.ofReal
          (∑ u : Fin P.T,
            actualTerminalClipBiasNorm I P u (⟨0, P.T_pos⟩, seeds))
        ∂freshSeedLaw I.oracle (responseCount P)) ≤
      ENNReal.ofReal
        (4 * (1 + physicalResidualTrackerConstant p) *
          ε / Ctail ^ (p - 1)) := by
  dsimp only
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  let r₀ : Fin P.T := ⟨0, P.T_pos⟩
  let B := 4 * (1 + physicalResidualTrackerConstant p) *
    ε / Ctail ^ (p - 1)
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  have hone (u : Fin P.T) :
      (∫⁻ seeds : Fin (responseCount P) → Seed,
        ENNReal.ofReal (actualTerminalClipBiasNorm I P u (r₀, seeds))
        ∂freshSeedLaw I.oracle (responseCount P)) ≤ ENNReal.ofReal B := by
    let F := actualTerminalClipBiasNorm I P u
    let f : Fin P.T × (Fin (responseCount P) → Seed) → ENNReal :=
      fun z => ENNReal.ofReal (F z)
    have hf : Measurable f :=
      ENNReal.measurable_ofReal.comp
        (measurable_actualTerminalClipBiasNorm I P u)
    have hind (r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
        f (r, seeds) = f (r₀, seeds) := by
      dsimp [f, F]
      rw [actualTerminalClipBiasNorm_private_independent
        I P u r r₀ seeds]
    have htransport := lintegral_private_independent
      P I.oracle f hf r₀ hind
    have hInt : Integrable F μ := by
      simpa only [F, μ] using
        (Admissible.paperSchedule_actualTerminalClipBiasNorm_integrable
          I ε Ctail κ Cb CI hε hCb hCI u)
    have hreal : (∫ z, F z ∂μ) ≤ B := by
      simpa only [F, μ, B] using
        (Admissible.paperSchedule_actualTerminalClipBias_expectation_le_epsilon
          I ε Ctail κ Cb CI hε hCtail hCb hCI u)
    have hnonneg : 0 ≤ᵐ[μ] F :=
      Filter.Eventually.of_forall (fun z => norm_nonneg _)
    calc
      (∫⁻ seeds, ENNReal.ofReal (F (r₀, seeds))
          ∂freshSeedLaw I.oracle (responseCount P)) =
          ∫⁻ z, f z ∂μ := htransport.symm
      _ = ENNReal.ofReal (∫ z, F z ∂μ) := by
        exact (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hreal
  have hmeas (u : Fin P.T) : Measurable
      (fun seeds : Fin (responseCount P) → Seed =>
        ENNReal.ofReal
          (actualTerminalClipBiasNorm I P u (r₀, seeds))) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_actualTerminalClipBiasNorm I P u).comp
        (measurable_const.prodMk measurable_id))
  have hsumPoint (seeds : Fin (responseCount P) → Seed) :
      ENNReal.ofReal
        (∑ u : Fin P.T,
          actualTerminalClipBiasNorm I P u (r₀, seeds)) =
      ∑ u : Fin P.T,
        ENNReal.ofReal
          (actualTerminalClipBiasNorm I P u (r₀, seeds)) :=
    ENNReal.ofReal_sum_of_nonneg (fun u _ => norm_nonneg _)
  have hT0 : (P.T : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt P.T_pos)
  have hTtop : (P.T : ENNReal) ≠ ⊤ := by simp
  calc
    (P.T : ENNReal)⁻¹ *
        (∫⁻ seeds,
          ENNReal.ofReal
            (∑ u : Fin P.T,
              actualTerminalClipBiasNorm I P u (r₀, seeds))
          ∂freshSeedLaw I.oracle (responseCount P)) =
        (P.T : ENNReal)⁻¹ *
          (∑ u : Fin P.T,
            ∫⁻ seeds,
              ENNReal.ofReal
                (actualTerminalClipBiasNorm I P u (r₀, seeds))
              ∂freshSeedLaw I.oracle (responseCount P)) := by
      simp_rw [hsumPoint]
      rw [lintegral_finsetSum Finset.univ (fun u _ => hmeas u)]
    _ ≤ (P.T : ENNReal)⁻¹ *
          (∑ _u : Fin P.T, ENNReal.ofReal B) := by
      gcongr with u hu
      exact hone u
    _ = ENNReal.ofReal B := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      calc
        _ = (P.T : ENNReal)⁻¹ *
            ((P.T : ENNReal) * ENNReal.ofReal B) := by ac_rfl
        _ = ENNReal.ofReal B :=
          ENNReal.inv_mul_cancel_left hT0 hTtop

end

end HeavyTailedNoise.UpperK1
