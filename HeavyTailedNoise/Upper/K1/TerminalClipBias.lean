import HeavyTailedNoise.Upper.K1.StationarityActualErrorSplit
import HeavyTailedNoise.Upper.K1.SameSeedResidualLpNormBounds
import HeavyTailedNoise.Upper.K1.KernelDriftMomentInterpolation
import HeavyTailedNoise.Upper.K1.CutoffBounds

/-!
The only terminal clipping bias is the difference between the auxiliary-source
mean of the actual terminal clip and the population gradient. The moment below
is the original centered `p`-BCM moment; the residual about a fixed tracker
center is handled by Minkowski, with no extra oracle premise. The bound is
pointwise in the decision and center, so it also applies to adaptive decisions.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

/-- A deliberately conservative tail bound, valid also at `p = 2` and `z = 0`.
The factor two avoids relying on a formula for the exact radial excess. -/
theorem upperClip_error_norm_le_rpow {d : ℕ} {τ p : ℝ}
    (hτ : 0 < τ) (hp : 1 < p) (z : Point d) :
    ‖upperClip τ z - z‖ ≤ 2 * ‖z‖ ^ p / τ ^ (p - 1) := by
  have hτpow : 0 < τ ^ (p - 1) := Real.rpow_pos_of_pos hτ _
  have hrhs : 0 ≤ 2 * ‖z‖ ^ p / τ ^ (p - 1) := by positivity
  by_cases hz : ‖z‖ ≤ τ
  · rw [upperClip_eq_self_of_norm_le hτ hz, sub_self, norm_zero]
    exact hrhs
  · have hτz : τ ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz)
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hτ hτz
    have hclip : ‖upperClip τ z‖ ≤ ‖z‖ := by
      simpa using upperClip_norm_sub_le hτ z (0 : Point d)
    have hlinear : ‖upperClip τ z - z‖ ≤ 2 * ‖z‖ := by
      calc
        ‖upperClip τ z - z‖ ≤ ‖upperClip τ z‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 2 * ‖z‖ := by linarith
    have hpow : τ ^ (p - 1) ≤ ‖z‖ ^ (p - 1) :=
      Real.rpow_le_rpow hτ.le hτz (by linarith)
    have hidentity : ‖z‖ * ‖z‖ ^ (p - 1) = ‖z‖ ^ p := by
      calc
        ‖z‖ * ‖z‖ ^ (p - 1) = ‖z‖ ^ (1 : ℝ) * ‖z‖ ^ (p - 1) := by simp
        _ = ‖z‖ ^ (1 + (p - 1)) := (Real.rpow_add hzpos _ _).symm
        _ = ‖z‖ ^ p := by congr 1; ring
    have hratio : ‖z‖ ≤ ‖z‖ ^ p / τ ^ (p - 1) := by
      apply (le_div_iff₀ hτpow).mpr
      nlinarith [mul_le_mul_of_nonneg_left hpow (norm_nonneg z)]
    calc
      ‖upperClip τ z - z‖ ≤ 2 * ‖z‖ := hlinear
      _ ≤ 2 * (‖z‖ ^ p / τ ^ (p - 1)) := by nlinarith [hratio]
      _ = 2 * ‖z‖ ^ p / τ ^ (p - 1) := by ring

/-- At any fixed decision and tracker center, terminal clipping introduces
at most the original residual `L^p` scale divided by the terminal threshold.
This includes `σ = 0` and makes no use of `q > 1`. -/
theorem Admissible.terminalClip_sourceMean_bias_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    {τ : ℝ} (hτ : 0 < τ) (x w : Point d) :
    ‖w + upperResidualSourceMean I.oracle (upperClip τ) x w -
        I.objective.grad x‖ ≤
      2 * (σ + ‖I.objective.grad x - w‖) ^ p / τ ^ (p - 1) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  let R : Seed → Point d := fun ξ => I.oracle.response x ξ - w
  let C : Seed → Point d := fun ξ => upperClip τ (R ξ)
  have hR : Integrable R I.oracle.law :=
    (I.integrable_response x).sub (integrable_const w)
  have hC : Integrable C I.oracle.law :=
    upperResidualSource_integrable I.oracle (upperClip τ)
      (measurable_upperClip hτ) τ (upperClip_norm_le hτ) x w
  have hRmean : (∫ ξ, R ξ ∂I.oracle.law) = I.objective.grad x - w := by
    dsimp [R]
    rw [integral_sub (I.integrable_response x) (integrable_const w)]
    simp [I.unbiased x]
  have hmean :
      w + upperResidualSourceMean I.oracle (upperClip τ) x w -
          I.objective.grad x =
        ∫ ξ, C ξ - R ξ ∂I.oracle.law := by
    rw [integral_sub hC hR, hRmean]
    change w + (∫ ξ, C ξ ∂I.oracle.law) - I.objective.grad x =
      (∫ ξ, C ξ ∂I.oracle.law) - (I.objective.grad x - w)
    abel
  have hMem : MemLp R (ENNReal.ofReal p) I.oracle.law :=
    Admissible.residual_memLp I x w
  have hRm : Measurable R :=
    (I.oracle.measurable_response.comp
      (measurable_const.prodMk measurable_id)).sub measurable_const
  have hp0 : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hPowInt : Integrable (fun ξ => ‖R ξ‖ ^ p) I.oracle.law := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      (hMem.integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top)
  have hτpow : 0 < τ ^ (p - 1) := Real.rpow_pos_of_pos hτ _
  have hfactor : 0 ≤ 2 / τ ^ (p - 1) := by positivity
  have hpoint (ξ : Seed) :
      ‖C ξ - R ξ‖ ≤ (2 / τ ^ (p - 1)) * ‖R ξ‖ ^ p := by
    simpa only [C, div_mul_eq_mul_div] using
      upperClip_error_norm_le_rpow hτ I.p_range.1 (R ξ)
  have hmoment :
      (∫ ξ, ‖R ξ‖ ^ p ∂I.oracle.law) ≤
        (lpNorm R (ENNReal.ofReal p) I.oracle.law) ^ p := by
    have h := integral_rpow_le_lpNorm_rpow_of_probability I.oracle.law
      (fun ξ => ‖R ξ‖) hRm.norm (fun ξ => norm_nonneg _)
      hp0 le_rfl hMem.norm
    simpa only [lpNorm_norm hMem.aestronglyMeasurable] using h
  have hLp := Admissible.residual_lpNorm_le I x w
  have hLpPow :
      (lpNorm R (ENNReal.ofReal p) I.oracle.law) ^ p ≤
        (σ + ‖I.objective.grad x - w‖) ^ p :=
    Real.rpow_le_rpow lpNorm_nonneg hLp hp0.le
  calc
    ‖w + upperResidualSourceMean I.oracle (upperClip τ) x w -
        I.objective.grad x‖ = ‖∫ ξ, C ξ - R ξ ∂I.oracle.law‖ := by rw [hmean]
    _ ≤ ∫ ξ, ‖C ξ - R ξ‖ ∂I.oracle.law :=
      norm_integral_le_integral_norm _
    _ ≤ (2 / τ ^ (p - 1)) *
        (∫ ξ, ‖R ξ‖ ^ p ∂I.oracle.law) := by
      rw [← integral_const_mul]
      exact integral_mono (hC.sub hR).norm
        (hPowInt.const_mul _) hpoint
    _ ≤ (2 / τ ^ (p - 1)) *
        (lpNorm R (ENNReal.ofReal p) I.oracle.law) ^ p :=
      mul_le_mul_of_nonneg_left hmoment hfactor
    _ ≤ (2 / τ ^ (p - 1)) *
        (σ + ‖I.objective.grad x - w‖) ^ p :=
      mul_le_mul_of_nonneg_left hLpPow hfactor
    _ = 2 * (σ + ‖I.objective.grad x - w‖) ^ p /
        τ ^ (p - 1) := by ring

/-- The literal terminal threshold reaches the physical cutoff. This does
not assume `J > 0`; the least-index definition covers `J = 0`. -/
theorem paperTau_terminal_ge_tail_scale
    {p σ ε Ctail : ℝ} (hε : 0 < ε) :
    paperNu σ ε * paperTailTarget p σ ε Ctail ≤
      paperTau σ ε (paperJ p σ ε Ctail) := by
  have hν : 0 ≤ paperNu σ ε := (paperNu_pos hε).le
  have htarget := paperJ_reaches_target p σ ε Ctail
  unfold paperTau
  nlinarith [mul_le_mul_of_nonneg_left htarget hν]

/-- Physical terminal-bias scale under the unchanged literal schedule.
The remaining tracker error is a genuine state variable, not a new premise
about oracle noise. -/
theorem Admissible.paperSchedule_terminalClip_sourceMean_bias_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hCtail : 0 < Ctail)
    (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    (x w : Point d) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    ‖w + upperResidualSourceMean I.oracle
        (upperClip (P.tau (Fin.last P.J))) x w -
        I.objective.grad x‖ ≤
      2 * (σ + ‖I.objective.grad x - w‖) ^ p /
        (paperNu σ ε * paperTailTarget p σ ε Ctail) ^ (p - 1) := by
  dsimp only
  let τ := paperTau σ ε (paperJ p σ ε Ctail)
  let b := paperNu σ ε * paperTailTarget p σ ε Ctail
  have hτ : 0 < τ := paperTau_pos hε _
  have hS : 0 < paperS σ ε := paperS_pos σ ε
  have htarget : 0 < paperTailTarget p σ ε Ctail := by
    dsimp [paperTailTarget]
    positivity
  have hb : 0 < b := mul_pos (paperNu_pos hε) htarget
  have hcut : b ≤ τ := paperTau_terminal_ge_tail_scale hε
  have hden : b ^ (p - 1) ≤ τ ^ (p - 1) :=
    Real.rpow_le_rpow hb.le hcut (by linarith [I.p_range.1])
  have hnum : 0 ≤ 2 * (σ + ‖I.objective.grad x - w‖) ^ p := by
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg (add_nonneg I.sigma_nonneg (norm_nonneg _)) _)
  have hbase := Admissible.terminalClip_sourceMean_bias_le I hτ x w
  change ‖w + upperResidualSourceMean I.oracle (upperClip τ) x w -
      I.objective.grad x‖ ≤
    2 * (σ + ‖I.objective.grad x - w‖) ^ p / b ^ (p - 1)
  exact hbase.trans (div_le_div_of_nonneg_left hnum
    (Real.rpow_pos_of_pos hb _) hden)

end

end HeavyTailedNoise.UpperK1
