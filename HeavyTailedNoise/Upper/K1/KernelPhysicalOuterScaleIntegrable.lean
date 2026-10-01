import HeavyTailedNoise.Upper.K1.KernelRuntimeSourceDriftReadout
import HeavyTailedNoise.Upper.K1.KernelPhysicalTrackerMemLp

/-!
The true adjacent-boundary tracker scale is integrable to the manuscript
exponent `s = p(1-1/q)` under the full product law.  It uses the one actual
tracker and the single physical tracker-moment source.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

theorem paperSchedule_actualTrackerPairScale_rpow_integrable
    (p q Δ σ Lbar ε Ctail κ Cb CI : ℝ)
    (hq : 1 < q)
    (hε : 0 < ε) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
      hε (by norm_num) hCb hCI
    let μ := (algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw I.oracle (responseCount P))
    ∀ u : Fin P.T,
      Integrable (fun z =>
        (actualTrackerPairScale P I u z) ^ paperSexp p q) μ := by
  dsimp only
  intro u
  let P := paperSchedule p q Δ σ Lbar ε Ctail (1 / 8) κ Cb CI
    hε (by norm_num) hCb hCI
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle (responseCount P)) :=
    freshSeedLaw_probability I.oracle (responseCount P)
  let μ := (algorithm (d := d) P).privateLaw.prod
    (freshSeedLaw I.oracle (responseCount P))
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let s := paperSexp p q
  let E₀ : Fin P.T × (Fin (responseCount P) → Seed) → ℝ :=
    actualTrackerAtBoundary P I u.val
  let E₁ : Fin P.T × (Fin (responseCount P) → Seed) → ℝ :=
    actualTrackerAtBoundary P I (u.val + 1)
  let A : Fin P.T × (Fin (responseCount P) → Seed) → ℝ :=
    actualTrackerPairScale P I u
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos (lt_trans zero_lt_one I.p_range.1)
    apply sub_pos.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa using hq)
  have hsp : s ≤ p := by
    dsimp [s, paperSexp]
    apply mul_le_of_le_one_right
      (lt_trans zero_lt_one I.p_range.1).le
    exact sub_le_self _ (div_nonneg (by norm_num) hqpos.le)
  have hE₀ : MemLp E₀ (ENNReal.ofReal p) μ := by
    simpa only [E₀, μ] using
      (paperSchedule_actualTracker_memLp
        p q Δ σ Lbar ε Ctail κ Cb CI hε hCb hCI I
        u.val (Nat.le_of_lt u.isLt))
  have hE₁ : MemLp E₁ (ENNReal.ofReal p) μ := by
    simpa only [E₁, μ] using
      (paperSchedule_actualTracker_memLp
        p q Δ σ Lbar ε Ctail κ Cb CI hε hCb hCI I
        (u.val + 1) (Nat.succ_le_iff.mpr u.isLt))
  have hconst : MemLp (fun _ : Fin P.T × (Fin (responseCount P) → Seed) =>
      2 * σ) (ENNReal.ofReal p) μ := memLp_const _
  have hAfun : A = ((fun _ => 2 * σ) + E₀) + E₁ := by
    funext z
    change actualTrackerPairScale P I u z = _
    rw [actualTrackerPairScale]
    rfl
  have hAMem : MemLp A (ENNReal.ofReal p) μ := by
    rw [hAfun]
    exact (hconst.add hE₀).add hE₁
  have hASMem : MemLp A (ENNReal.ofReal s) μ :=
    hAMem.mono_exponent (ENNReal.ofReal_le_ofReal hsp)
  have hA0 (z : Fin P.T × (Fin (responseCount P) → Seed)) :
      0 ≤ A z := by
    change 0 ≤ actualTrackerPairScale P I u z
    rw [actualTrackerPairScale]
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) I.sigma_nonneg)
        (actualTrackerAtBoundary_nonneg P I u.val z))
      (actualTrackerAtBoundary_nonneg P I (u.val + 1) z)
  have hNormInt : Integrable (fun z => ‖A z‖ ^ s) μ := by
    simpa only [ENNReal.toReal_ofReal hs.le] using
      (hASMem.integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hs) ENNReal.ofReal_ne_top)
  have hfun : (fun z => ‖A z‖ ^ s) = (fun z => (A z) ^ s) := by
    funext z
    rw [Real.norm_eq_abs, abs_of_nonneg (hA0 z)]
  rw [hfun] at hNormInt
  exact hNormInt

end

end HeavyTailedNoise.UpperK1
