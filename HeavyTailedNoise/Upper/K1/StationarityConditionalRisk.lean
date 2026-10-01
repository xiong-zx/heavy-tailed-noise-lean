import HeavyTailedNoise.Upper.K1.StationarityAssembly

/-!
Conditional expected stationarity for the one literal algorithm. The only
unfinished analytical input is the time-average completed-estimator error;
path, query, and scalar-budget premises are explicit and must later be
discharged by the actual-run and physical-schedule modules.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem Admissible.risk_le_of_average_estimate_error
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar ε K : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hε : 0 < ε) (hh : 0 < P.h) (hKnonneg : 0 ≤ K)
    (hK : Δ + (P.T : ℝ) * Lbar * P.h ^ 2 ≤ P.h * K)
    (hbudget : (P.T : ENNReal)⁻¹ * ENNReal.ofReal K +
      2 * ENNReal.ofReal (ε / 8) ≤ ENNReal.ofReal ε)
    (x hhat : (Fin (responseCount P) → Seed) → ℕ → Point d)
    (hx0 : ∀ seeds, x seeds 0 = 0)
    (hstep : ∀ seeds (t : ℕ), t < P.T →
      x seeds (t + 1) = x seeds t - P.h • direction (hhat seeds t))
    (hxQuery : ∀ seeds (r : Fin P.T),
      x seeds r.val = canonicalRuntimePoint P I.oracle r seeds)
    (hxMeas : ∀ r : Fin P.T,
      Measurable (fun seeds => x seeds r.val))
    (herror : (P.T : ENNReal)⁻¹ *
      (∫⁻ seeds : Fin (responseCount P) → Seed,
        ENNReal.ofReal
          (∑ t ∈ Finset.range P.T,
            ‖hhat seeds t - I.objective.grad (x seeds t)‖)
        ∂freshSeedLaw I.oracle (responseCount P)) ≤
      ENNReal.ofReal (ε / 8)) :
    risk I (algorithm P) ≤ ENNReal.ofReal ε := by
  let seedLaw := freshSeedLaw I.oracle (responseCount P)
  letI : IsProbabilityMeasure seedLaw :=
    freshSeedLaw_probability I.oracle (responseCount P)
  let c : ENNReal := (P.T : ENNReal)⁻¹
  let G : (Fin (responseCount P) → Seed) → ℝ := fun seeds =>
    ∑ r : Fin P.T, ‖I.objective.grad (x seeds r.val)‖
  let E : (Fin (responseCount P) → Seed) → ℝ := fun seeds =>
    ∑ t ∈ Finset.range P.T,
      ‖hhat seeds t - I.objective.grad (x seeds t)‖
  have hpath (seeds : Fin (responseCount P) → Seed) :
      G seeds ≤ K + 2 * E seeds := by
    have hdescent := Admissible.finite_normalized_descent_sum_gap I hh.le P.T
      (x seeds) (hhat seeds) (hstep seeds) (hx0 seeds)
    have hG : G seeds = ∑ t ∈ Finset.range P.T,
        ‖I.objective.grad (x seeds t)‖ := by
      dsimp [G]
      exact Fin.sum_univ_eq_sum_range
        (fun t : ℕ => ‖I.objective.grad (x seeds t)‖) P.T
    rw [← hG] at hdescent
    have hmul : P.h * G seeds ≤ P.h * (K + 2 * E seeds) := by
      dsimp [E]
      nlinarith [hdescent, hK]
    exact (mul_le_mul_iff_of_pos_left hh).mp hmul
  have hpointwise (seeds : Fin (responseCount P) → Seed) :
      (∑ r : Fin P.T,
        ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖) ≤
      ENNReal.ofReal K + 2 * ENNReal.ofReal (E seeds) := by
    calc
      (∑ r : Fin P.T,
        ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖) =
          ENNReal.ofReal (G seeds) := by
            exact (ENNReal.ofReal_sum_of_nonneg
              (fun r _ => norm_nonneg (I.objective.grad (x seeds r.val)))).symm
      _ ≤ ENNReal.ofReal (K + 2 * E seeds) :=
        ENNReal.ofReal_le_ofReal (hpath seeds)
      _ ≤ ENNReal.ofReal K + ENNReal.ofReal (2 * E seeds) :=
        ENNReal.ofReal_add_le
      _ = ENNReal.ofReal K + 2 * ENNReal.ofReal (E seeds) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hsumBound :
      (∫⁻ seeds : Fin (responseCount P) → Seed,
        ∑ r : Fin P.T,
          ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖ ∂seedLaw) ≤
      ENNReal.ofReal K +
        2 * ∫⁻ seeds : Fin (responseCount P) → Seed,
          ENNReal.ofReal (E seeds) ∂seedLaw := by
    calc
      _ ≤ ∫⁻ seeds : Fin (responseCount P) → Seed,
          ENNReal.ofReal K + 2 * ENNReal.ofReal (E seeds) ∂seedLaw :=
            lintegral_mono hpointwise
      _ = ENNReal.ofReal K +
          2 * ∫⁻ seeds : Fin (responseCount P) → Seed,
            ENNReal.ofReal (E seeds) ∂seedLaw := by
              rw [lintegral_add_left measurable_const]
              rw [lintegral_const_mul' 2 _ (by norm_num : (2 : ENNReal) ≠ ⊤)]
              simp
  have hrisk := risk_eq_uniform_path_lintegral P I x hxQuery hxMeas
  change risk I (algorithm P) = c *
    (∫⁻ seeds : Fin (responseCount P) → Seed,
      ∑ r : Fin P.T,
        ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖ ∂seedLaw) at hrisk
  rw [hrisk]
  calc
    c * (∫⁻ seeds : Fin (responseCount P) → Seed,
      ∑ r : Fin P.T,
        ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖ ∂seedLaw) ≤
      c * (ENNReal.ofReal K +
        2 * ∫⁻ seeds : Fin (responseCount P) → Seed,
          ENNReal.ofReal (E seeds) ∂seedLaw) :=
            mul_le_mul' le_rfl hsumBound
    _ = c * ENNReal.ofReal K +
        2 * (c * ∫⁻ seeds : Fin (responseCount P) → Seed,
          ENNReal.ofReal (E seeds) ∂seedLaw) := by ring
    _ ≤ c * ENNReal.ofReal K + 2 * ENNReal.ofReal (ε / 8) := by
      have herr : c * (∫⁻ seeds : Fin (responseCount P) → Seed,
          ENNReal.ofReal (E seeds) ∂seedLaw) ≤
          ENNReal.ofReal (ε / 8) := herror
      have herr2 : 2 * (c * (∫⁻ seeds : Fin (responseCount P) → Seed,
          ENNReal.ofReal (E seeds) ∂seedLaw)) ≤
          2 * ENNReal.ofReal (ε / 8) :=
        mul_le_mul_of_nonneg_left herr (bot_le : (0 : ENNReal) ≤ 2)
      exact add_le_add le_rfl herr2
    _ ≤ ENNReal.ofReal ε := hbudget

end

end HeavyTailedNoise.UpperK1
