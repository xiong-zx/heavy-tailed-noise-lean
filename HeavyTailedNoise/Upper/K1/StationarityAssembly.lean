import HeavyTailedNoise.Upper.Foundations.NormalizedDescent
import HeavyTailedNoise.Upper.K1.UniformOutput
import HeavyTailedNoise.Upper.K1.PhysicalParameters

/-!
Conditional terminal assembly for the literal strict-K=1 method. The finite
descent telescope needs only runtime steps before the declared horizon. The
exact risk identity uses the algorithm's existing independent uniform output.
Later theorems must prove that the actual path meets the explicit step and
estimation-error premises; this file does not assume a new oracle condition.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Finite-horizon form of the built normalized descent lemma. Requiring the
update only for `t<T` matches the physical run, which draws no further batch
after the final output. -/
theorem Admissible.finite_normalized_descent_sum_gap
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    {h : ℝ} (hh : 0 ≤ h) (T : ℕ)
    (x hhat : ℕ → Point d)
    (hstep : ∀ t < T, x (t + 1) = x t - h • direction (hhat t))
    (hx0 : x 0 = 0) :
    h * ∑ t ∈ Finset.range T, ‖I.objective.grad (x t)‖ ≤
      Δ + 2 * h * ∑ t ∈ Finset.range T,
        ‖hhat t - I.objective.grad (x t)‖ + (T : ℝ) * Lbar * h ^ 2 := by
  have hsum : ∀ n : ℕ, (∀ t < n, x (t + 1) =
      x t - h • direction (hhat t)) →
      h * ∑ t ∈ Finset.range n, ‖I.objective.grad (x t)‖ ≤
        I.objective.value (x 0) - I.objective.value (x n) +
          2 * h * ∑ t ∈ Finset.range n,
            ‖hhat t - I.objective.grad (x t)‖ +
          (n : ℝ) * Lbar * h ^ 2 := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hprefix : ∀ t < n, x (t + 1) =
            x t - h • direction (hhat t) := by
          intro t ht
          exact hn t (by omega)
        have hprev := ih hprefix
        have hlocal := I.normalized_step_descent hh (x n) (hhat n)
        rw [← hn n (by omega)] at hlocal
        simp only [Finset.sum_range_succ, Nat.cast_succ] at ⊢
        nlinarith [hprev, hlocal]
  have htotal := hsum T hstep
  rw [hx0] at htotal
  have hgap := I.objective.gap (x T)
  linarith

variable {q : ℝ} (P : Schedule q)

/-- This is exactly the runtime query appearing in `UniformOutput`, with its
private index fixed to the canonical anchor. It is a name for an existing
query, not a second decision rule. -/
def canonicalRuntimePoint {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (r : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) : Point d :=
  query P (batchStart P r.val)
    (runTranscript O (algorithm (d := d) P)
      (⟨0, P.T_pos⟩ : Fin P.T) (batchStart P r.val)
      (fun j : Fin (batchStart P r.val) =>
        seeds ⟨j.val, lt_trans j.isLt (outputIndex P r).isLt⟩))

/-- Uniform output converts the mean of runtime gradient norms into the
actual `risk` of the single algorithm. The path/query identification and
coordinate measurability are explicit intermediate obligations. -/
theorem risk_eq_uniform_path_lintegral
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x : (Fin (responseCount P) → Seed) → ℕ → Point d)
    (hxQuery : ∀ seeds (r : Fin P.T),
      x seeds r.val = canonicalRuntimePoint P I.oracle r seeds)
    (hxMeas : ∀ r : Fin P.T, Measurable (fun seeds => x seeds r.val)) :
    risk I (algorithm P) =
      (P.T : ENNReal)⁻¹ *
        ∫⁻ seeds : Fin (responseCount P) → Seed,
          ∑ r : Fin P.T,
            ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖
          ∂freshSeedLaw I.oracle (responseCount P) := by
  let μ := freshSeedLaw I.oracle (responseCount P)
  let c : ENNReal := (P.T : ENNReal)⁻¹
  have hmeas (r : Fin P.T) :
      Measurable (fun seeds : Fin (responseCount P) → Seed =>
        ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖) :=
    ENNReal.measurable_ofReal.comp
      ((I.objective.continuous_grad.measurable.comp (hxMeas r)).norm)
  calc
    risk I (algorithm P) =
        ∑ r : Fin P.T,
          (∫⁻ seeds : Fin (responseCount P) → Seed,
            ENNReal.ofReal ‖I.objective.grad
              (canonicalRuntimePoint P I.oracle r seeds)‖ ∂μ) * c := by
              simpa only [μ, c, canonicalRuntimePoint] using
                risk_eq_uniform_runtime_start_lintegrals I P
    _ = ∑ r : Fin P.T,
          (∫⁻ seeds : Fin (responseCount P) → Seed,
            ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖ ∂μ) * c := by
              apply Finset.sum_congr rfl
              intro r hr
              congr 1
              apply lintegral_congr
              intro seeds
              rw [hxQuery seeds r]
    _ = (∑ r : Fin P.T,
          ∫⁻ seeds : Fin (responseCount P) → Seed,
            ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖ ∂μ) * c := by
              rw [Finset.sum_mul]
    _ = (∫⁻ seeds : Fin (responseCount P) → Seed,
          ∑ r : Fin P.T,
            ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖ ∂μ) * c := by
              rw [lintegral_finsetSum Finset.univ (fun r _ => hmeas r)]
    _ = c * ∫⁻ seeds : Fin (responseCount P) → Seed,
          ∑ r : Fin P.T,
            ENNReal.ofReal ‖I.objective.grad (x seeds r.val)‖ ∂μ := by
              rw [mul_comm]

end

end HeavyTailedNoise.UpperK1
