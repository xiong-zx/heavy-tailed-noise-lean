import HeavyTailedNoise.Upper.K1.FiniteBatchVariance

/-!
The stochastic runtime-kernel component at one fixed output time `t`.
`kernelPhi P k` already contains the low-band lag-zero term and every high-band
EMA coefficient. This component excludes initialization high memory, mean
tracking drift, and terminal clipping bias.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Every runtime source index `u : Fin t` precedes the fixed output time. -/
theorem runtimeSourceIndex_lt {t : ℕ} {ht : t ≤ P.T} (u : Fin t) :
    (u.castLE ht).val < t := by
  simpa only [Fin.val_castLE] using u.isLt

/-- The combined kernel has lag zero exactly for the latest runtime batch. -/
theorem runtimeKernelLag_zero_iff {t : ℕ} (u : Fin t) :
    t - 1 - u.val = 0 ↔ u.val + 1 = t := by
  omega

/-- Sum of the complete centered shared-kernel errors of runtime batches
`0,...,t-1`, with the exact lag of each source at output time `t`. -/
def runtimeKernelNoise {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ) (ht : t ≤ P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) : Point d :=
  ∑ u : Fin t,
    actualKernelBatchError P O (u.castLE ht) (t - 1 - u.val) z

/-- Exact finite-time Pythagorean identity for the stochastic runtime-kernel
component. No independence among scales inside `kernelPhi` is used. -/
theorem runtimeKernelNoise_sq_eq_sum
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ) (ht : t ≤ P.T) :
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ‖runtimeKernelNoise P O t ht z‖ ^ 2
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) =
      ∑ u : Fin t,
        ∫ z : Fin P.T × (Fin (responseCount P) → Seed),
          ‖actualKernelBatchError P O (u.castLE ht) (t - 1 - u.val) z‖ ^ 2
          ∂((algorithm (d := d) P).privateLaw.prod
            (freshSeedLaw O (responseCount P))) := by
  have h := finite_actualKernelBatchError_sq_eq_sum P O ht
    (fun _ : Fin t => (1 : ℝ)) (fun u : Fin t => t - 1 - u.val)
  simpa only [runtimeKernelNoise, one_smul, one_pow, one_mul] using h

/-- Runtime-kernel stochastic error is bounded by the sum of the complete
one-source `Φ` second moments with one shared batch factor `1/P.n`. -/
theorem runtimeKernelNoise_sq_le_sources
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ) (ht : t ≤ P.T) :
    (∫ z : Fin P.T × (Fin (responseCount P) → Seed),
      ‖runtimeKernelNoise P O t ht z‖ ^ 2
      ∂((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw O (responseCount P)))) ≤
      ∑ u : Fin t, (P.n : ℝ)⁻¹ *
        ∫ H : BatchHistory P d (u.castLE ht),
          ∫ ξ : Seed,
            ‖kernelPhi P (t - 1 - u.val)
              (O.response (batchDecision P (u.castLE ht) H) ξ -
                batchCenter P (u.castLE ht) H)‖ ^ 2
            ∂O.law ∂batchPastHistoryLaw P O (u.castLE ht) := by
  have h := finite_actualKernelBatchError_sq_le_sources P O ht
    (fun _ : Fin t => (1 : ℝ)) (fun u : Fin t => t - 1 - u.val)
  simpa only [runtimeKernelNoise, one_smul, one_pow, one_mul] using h

end

end HeavyTailedNoise.UpperK1
