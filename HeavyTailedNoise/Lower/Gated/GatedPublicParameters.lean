import HeavyTailedNoise.Lower.Gated.LowerBoundFullDimensionChoice
import HeavyTailedNoise.Lower.Gated.ScaledObjectiveGap

/-!
Public parameters for the finite-cap gated lower-bound application.

A=LΔ/ε², S=σ/ε, the actual chain floor T, the final dimension d, and the
actual stage floor m are selected only from public L,Δ,ε,σ,N.  No algorithm,
private tape, oracle sample, probability bound, or expected stopping time is
an input.  The conservative response coefficient 10⁻²⁵ leaves enough slack
for the additional response-free output decision in 4(N+1)≤Tm.
-/

namespace HeavyTailedNoise

noncomputable section

set_option autoImplicit false

def gatedPublicRateConstant : ℝ := 1 / 10 ^ 25

/-- One tenth of the checked quarter-budget coefficient absorbs the output
decision using the actual stage floors, including the N=0 case. -/
theorem gatedFixedDecisionBudget_of_public_responseBudget
    {A S : ℝ} {d N : ℕ} (hA : 0 ≤ A)
    (hT64 : 64 ≤ gatedChainLength A) (hd : 0 < d)
    (hdim : 2 * gatedChainLength A ≤ d)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / (16 * 300 ^ 2)))
    (hN : (N : ℝ) ≤ gatedPublicRateConstant * A * S ^ 2) :
    4 * (N + 1) ≤ gatedChainLength A * gatedStageLength d (gatedChainLength A) S := by
  have hquarter := gated_quarter_budget_actual hA hT64 hd hdim hlarge
  have hm2 := gatedStageLength_ge_two hd hdim hlarge
  have hten : (10 : ℝ) * N ≤
      (gatedChainLength A : ℝ) * gatedStageLength d (gatedChainLength A) S / 4 := by
    calc
      (10 : ℝ) * N ≤ 10 * (gatedPublicRateConstant * A * S ^ 2) :=
        mul_le_mul_of_nonneg_left hN (by norm_num)
      _ = (1 / 10 ^ 24 : ℝ) * A * S ^ 2 := by
        unfold gatedPublicRateConstant
        norm_num
        ring
      _ ≤ (gatedChainLength A : ℝ) * gatedStageLength d (gatedChainLength A) S / 4 := hquarter
  have hprodNat : 128 ≤ gatedChainLength A * gatedStageLength d (gatedChainLength A) S := by
    have h := Nat.mul_le_mul hT64 hm2
    norm_num at h
    exact h
  have hprod : (128 : ℝ) ≤
      (gatedChainLength A : ℝ) * gatedStageLength d (gatedChainLength A) S := by
    exact_mod_cast hprodNat
  have hreal : (4 : ℝ) * ((N : ℝ) + 1) ≤
      (gatedChainLength A : ℝ) * gatedStageLength d (gatedChainLength A) S := by
    linarith
  exact_mod_cast hreal

/-- The actual chain floor agrees with the physical manuscript formula. -/
theorem gatedChainLength_eq_physical_floor (L Δ ε : ℝ) :
    gatedChainLength (L * Δ / ε ^ 2) = ⌊L * Δ / (330240000 * ε ^ 2)⌋₊ := by
  unfold gatedChainLength
  rw [div_div, mul_comm (ε ^ 2) (330240000 : ℝ)]

theorem gatedPublic_noiseAmplitude_identity (σ ε : ℝ) (d : ℕ) :
    ((σ / ε) / 80) / Real.sqrt d = σ / (80 * ε * Real.sqrt d) := by
  rw [div_div, div_div]
  congr 1
  ring

/-- One public packet supplies instance legality, pinhole and accident
dimension conditions, and the deterministic response-plus-output budget. -/
theorem gatedPublicParameters
    (L Δ ε σ : ℝ) (N : ℕ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσε : ε ≤ σ)
    (hT64 : 64 ≤ gatedChainLength (L * Δ / ε ^ 2))
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * ((σ / ε) / 80) ^ 2 / (16 * 300 ^ 2)))
    (hN : (N : ℝ) ≤ gatedPublicRateConstant * (L * Δ / ε ^ 2) * (σ / ε) ^ 2) :
    let A := L * Δ / ε ^ 2
    let S := σ / ε
    let T := gatedChainLength A
    let d := gatedFullDimensionChoice T N S
    let m := gatedStageLength d T S
    0 < A ∧ 0 < T ∧ T = ⌊L * Δ / (330240000 * ε ^ 2)⌋₊ ∧
      330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ ∧
      1 ≤ S ∧ 0 < S ∧ (S / 80) / Real.sqrt d = σ / (80 * ε * Real.sqrt d) ∧
      0 < d ∧ 2 * T ≤ d ∧ N ≤ d ∧ 2 ≤ m ∧
      21400 * (1 + Real.log (2 * (m : ℝ))) ≤ ((d - T : ℕ) : ℝ) ∧
      4096 * (hardRadius T) ^ 2 ≤ ((d - T : ℕ) : ℝ) ∧
      2 * (N + 2 : ℕ) * T * Real.exp (-((d - T : ℕ) : ℝ) /
        (2048 * (hardRadius T) ^ 2)) ≤ (1 / 10 : ℝ) ∧
      4 * (N + 1) ≤ T * m ∧ 4 * N ≤ T * m := by
  let A := L * Δ / ε ^ 2
  let S := σ / ε
  let T := gatedChainLength A
  let d := gatedFullDimensionChoice T N S
  let m := gatedStageLength d T S
  have hA : 0 < A := by dsimp [A]; positivity
  have hT : 0 < T := by dsimp [T, A]; omega
  have hS1 : 1 ≤ S := by
    dsimp [S]
    apply (le_div_iff₀ hε).2
    simpa only [one_mul] using hσε
  have hS : 0 < S := (by norm_num : (0 : ℝ) < 1).trans_le hS1
  have hfloor : T = ⌊L * Δ / (330240000 * ε ^ 2)⌋₊ :=
    gatedChainLength_eq_physical_floor L Δ ε
  have hgap : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ := by
    rw [hfloor]
    exact gatedChainLength_budget L ε Δ hL hε hΔ.le
  obtain ⟨hd, hdim, hNd, hm2, hlog, haccdim, hacc⟩ :=
    gatedFullDimensionChoice_conditions hT N S hlarge
  have hdecision : 4 * (N + 1) ≤ T * m :=
    gatedFixedDecisionBudget_of_public_responseBudget hA.le hT64 hd hdim hlarge hN
  have hresponse : 4 * N ≤ T * m := by omega
  exact ⟨hA, hT, hfloor, hgap, hS1, hS,
    gatedPublic_noiseAmplitude_identity σ ε d, hd, hdim, hNd, hm2,
    hlog, haccdim, hacc, hdecision, hresponse⟩

end

end HeavyTailedNoise
