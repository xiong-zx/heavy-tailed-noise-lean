import HeavyTailedNoise.Upper.K1.InitialMemoryRadial
import HeavyTailedNoise.Upper.K1.NoiseScale

/-!
The literal physical initialization count pays for the terminal cutoff's
`2-p` interpolation factor. This scalar statement covers `p=2`, `σ=0`,
and the optional zero-response branch without changing the schedule.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

/-- With the manuscript's `nI`, the terminal-cutoff p-to-2 conversion costs
at most `ε²/CI` per unit residual `ν^p`. The theorem refers to the actual
rounded batch size, not a real-valued surrogate. -/
theorem paperSchedule_initialVarianceScale_le_epsilon_sq
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p ∧ p ≤ 2)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    (paperNu σ ε) ^ p *
      (P.tau ⟨P.J, Nat.lt_succ_self P.J⟩) ^ (2 - p) *
        (P.nI : ℝ)⁻¹ ≤ ε ^ 2 / CI := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  let ν : ℝ := paperNu σ ε
  let S : ℝ := paperS σ ε
  let U : ℝ := paperU p σ ε Ctail
  let a : ℝ := 2 - p
  have hν : 0 < ν := paperNu_pos hε
  have hS : 0 < S := paperS_pos σ ε
  have hU : 0 < U := paperU_pos hε
  have hτ : P.tau ⟨P.J, Nat.lt_succ_self P.J⟩ = ν * U := by
    change paperTau σ ε (paperJ p σ ε Ctail) =
      paperNu σ ε * paperU p σ ε Ctail
    unfold paperU
    rw [div_eq_mul_inv]
    calc
      paperTau σ ε (paperJ p σ ε Ctail) =
          paperTau σ ε (paperJ p σ ε Ctail) *
            (paperNu σ ε * (paperNu σ ε)⁻¹) := by
              rw [mul_inv_cancel₀ (ne_of_gt hν)]
              ring
      _ = paperNu σ ε *
            (paperTau σ ε (paperJ p σ ε Ctail) *
              (paperNu σ ε)⁻¹) := by ring
  have hνpow : ν ^ p * ν ^ a = ν ^ 2 := by
    rw [← Real.rpow_add hν]
    have hpa : p + a = (2 : ℝ) := by dsimp [a]; ring
    rw [hpa]
    simp
  have hpow : ν ^ p *
      (P.tau ⟨P.J, Nat.lt_succ_self P.J⟩) ^ a =
      ν ^ 2 * U ^ a := by
    rw [hτ, Real.mul_rpow hν.le hU.le]
    rw [← mul_assoc, hνpow]
  have hnI : CI * S ^ 2 * U ^ a ≤ (P.nI : ℝ) := by
    change CI * (paperS σ ε) ^ 2 *
      (paperU p σ ε Ctail) ^ (paperA p) ≤
      (paperInitialBatchSize p σ ε Ctail CI : ℝ)
    exact Nat.le_ceil _
  have hνS : ν = ε * S := paperNu_eq_eps_mul_paperS hε
  have hmain :
      (ν ^ p *
        (P.tau ⟨P.J, Nat.lt_succ_self P.J⟩) ^ a) * CI ≤
      ε ^ 2 * (P.nI : ℝ) := by
    rw [hpow, hνS]
    calc
      (ε * S) ^ 2 * U ^ a * CI =
          ε ^ 2 * (CI * S ^ 2 * U ^ a) := by ring
      _ ≤ ε ^ 2 * (P.nI : ℝ) :=
        mul_le_mul_of_nonneg_left hnI (sq_nonneg ε)
  have hnIpos : (0 : ℝ) < P.nI := Nat.cast_pos.mpr P.nI_pos
  change (ν ^ p *
    (P.tau ⟨P.J, Nat.lt_succ_self P.J⟩) ^ a) *
      (P.nI : ℝ)⁻¹ ≤ ε ^ 2 / CI
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ hnIpos).2
  have hscaled :
      ν ^ p * (P.tau ⟨P.J, Nat.lt_succ_self P.J⟩) ^ a ≤
        ε ^ 2 * (P.nI : ℝ) / CI :=
    (le_div_iff₀ hCI).2 (by nlinarith [hmain])
  simpa only [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc]
    using hscaled

end

end HeavyTailedNoise.UpperK1
