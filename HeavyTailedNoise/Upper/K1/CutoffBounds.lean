import HeavyTailedNoise.Upper.K1.PhysicalParameters

/-!
Bounds for the least dyadic cutoff used by the literal `alg:k1` schedule.
These are deterministic and retain the manuscript's `J=0` boundary.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem paperTailTarget_ge_twelve {p σ ε Ctail : ℝ}
    (hp : 1 < p) (hCtail : 12 ≤ Ctail) :
    12 ≤ paperTailTarget p σ ε Ctail := by
  have hS := one_le_paperS σ ε
  have hden : 0 < p - 1 := sub_pos.mpr hp
  have hexp : 0 ≤ 1 / (p - 1) := by positivity
  have hpow := Real.one_le_rpow hS hexp
  have hCnonneg : 0 ≤ Ctail := by linarith
  calc
    (12 : ℝ) ≤ Ctail := hCtail
    _ = Ctail * 1 := by ring
    _ ≤ Ctail * (paperS σ ε) ^ (1 / (p - 1)) :=
      mul_le_mul_of_nonneg_left hpow hCnonneg
    _ = paperTailTarget p σ ε Ctail := rfl

theorem paperU_eq_dyadic {p σ ε Ctail : ℝ} (hε : 0 < ε) :
    paperU p σ ε Ctail = 12 * (2 : ℝ) ^ paperJ p σ ε Ctail := by
  have hν : paperNu σ ε ≠ 0 := ne_of_gt (paperNu_pos hε)
  unfold paperU paperTau
  field_simp [hν]

theorem paperU_reaches_target {p σ ε Ctail : ℝ} (hε : 0 < ε) :
    paperTailTarget p σ ε Ctail ≤ paperU p σ ε Ctail := by
  rw [paperU_eq_dyadic hε]
  exact paperJ_reaches_target p σ ε Ctail

/-- The least cutoff lies in the manuscript's factor-two interval, including
the `J=0` case. -/
theorem paperU_lt_two_target {p σ ε Ctail : ℝ}
    (hp : 1 < p) (hε : 0 < ε) (hCtail : 12 ≤ Ctail) :
    paperU p σ ε Ctail < 2 * paperTailTarget p σ ε Ctail := by
  have htarget := paperTailTarget_ge_twelve (σ := σ) (ε := ε) hp hCtail
  by_cases hJ : paperJ p σ ε Ctail = 0
  · rw [paperU_eq_dyadic hε, hJ]
    norm_num
    linarith
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hJ
    have hprev : ¬ paperTailTarget p σ ε Ctail ≤ 12 * (2 : ℝ) ^ j := by
      apply paperJ_is_least p σ ε Ctail
      rw [hj]
      exact Nat.lt_succ_self j
    have hlt : 12 * (2 : ℝ) ^ j < paperTailTarget p σ ε Ctail :=
      lt_of_not_ge hprev
    rw [paperU_eq_dyadic hε, hj, pow_succ]
    nlinarith

end

end HeavyTailedNoise.UpperK1
