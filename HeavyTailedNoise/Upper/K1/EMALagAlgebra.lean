import HeavyTailedNoise.Upper.K1.EMAMeanAlgebra

/-!
The finite source-mean lag identity in manuscript equation `ema-19`. Source
means are arbitrary vectors indexed by time; no stochastic conditional
expectation is taken at a future path. The same formula includes `α=1`.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

/-- For current time `t+1`, source move `u+1 → u+2` has coefficient
`b^(t-u)`, exactly `b^((t+1)-(u+1))` in the manuscript. -/
def emaLagSum {d : ℕ} (b : ℝ) (μ : ℕ → Point d) (t : ℕ) : Point d :=
  ∑ u ∈ Finset.range t, b ^ (t - u) • (μ (u + 2) - μ (u + 1))

theorem emaLagSum_succ {d : ℕ} (b : ℝ) (μ : ℕ → Point d) (t : ℕ) :
    emaLagSum b μ (t + 1) =
      b • emaLagSum b μ t + b • (μ (t + 2) - μ (t + 1)) := by
  have hsum :
      (∑ u ∈ Finset.range t,
        b ^ ((t + 1) - u) • (μ (u + 2) - μ (u + 1))) =
      b • ∑ u ∈ Finset.range t,
        b ^ (t - u) • (μ (u + 2) - μ (u + 1)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hut : u < t := Finset.mem_range.mp hu
    have hindex : (t + 1) - u = (t - u) + 1 := by omega
    calc
      b ^ ((t + 1) - u) • (μ (u + 2) - μ (u + 1)) =
          (b ^ (t - u) * b) • (μ (u + 2) - μ (u + 1)) := by
            rw [hindex, pow_succ]
      _ = (b * b ^ (t - u)) • (μ (u + 2) - μ (u + 1)) := by
        rw [mul_comm]
      _ = b • (b ^ (t - u) • (μ (u + 2) - μ (u + 1))) := by
        rw [smul_smul]
  calc
    emaLagSum b μ (t + 1) =
        (∑ u ∈ Finset.range t,
          b ^ ((t + 1) - u) • (μ (u + 2) - μ (u + 1))) +
          b • (μ (t + 2) - μ (t + 1)) := by
            simp [emaLagSum, Finset.sum_range_succ]
    _ = b • emaLagSum b μ t + b • (μ (t + 2) - μ (t + 1)) := by
      rw [hsum]
      rfl

variable {q : ℝ} (P : Schedule q)

/-- Exact one-band mean-lag identity. The left side is the algebraic EMA mean
component minus the current source mean; the right side telescopes earlier
source moves with powers of the actual retention coefficient. -/
theorem bandMeanComponent_sub_source {d : ℕ} (j : Fin P.J)
    (μ : ℕ → Point d) (t : ℕ) :
    bandMeanComponent P j μ (t + 1) - μ (t + 1) =
      -emaLagSum (1 - P.alpha j) μ t := by
  induction t with
  | zero =>
      change (1 - P.alpha j) • μ 1 + P.alpha j • μ 1 - μ 1 =
        -emaLagSum (1 - P.alpha j) μ 0
      simp only [emaLagSum, Finset.range_zero, Finset.sum_empty, neg_zero]
      rw [← add_smul]
      have hcoef : 1 - P.alpha j + P.alpha j = (1 : ℝ) := by ring
      rw [hcoef, one_smul, sub_self]
  | succ t ih =>
      let b := 1 - P.alpha j
      have hrec :
          bandMeanComponent P j μ (t + 2) - μ (t + 2) =
            b • (bandMeanComponent P j μ (t + 1) - μ (t + 1)) -
              b • (μ (t + 2) - μ (t + 1)) := by
        calc
          bandMeanComponent P j μ (t + 2) - μ (t + 2) =
              b • bandMeanComponent P j μ (t + 1) +
                P.alpha j • μ (t + 2) - μ (t + 2) := rfl
          _ = b • bandMeanComponent P j μ (t + 1) +
                (P.alpha j - 1) • μ (t + 2) := by
                  calc
                    _ = b • bandMeanComponent P j μ (t + 1) +
                          (P.alpha j • μ (t + 2) - μ (t + 2)) := by abel
                    _ = b • bandMeanComponent P j μ (t + 1) +
                          (P.alpha j - 1) • μ (t + 2) := by
                            have hαμ : (P.alpha j - 1) • μ (t + 2) =
                                P.alpha j • μ (t + 2) - μ (t + 2) := by
                              rw [sub_smul, one_smul]
                            rw [hαμ]
          _ = b • bandMeanComponent P j μ (t + 1) -
                b • μ (t + 2) := by
                  have hα : P.alpha j - 1 = -b := by dsimp [b]; ring
                  rw [hα, neg_smul]
                  rfl
          _ = b • (bandMeanComponent P j μ (t + 1) - μ (t + 2)) := by
            rw [smul_sub]
          _ = b • ((bandMeanComponent P j μ (t + 1) - μ (t + 1)) -
                (μ (t + 2) - μ (t + 1))) := by
                  congr 1
                  abel
          _ = b • (bandMeanComponent P j μ (t + 1) - μ (t + 1)) -
                b • (μ (t + 2) - μ (t + 1)) := by rw [smul_sub]
      rw [hrec, ih, emaLagSum_succ]
      simp only [smul_neg]
      abel

end

end HeavyTailedNoise.UpperK1
