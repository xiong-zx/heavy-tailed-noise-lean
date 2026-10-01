import HeavyTailedNoise.Upper.K1.EMAMeanAlgebra

/-!
Finite source-weight formula in manuscript equation `ema-18`. The initial
term has weight `b^t`; the range sum uses source time `u+1` and weight
`α b^(t-1-u)`. This is the algebraic mean component, not another runtime EMA.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

def bandMeanClosedForm {d : ℕ} (j : Fin P.J)
    (μ : ℕ → Point d) (t : ℕ) : Point d :=
  (1 - P.alpha j) ^ t • μ 1 +
    ∑ u ∈ Finset.range t,
      (P.alpha j * (1 - P.alpha j) ^ (t - 1 - u)) • μ (u + 1)

theorem bandMeanClosedForm_succ {d : ℕ} (j : Fin P.J)
    (μ : ℕ → Point d) (t : ℕ) :
    bandMeanClosedForm P j μ (t + 1) =
      (1 - P.alpha j) • bandMeanClosedForm P j μ t +
        P.alpha j • μ (t + 1) := by
  let b := 1 - P.alpha j
  have hsum :
      (∑ u ∈ Finset.range t,
        (P.alpha j * b ^ (t - u)) • μ (u + 1)) =
      b • ∑ u ∈ Finset.range t,
        (P.alpha j * b ^ (t - 1 - u)) • μ (u + 1) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hut : u < t := Finset.mem_range.mp hu
    have hexp : t - u = (t - 1 - u) + 1 := by omega
    have hcoef : P.alpha j * b ^ (t - u) =
        b * (P.alpha j * b ^ (t - 1 - u)) := by
      rw [hexp, pow_succ]
      ring
    rw [hcoef, smul_smul]
  have hbase : b ^ (t + 1) • μ 1 = b • (b ^ t • μ 1) := by
    rw [pow_succ, smul_smul, mul_comm]
  have hlast :
      (P.alpha j * b ^ ((t + 1) - 1 - t)) • μ (t + 1) =
        P.alpha j • μ (t + 1) := by simp
  dsimp [bandMeanClosedForm, b] at hsum hbase hlast ⊢
  rw [Finset.sum_range_succ, hlast, hsum, hbase, smul_add]
  abel

/-- Exact finite formula `b_j^t μ_j(1) + Σ_{u=1}^t α_j b_j^{t-u} μ_j(u)`.
The `Finset.range` index is `u-1`. -/
theorem bandMeanComponent_eq_closedForm {d : ℕ} (j : Fin P.J)
    (μ : ℕ → Point d) (t : ℕ) :
    bandMeanComponent P j μ t = bandMeanClosedForm P j μ t := by
  induction t with
  | zero => simp [bandMeanComponent, bandMeanClosedForm]
  | succ t ih =>
      rw [bandMeanComponent_succ, ih, bandMeanClosedForm_succ]

end

end HeavyTailedNoise.UpperK1
