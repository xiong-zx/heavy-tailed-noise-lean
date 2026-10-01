import HeavyTailedNoise.Upper.K1.EMAClosedForm

/-!
Exact finite EMA decomposition with an arbitrary initial memory. The source
mean, initial sample error and runtime centered batch errors are kept separate.
This algebra introduces neither another algorithm nor an independence claim.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

def bandCenteredNoise {d : ℕ} (j : Fin P.J)
    (E : ℕ → Point d) (t : ℕ) : Point d :=
  ∑ u ∈ Finset.range t,
    (P.alpha j * (1 - P.alpha j) ^ (t - 1 - u)) • E u

theorem bandCenteredNoise_succ {d : ℕ} (j : Fin P.J)
    (E : ℕ → Point d) (t : ℕ) :
    bandCenteredNoise P j E (t + 1) =
      (1 - P.alpha j) • bandCenteredNoise P j E t +
        P.alpha j • E t := by
  let b := 1 - P.alpha j
  have hsum :
      (∑ u ∈ Finset.range t,
        (P.alpha j * b ^ (t - u)) • E u) =
      b • ∑ u ∈ Finset.range t,
        (P.alpha j * b ^ (t - 1 - u)) • E u := by
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
  have hlast :
      (P.alpha j * b ^ ((t + 1) - 1 - t)) • E t =
        P.alpha j • E t := by simp
  dsimp [bandCenteredNoise, b] at hsum hlast ⊢
  rw [Finset.sum_range_succ, hlast, hsum]

theorem ema_recursion_eq_mean_initial_noise {d : ℕ}
    (j : Fin P.J) (M B μ : ℕ → Point d) (T : ℕ)
    (hrec : ∀ t < T,
      M (t + 1) = (1 - P.alpha j) • M t + P.alpha j • B t)
    (t : ℕ) (ht : t ≤ T) :
    M t = bandMeanComponent P j μ t +
      (1 - P.alpha j) ^ t • (M 0 - μ 1) +
      bandCenteredNoise P j (fun u => B u - μ (u + 1)) t := by
  induction t with
  | zero =>
      simp only [bandMeanComponent_zero, pow_zero, one_smul,
        bandCenteredNoise, Finset.range_zero, Finset.sum_empty]
      abel
  | succ t ih =>
      have htT : t < T := by omega
      have hi := ih (Nat.le_of_lt htT)
      have hpow : (1 - P.alpha j) ^ (t + 1) =
          (1 - P.alpha j) * (1 - P.alpha j) ^ t := by
        rw [pow_succ, mul_comm]
      rw [hrec t htT, hi, bandMeanComponent_succ,
        bandCenteredNoise_succ, hpow]
      simp only [smul_add, smul_sub, smul_smul]
      abel

end

end HeavyTailedNoise.UpperK1
