import HeavyTailedNoise.Upper.K1.EMACenteredAlgebra

/-!
Finite time/band reordering for the complete shared-source runtime kernel.
The low-band term occurs in exactly the latest batch; the high-band terms
are the same finite EMA noise sums. This is purely vector algebra.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem finite_kernel_sum_eq_low_and_bandNoise {d : ℕ}
    (L : ℕ → Point d) (E : Fin P.J → ℕ → Point d)
    (t : ℕ) (ht : 0 < t) :
    (∑ u ∈ Finset.range t,
      ((if t - 1 - u = 0 then L u else 0) +
        ∑ j : Fin P.J,
          (P.alpha j * (1 - P.alpha j) ^ (t - 1 - u)) • E j u)) =
      L (t - 1) + ∑ j : Fin P.J, bandCenteredNoise P j (E j) t := by
  have hlow :
      (∑ u ∈ Finset.range t, (if t - 1 - u = 0 then L u else 0)) =
        L (t - 1) := by
    calc
      (∑ u ∈ Finset.range t, (if t - 1 - u = 0 then L u else 0)) =
          (if t - 1 - (t - 1) = 0 then L (t - 1) else 0) := by
        apply Finset.sum_eq_single (t - 1)
        · intro u hu hne
          have hut : u < t := Finset.mem_range.mp hu
          have hlag : t - 1 - u ≠ 0 := by omega
          simp only [hlag, ite_false]
        · intro hnot
          have hmem : t - 1 ∈ Finset.range t := Finset.mem_range.mpr (by omega)
          exact False.elim (hnot hmem)
      _ = L (t - 1) := by simp
  rw [Finset.sum_add_distrib, hlow]
  congr 1
  rw [Finset.sum_comm]
  rfl

end

end HeavyTailedNoise.UpperK1
