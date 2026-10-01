import HeavyTailedNoise.Upper.K1.Algorithm

/-!
The exact one-source shared-batch kernel of the frozen `alg:k1` method.
`kernelPhi P k` is applied to one returned residual as a whole. A later
probability proof must never replace the square of its band sum by a sum of
independent band variances.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Manuscript `Ψ_k`: all high-band EMA contributions from one source vector. -/
def kernelPsi {d : ℕ} (k : ℕ) (z : Point d) : Point d :=
  ∑ j : Fin P.J,
    (P.alpha j * (1 - P.alpha j) ^ k) • highBand P j z

/-- Manuscript `Φ_k`: the low-band term occurs only at lag zero. -/
def kernelPhi {d : ℕ} (k : ℕ) (z : Point d) : Point d :=
  if k = 0 then lowBand P z + kernelPsi P k z else kernelPsi P k z

theorem measurable_kernelPsi {d : ℕ} (k : ℕ) :
    Measurable (kernelPsi (d := d) P k) := by
  classical
  unfold kernelPsi
  apply Finset.measurable_sum
  intro j hj
  have hc : Measurable (fun _ : Point d => P.alpha j * (1 - P.alpha j) ^ k) :=
    measurable_const
  exact hc.smul (measurable_highBand P j)

theorem measurable_kernelPhi {d : ℕ} (k : ℕ) :
    Measurable (kernelPhi (d := d) P k) := by
  by_cases hk : k = 0
  · subst k
    have hfun : kernelPhi (d := d) P 0 =
        fun z => lowBand P z + kernelPsi P 0 z := by
      funext z
      simp [kernelPhi]
    rw [hfun]
    exact (measurable_lowBand P).add (measurable_kernelPsi P 0)
  · have hfun : kernelPhi (d := d) P k = kernelPsi P k := by
      funext z
      simp [kernelPhi, hk]
    rw [hfun]
    exact measurable_kernelPsi P k

theorem kernelPhi_zero {d : ℕ} (z : Point d) :
    kernelPhi P 0 z = lowBand P z + kernelPsi P 0 z := by
  simp [kernelPhi]

theorem kernelPhi_succ {d : ℕ} (k : ℕ) (z : Point d) :
    kernelPhi P (k + 1) z = kernelPsi P (k + 1) z := by
  simp [kernelPhi]

end

end HeavyTailedNoise.UpperK1
