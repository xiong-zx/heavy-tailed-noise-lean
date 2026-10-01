import HeavyTailedNoise.Upper.K1.KernelBatch
import HeavyTailedNoise.Upper.K1.PhysicalParameters

/-!
Conservative shell geometry for the literal dyadic schedule. We use triangle
bounds on each shell rather than a separate radial-collinearity implementation.
Together with the exact zero support, this retains the no-log kernel rate.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem highBand_zero_of_norm_le {d : ℕ} (j : Fin P.J) (z : Point d)
    (hmono : P.tau j.castSucc ≤ P.tau j.succ)
    (hz : ‖z‖ ≤ P.tau j.castSucc) : highBand P j z = 0 := by
  have hlo := upperClip_eq_self_of_norm_le (P.tau_pos j.castSucc) hz
  have hhi := upperClip_eq_self_of_norm_le (P.tau_pos j.succ) (hz.trans hmono)
  simp [highBand, upperShell, hlo, hhi]

theorem highBand_norm_le_three_low {d : ℕ} (j : Fin P.J) (z : Point d)
    (hdouble : P.tau j.succ = 2 * P.tau j.castSucc) :
    ‖highBand P j z‖ ≤ 3 * P.tau j.castSucc := by
  have h := highBand_norm_le P j z
  rw [hdouble] at h
  linarith

theorem paperTau_succ (σ ε : ℝ) (j : ℕ) :
    paperTau σ ε (j + 1) = 2 * paperTau σ ε j := by
  unfold paperTau
  rw [pow_succ]
  ring

/-- Every adjacent pair in the actual finite schedule has ratio two. -/
theorem paperSchedule_tau_double
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    (j : Fin (paperJ p σ ε Ctail)) :
    (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI hε hch hCb hCI).tau j.succ =
      2 * (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI hε hch hCb hCI).tau
        j.castSucc := by
  change paperTau σ ε (j.val + 1) = 2 * paperTau σ ε j.val
  exact paperTau_succ σ ε j.val

end

end HeavyTailedNoise.UpperK1
