import HeavyTailedNoise.Upper.K1.KernelShellSupport

/-!
Conservative same-seed shell increment geometry for the frozen algorithm.
Each high band is the difference of two radial projections. A factor two is
enough for the later weighted-drift estimate and keeps the proof independent
of an unformalized sharper shell projection fact.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

/-- One high-band transform is two-Lipschitz in the original residual.
The oracle is not changed and no independent band noise is introduced. -/
theorem highBand_norm_sub_le_two {q : ℝ} (P : Schedule q)
    {d : ℕ} (j : Fin P.J) (u v : Point d) :
    ‖highBand P j u - highBand P j v‖ ≤ 2 * ‖u - v‖ := by
  let hi := P.tau j.succ
  let lo := P.tau j.castSucc
  have hhi := upperClip_norm_sub_le (P.tau_pos j.succ) u v
  have hlo := upperClip_norm_sub_le (P.tau_pos j.castSucc) u v
  have hrew : highBand P j u - highBand P j v =
      (upperClip hi u - upperClip hi v) -
        (upperClip lo u - upperClip lo v) := by
    dsimp [highBand, upperShell, hi, lo]
    abel
  rw [hrew]
  calc
    ‖(upperClip hi u - upperClip hi v) -
        (upperClip lo u - upperClip lo v)‖ ≤
      ‖upperClip hi u - upperClip hi v‖ +
        ‖upperClip lo u - upperClip lo v‖ := norm_sub_le _ _
    _ ≤ 2 * ‖u - v‖ := by
      dsimp [hi, lo]
      linarith

end

end HeavyTailedNoise.UpperK1
