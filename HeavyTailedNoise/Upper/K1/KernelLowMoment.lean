import HeavyTailedNoise.Upper.K1.KernelLowBand
import HeavyTailedNoise.Upper.Foundations.ClipMoment

/-!
The lag-zero low core requires only the residual `p` moment.  The factor-two
clipping interpolation has a conservative constant and is valid at `p = 2`
and for a zero residual.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

/-- Deterministic low-core square bound with no absolute second-moment
assumption on the un-clipped residual. -/
theorem lowBand_sq_le_residual_p
    {q : ℝ} (P : Schedule q) {d : ℕ} {p : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (z : Point d) :
    ‖lowBand P z‖ ^ 2 ≤
      (2 * P.tau ⟨0, Nat.zero_lt_succ P.J⟩) ^ (2 - p) * ‖z‖ ^ p := by
  have h := upperClip_difference_sq_le_rpow
    (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩) ⟨hp, hp2⟩
    z (0 : Point d)
  simpa [lowBand] using h

end

end HeavyTailedNoise.UpperK1
