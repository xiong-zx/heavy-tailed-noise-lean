import HeavyTailedNoise.Analysis.CarmonCoordinates
import HeavyTailedNoise.Analysis.CarmonPhi
import HeavyTailedNoise.Analysis.CarmonScalar

/-!
The exact finite Carmon scalar chain used by the gated Haar construction.
Indices are zero-based; `chainPredecessor z k` supplies coordinate `k-1` for
positive indices. No scalar chain gap or stationarity estimate is assumed.
-/

namespace HeavyTailedNoise

open scoped BigOperators

noncomputable section

/-- The manuscript's unscaled Carmon chain `f_T`. -/
def carmonChain {T : ℕ} (z : Fin T → ℝ) : ℝ :=
  ∑ k : Fin T,
    if k.val = 0 then -carmonPsi 1 * carmonPhi (z k)
    else
      carmonPsi (-chainPredecessor z k) * carmonPhi (-(z k)) -
        carmonPsi (chainPredecessor z k) * carmonPhi (z k)

theorem contDiff_carmonChain_two (T : ℕ) :
    ContDiff ℝ 2 (carmonChain (T := T)) := by
  unfold carmonChain
  apply ContDiff.sum
  intro k hk
  have hc : ContDiff ℝ 2 (fun z : Fin T → ℝ => z k) := by fun_prop
  by_cases hzero : k.val = 0
  · simp only [hzero, ↓reduceIte]
    exact (contDiff_const.mul (contDiff_carmonPhi_two.comp hc))
  · simp only [hzero, ↓reduceIte]
    have hp := contDiff_chainPredecessor k
    exact ((contDiff_carmonPsi_two.comp hp.neg).mul
      (contDiff_carmonPhi_two.comp hc.neg)).sub
      ((contDiff_carmonPsi_two.comp hp).mul
        (contDiff_carmonPhi_two.comp hc))

end

end HeavyTailedNoise
