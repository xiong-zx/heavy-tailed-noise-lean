import HeavyTailedNoise.Analysis.CarmonChain
import HeavyTailedNoise.Lower.Gated.SupportResidualGate

/-!
The exact unscaled hard objective before its final parameter rescaling.
Quantitative regularity, gap, stationarity, and locality remain separate proofs.
-/

namespace HeavyTailedNoise

noncomputable section

/-- The manuscript's soft-projection radius `R=2500√T`. -/
def hardRadius (T : ℕ) : ℝ := 2500 * Real.sqrt T

/-- Radial soft projection `ρ_R(x)=x/√(1+‖x‖²/R²)`. -/
def softProjection {d : ℕ} (R : ℝ) (x : Point d) : Point d :=
  (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹ • x

theorem contDiff_softProjection_two {d : ℕ} {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ 2 (softProjection (d := d) R) := by
  have hn : ContDiff ℝ 2 (fun x : Point d => ‖x‖ ^ 2) :=
    (contDiff_id.norm_sq ℝ)
  have hb : ContDiff ℝ 2 (fun x : Point d => 1 + ‖x‖ ^ 2 / R ^ 2) :=
    contDiff_const.add (hn.div_const (R ^ 2))
  have hp (x : Point d) : 0 < 1 + ‖x‖ ^ 2 / R ^ 2 := by positivity
  have hs : ContDiff ℝ 2 (fun x : Point d => Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2)) :=
    hb.sqrt (fun x => (hp x).ne')
  have hi : ContDiff ℝ 2
      (fun x : Point d => (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹) :=
    hs.inv (fun x => (Real.sqrt_pos.mpr (hp x)).ne')
  exact hi.smul contDiff_id

/-- Exact `H_U(x)=f_T(Uᵀρ_R(x))+Q_U(ρ_R(x))+(η/2)‖x‖²`, with `η=1/5`. -/
def hardPotential {d T : ℕ} (U : Fin T → Point d) (x : Point d) : ℝ :=
  let y := softProjection (hardRadius T) x
  carmonChain (frameCoordinates U y) + gatedCorrection U y +
    (1 / 10 : ℝ) * ‖x‖ ^ 2

theorem contDiff_hardPotential_two {d T : ℕ} (hT : 0 < T)
    (U : Fin T → Point d) : ContDiff ℝ 2 (hardPotential U) := by
  have hR : 0 < hardRadius T := by
    unfold hardRadius
    have ht : (0 : ℝ) < T := by exact_mod_cast hT
    positivity
  have hy : ContDiff ℝ 2 (softProjection (d := d) (hardRadius T)) :=
    contDiff_softProjection_two hR
  have hz : ContDiff ℝ 2
      (fun x : Point d => frameCoordinates U (softProjection (hardRadius T) x)) :=
    (contDiff_frameCoordinates_two U).comp hy
  have hf : ContDiff ℝ 2
      (fun x : Point d => carmonChain
        (frameCoordinates U (softProjection (hardRadius T) x))) :=
    (contDiff_carmonChain_two T).comp hz
  have hq : ContDiff ℝ 2
      (fun x : Point d => gatedCorrection U (softProjection (hardRadius T) x)) :=
    (contDiff_gatedCorrection_two U).comp hy
  have hr : ContDiff ℝ 2 (fun x : Point d => (1 / 10 : ℝ) * ‖x‖ ^ 2) :=
    contDiff_const.mul (contDiff_id.norm_sq ℝ)
  change ContDiff ℝ 2 (fun x : Point d =>
    carmonChain (frameCoordinates U (softProjection (hardRadius T) x)) +
      gatedCorrection U (softProjection (hardRadius T) x) +
        (1 / 10 : ℝ) * ‖x‖ ^ 2)
  exact (hf.add hq).add hr

end

end HeavyTailedNoise
