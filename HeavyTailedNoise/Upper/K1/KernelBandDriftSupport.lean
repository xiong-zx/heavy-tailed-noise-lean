import HeavyTailedNoise.Upper.K1.KernelBandLipschitz

/-!
Exact zero support of the literal high band under the manuscript's dyadic
thresholds. The eventual q-WAS drift estimate uses this to sum only scales
active for at least one of two same-seed residuals.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem paperSchedule_highBand_zero_of_norm_le
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} (j : Fin (paperJ p σ ε Ctail)) (z : Point d)
    (hz : ‖z‖ ≤ paperTau σ ε j.val) :
    highBand (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI) j z = 0 := by
  let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  have hdouble := paperSchedule_tau_double p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI j
  have hmono : P.tau j.castSucc ≤ P.tau j.succ := by
    rw [hdouble]
    have hτ := P.tau_pos j.castSucc
    linarith
  have hz' : ‖z‖ ≤ P.tau j.castSucc := by
    simpa only [P, paperSchedule, Fin.val_castSucc] using hz
  exact highBand_zero_of_norm_le P j z hmono hz'

/-- If both same-seed residuals lie below a band's lower threshold, their
increment vanishes exactly. -/
theorem paperSchedule_highBand_sub_zero_of_max_norm_le
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} (j : Fin (paperJ p σ ε Ctail)) (u v : Point d)
    (hmax : max ‖u‖ ‖v‖ ≤ paperTau σ ε j.val) :
    highBand (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI) j u -
      highBand (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
        hε hch hCb hCI) j v = 0 := by
  have hu : ‖u‖ ≤ paperTau σ ε j.val :=
    (le_max_left _ _).trans hmax
  have hv : ‖v‖ ≤ paperTau σ ε j.val :=
    (le_max_right _ _).trans hmax
  rw [paperSchedule_highBand_zero_of_norm_le
    p q Δ σ Lbar ε Ctail ch κ Cb CI hε hch hCb hCI j u hu,
    paperSchedule_highBand_zero_of_norm_le
      p q Δ σ Lbar ε Ctail ch κ Cb CI hε hch hCb hCI j v hv]
  simp

end

end HeavyTailedNoise.UpperK1
