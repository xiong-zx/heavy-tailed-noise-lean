import HeavyTailedNoise.Lower.Gated.JointPrefixGradientMeas
import HeavyTailedNoise.Lower.Gated.ScaledObjectiveStationarity

/-!
Joint frame-query measurability of the *full* hard and scaled gradients. The
terminal prefix identity avoids a second expensive joint-Hessian proof.
-/

namespace HeavyTailedNoise

noncomputable section

theorem measurable_joint_hardGradient {d T : ℕ} (hT : 0 < T) :
    Measurable (fun z : (Fin T → Point d) × Point d =>
      gradient (hardPotential z.1) z.2) := by
  let j : Fin T := ⟨T - 1, by omega⟩
  have hj : j.val + 1 = T := by dsimp [j]; omega
  have hpre := measurable_joint_prefixGradient (d := d) hT j
  have heq (U : Fin T → Point d) :
      prefixHardPotential U j = hardPotential U :=
    prefixHardPotential_eq_full_at_last U j hj
  simpa only [heq] using hpre

theorem measurable_joint_scaledHardGradient
    {d T : ℕ} (hT : 0 < T) {L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) :
    Measurable (fun z : (Fin T → Point d) × Point d =>
      gradient (scaledHardPotential L ε z.1) z.2) := by
  let lam : ℝ := hardScaleLambda L ε
  have hquery : Measurable
      (fun z : (Fin T → Point d) × Point d => lam⁻¹ • z.2) := by fun_prop
  have hpair : Measurable
      (fun z : (Fin T → Point d) × Point d =>
        (z.1, lam⁻¹ • z.2)) := measurable_fst.prodMk hquery
  have hH : Measurable
      (fun z : (Fin T → Point d) × Point d =>
        gradient (hardPotential z.1) (lam⁻¹ • z.2)) :=
    (measurable_joint_hardGradient hT).comp hpair
  have hsmul : Measurable
      (fun z : (Fin T → Point d) × Point d =>
        (80 * ε) • gradient (hardPotential z.1) (lam⁻¹ • z.2)) :=
    (measurable_const : Measurable
      (fun _ : (Fin T → Point d) × Point d => (80 * ε : ℝ))).smul hH
  have heq :
      (fun z : (Fin T → Point d) × Point d =>
        gradient (scaledHardPotential L ε z.1) z.2) =
      (fun z => (80 * ε) • gradient (hardPotential z.1) (lam⁻¹ • z.2)) := by
    funext z
    simpa [lam] using gradient_scaledHardPotential_eq hT z.1 hL hε z.2
  rw [heq]
  exact hsmul

end

end HeavyTailedNoise
