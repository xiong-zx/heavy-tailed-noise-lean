import HeavyTailedNoise.Lower.Gated.ScaledObjectiveSmoothness
import HeavyTailedNoise.Probability.GaussianOracle

/-!
The actual rescaled gated Haar objective and additive isotropic Gaussian
oracle satisfy the shared finite-q admissibility contract. All geometric
constants are discharged by the imported checked modules.
-/

namespace HeavyTailedNoise

noncomputable section

def hardScaledObjective
    {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    {L ε Δ : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hbudget : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ) :
    Objective d Δ where
  dimension_pos := hd
  value := scaledHardPotential L ε U
  grad := gradient (scaledHardPotential L ε U)
  hasGradientAt := by
    intro x
    exact ((contDiff_scaledHardPotential_two hT U L ε).differentiable
      (by norm_num) x).hasGradientAt
  continuous_grad :=
    (lipschitzWith_gradient_scaledHardPotential hU hT hL hε).continuous
  gap := by
    intro x
    let lam : ℝ := hardScaleLambda L ε
    let c : ℝ := L * lam ^ 2 / 4300
    let y : Point d := lam⁻¹ • x
    have hlam : 0 < lam := by dsimp [lam, hardScaleLambda]; positivity
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hbdd : BddBelow (Set.range (hardPotential U)) := by
      refine ⟨sInf (Set.range (carmonChain (T := T))), ?_⟩
      rintro _ ⟨z, rfl⟩
      exact hardPotential_chainInf_le U z
    have hInf : sInf (Set.range (hardPotential U)) ≤ hardPotential U y :=
      csInf_le hbdd (Set.mem_range_self y)
    have hH : hardPotential U 0 - hardPotential U y ≤ 12 * T := by
      linarith [hardPotential_gap_le_12T U]
    have hscale :
        scaledHardPotential L ε U 0 - scaledHardPotential L ε U x =
          c * (hardPotential U 0 - hardPotential U y) := by
      simp [scaledHardPotential_zero, scaledHardPotential, c, lam, y]
      ring
    have hcost : c * (12 * T) =
        (330240000 * ε ^ 2 * T) / L := by
      dsimp [c, lam, hardScaleLambda]
      field_simp [hL.ne']
      ring
    calc
      scaledHardPotential L ε U 0 - scaledHardPotential L ε U x =
          c * (hardPotential U 0 - hardPotential U y) := hscale
      _ ≤ c * (12 * T) := mul_le_mul_of_nonneg_left hH hc
      _ = (330240000 * ε ^ 2 * T) / L := hcost
      _ ≤ Δ := (div_le_iff₀ hL).2 (by simpa [mul_comm] using hbudget)

/-- For every finite q≥1 and 1<p≤2, the exact final additive Gaussian
instance is legal under the manuscript's parameter budget. -/
def hardGaussianAdmissible
    {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    {p q L ε Δ σ : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (hbudget : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ) :
    Admissible d (Point d) p q Δ σ L :=
  gaussianAdmissible
    (hardScaledObjective hd hT U hU hL hε hbudget)
    hp hq hΔ hσ hL
    (by intro x y; exact norm_gradient_scaledHardPotential_sub_le_L hU hT hL hε x y)

/-- With the manuscript's actual floor choice of chain length, the gap
budget is automatic rather than a further instance hypothesis. -/
def hardGaussianAdmissibleForChosenT
    {d : ℕ} (hd : 0 < d)
    {p q L ε Δ σ : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (hT : 0 < ⌊L * Δ / (330240000 * ε ^ 2)⌋₊)
    (U : Fin (⌊L * Δ / (330240000 * ε ^ 2)⌋₊) → Point d)
    (hU : Orthonormal ℝ U) :
    Admissible d (Point d) p q Δ σ L :=
  hardGaussianAdmissible hd hT U hU hp hq hL hε hΔ hσ
    (gatedChainLength_budget L ε Δ hL hε hΔ.le)

end

end HeavyTailedNoise
