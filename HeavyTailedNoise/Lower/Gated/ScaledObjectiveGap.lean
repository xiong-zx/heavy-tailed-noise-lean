import HeavyTailedNoise.Lower.Gated.HardObjectiveGap
import HeavyTailedNoise.Analysis.LowerBoundArithmetic

/-!
The manuscript's exact final rescaling of the gated Haar objective. The
function-value gap is checked separately from the still-open gradient
Lipschitz and stationarity claims.
-/

namespace HeavyTailedNoise

noncomputable section

/-- `2 ℓ₁ ε/(L c_*)` with `ℓ₁=4300` and `c_*=1/40`. -/
def hardScaleLambda (L ε : ℝ) : ℝ := 344000 * ε / L

theorem hardScaleLambda_eq_manuscript (L ε : ℝ) :
    hardScaleLambda L ε = 2 * 4300 * ε / (L * (1 / 40 : ℝ)) := by
  unfold hardScaleLambda
  ring

/-- The exact final population objective before adjoining its Gaussian oracle. -/
def scaledHardPotential {d T : ℕ} (L ε : ℝ) (U : Fin T → Point d)
    (x : Point d) : ℝ :=
  let lam := hardScaleLambda L ε
  (L * lam ^ 2 / 4300) * hardPotential U (lam⁻¹ • x)

theorem scaledHardPotential_zero {d T : ℕ} (L ε : ℝ) (U : Fin T → Point d) :
    scaledHardPotential L ε U 0 =
      (L * (hardScaleLambda L ε) ^ 2 / 4300) * hardPotential U 0 := by
  simp [scaledHardPotential]

private theorem hardPotential_gap_pointwise {d T : ℕ} (U : Fin T → Point d)
    (x : Point d) :
    hardPotential U 0 - hardPotential U x ≤ 12 * T := by
  have hbdd : BddBelow (Set.range (hardPotential U)) := by
    refine ⟨sInf (Set.range (carmonChain (T := T))), ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hardPotential_chainInf_le U y
  have hInf := csInf_le hbdd (Set.mem_range_self x)
  linarith [hardPotential_gap_le_12T U]

theorem scaledHardPotential_gap_le {d T : ℕ} (L ε : ℝ)
    (hL : 0 ≤ L) (U : Fin T → Point d) :
    scaledHardPotential L ε U 0 -
      sInf (Set.range (scaledHardPotential L ε U)) ≤
        (L * (hardScaleLambda L ε) ^ 2 / 4300) * (12 * T) := by
  let c : ℝ := L * (hardScaleLambda L ε) ^ 2 / 4300
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint (x : Point d) :
      scaledHardPotential L ε U 0 - c * (12 * T) ≤
        scaledHardPotential L ε U x := by
    rw [scaledHardPotential_zero]
    change c * hardPotential U 0 - c * (12 * T) ≤
      c * hardPotential U ((hardScaleLambda L ε)⁻¹ • x)
    have hgap := hardPotential_gap_pointwise U
      ((hardScaleLambda L ε)⁻¹ • x)
    have hnonneg : 0 ≤ c *
        (12 * T - (hardPotential U 0 -
          hardPotential U ((hardScaleLambda L ε)⁻¹ • x))) :=
      mul_nonneg hc (sub_nonneg.mpr hgap)
    nlinarith [hnonneg]
  have hne : (Set.range (scaledHardPotential L ε U)).Nonempty :=
    ⟨scaledHardPotential L ε U 0, ⟨0, rfl⟩⟩
  have hinf : scaledHardPotential L ε U 0 - c * (12 * T) ≤
      sInf (Set.range (scaledHardPotential L ε U)) :=
    le_csInf hne (by rintro _ ⟨x, rfl⟩; exact hpoint x)
  dsimp [c] at hinf ⊢
  linarith

/-- Instance-gap legality under the manuscript's exact upper condition on T. -/
theorem scaledHardPotential_gap_le_Delta {d T : ℕ}
    {L ε Δ : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (U : Fin T → Point d)
    (hT : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ) :
    scaledHardPotential L ε U 0 -
      sInf (Set.range (scaledHardPotential L ε U)) ≤ Δ := by
  have hgap := scaledHardPotential_gap_le L ε hL.le U
  have hcost :
      (L * (hardScaleLambda L ε) ^ 2 / 4300) * (12 * T) =
        (330240000 * ε ^ 2 * T) / L := by
    unfold hardScaleLambda
    field_simp [hL.ne']
    ring
  rw [hcost] at hgap
  exact hgap.trans ((div_le_iff₀ hL).2 (by simpa [mul_comm] using hT))

/-- For the actual floor choice of `T`, the final instance satisfies its
function-value gap budget with no arithmetic premise left open. -/
theorem scaledHardPotential_gap_le_Delta_of_manuscript_T
    {d : ℕ} {L ε Δ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 ≤ Δ)
    (U : Fin (⌊L * Δ / (330240000 * ε ^ 2)⌋₊) → Point d) :
    scaledHardPotential L ε U 0 -
      sInf (Set.range (scaledHardPotential L ε U)) ≤ Δ :=
  scaledHardPotential_gap_le_Delta hL hε U
    (gatedChainLength_budget L ε Δ hL hε hΔ)

end

end HeavyTailedNoise
