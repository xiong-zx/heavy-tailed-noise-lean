import HeavyTailedNoise.Upper.K1.SameSeedLpNormBounds

/-!
Fixed-center residual norms follow by Minkowski from the oracle's centered
`p` moment and same-seed response-increment `q` moment.  A deterministic
center shift contributes only its ordinary norm.  The `q` result remains
valid at `q = 1`; it assumes no absolute residual `q` moment.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

private theorem lpNorm_const_probability
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (c : E) :
    lpNorm (fun _ : α => c) (ENNReal.ofReal r) μ = ‖c‖ := by
  have hprob : μ.real Set.univ = 1 := by simp
  rw [lpNorm_const' (ENNReal.ofReal_ne_zero_iff.mpr hr)
    ENNReal.ofReal_ne_top c]
  simp [hprob]

theorem Admissible.residual_lpNorm_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x w : Point d) :
    lpNorm (fun ξ => I.oracle.response x ξ - w)
      (ENNReal.ofReal p) I.oracle.law ≤
      σ + ‖I.objective.grad x - w‖ := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  have hp : 0 < p := lt_trans zero_lt_one I.p_range.1
  have hpENN : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal I.p_range.1.le
  have hcentered := Admissible.centered_response_memLp I x
  have hconst : lpNorm (fun _ : Seed => I.objective.grad x - w)
      (ENNReal.ofReal p) I.oracle.law =
      ‖I.objective.grad x - w‖ :=
    lpNorm_const_probability I.oracle.law hp _
  have hfun : (fun ξ => I.oracle.response x ξ - w) =
      (fun ξ => I.oracle.response x ξ - I.objective.grad x) +
        (fun _ : Seed => I.objective.grad x - w) := by
    funext ξ
    simp only [Pi.add_apply]
    abel
  rw [hfun]
  calc
    lpNorm ((fun ξ => I.oracle.response x ξ - I.objective.grad x) +
        (fun _ : Seed => I.objective.grad x - w))
        (ENNReal.ofReal p) I.oracle.law ≤
      lpNorm (fun ξ => I.oracle.response x ξ - I.objective.grad x)
          (ENNReal.ofReal p) I.oracle.law +
        lpNorm (fun _ : Seed => I.objective.grad x - w)
          (ENNReal.ofReal p) I.oracle.law :=
      lpNorm_add_le hcentered hpENN
    _ ≤ σ + ‖I.objective.grad x - w‖ := by
      rw [hconst]
      exact add_le_add
        (Admissible.centered_response_lpNorm_le I x) le_rfl

theorem Admissible.same_seed_residual_increment_lpNorm_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x x' w w' : Point d) :
    lpNorm (fun ξ => (I.oracle.response x' ξ - w') -
      (I.oracle.response x ξ - w))
      (ENNReal.ofReal q) I.oracle.law ≤
      Lbar * ‖x' - x‖ + ‖w' - w‖ := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one I.q_range
  have hqENN : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal I.q_range
  have hraw := Admissible.same_seed_increment_memLp I x' x
  have hconst : lpNorm (fun _ : Seed => w' - w)
      (ENNReal.ofReal q) I.oracle.law = ‖w' - w‖ :=
    lpNorm_const_probability I.oracle.law hq _
  have hfun : (fun ξ => (I.oracle.response x' ξ - w') -
      (I.oracle.response x ξ - w)) =
      (fun ξ => I.oracle.response x' ξ - I.oracle.response x ξ) -
        (fun _ : Seed => w' - w) := by
    funext ξ
    simp only [Pi.sub_apply]
    abel
  rw [hfun]
  calc
    lpNorm ((fun ξ => I.oracle.response x' ξ - I.oracle.response x ξ) -
        (fun _ : Seed => w' - w)) (ENNReal.ofReal q) I.oracle.law ≤
      lpNorm (fun ξ => I.oracle.response x' ξ - I.oracle.response x ξ)
          (ENNReal.ofReal q) I.oracle.law +
        lpNorm (fun _ : Seed => w' - w)
          (ENNReal.ofReal q) I.oracle.law :=
      lpNorm_sub_le hraw hqENN
    _ ≤ Lbar * ‖x' - x‖ + ‖w' - w‖ := by
      rw [hconst]
      exact add_le_add
        (Admissible.same_seed_increment_lpNorm_le I x' x) le_rfl

end

end HeavyTailedNoise.UpperK1
