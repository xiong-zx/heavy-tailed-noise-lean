import HeavyTailedNoise.Upper.K1.SameSeedMomentLp

/-!
The same-seed source drift uses the conjugate exponents `q` and
`q / (q - 1)`.  The maximum of the two endpoint residual norms has only a
`p` moment; raising it to `paperSexp p q` gives precisely the conjugate
moment needed for Hölder.  These are fixed-seed-space facts, with no
independence between the two endpoints or among dyadic bands.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

private theorem paperSexp_conjugate (q : ℝ) (hq : 1 < q) :
    (q / (q - 1)).HolderConjugate q := by
  simpa only [Real.conjExponent] using
    (Real.HolderConjugate.conjExponent hq).symm

private theorem paperSexp_mul_conjugate (p q : ℝ) (hq : 1 < q) :
    paperSexp p q * (q / (q - 1)) = p := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq.ne'
  dsimp [paperSexp]
  field_simp [hq0, hq1] <;> ring

private theorem max_norm_memLp
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) (X Y : α → E) (hXm : Measurable X) (hYm : Measurable Y)
    {t : ENNReal} (hX : MemLp X t μ) (hY : MemLp Y t μ) :
    MemLp (fun a => max ‖X a‖ ‖Y a‖) t μ := by
  have hsum : MemLp (fun a => ‖X a‖ + ‖Y a‖) t μ := by
    apply (hX.norm.add hY.norm).congr_norm
      ((hXm.norm.add hYm.norm).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun a => by
      simp only [Pi.add_apply]
  have hRm : Measurable (fun a => max ‖X a‖ ‖Y a‖) :=
    hXm.norm.max hYm.norm
  refine hsum.mono' hRm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun a => by
    have hR0 : 0 ≤ max ‖X a‖ ‖Y a‖ :=
      (norm_nonneg (X a)).trans (le_max_left _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hR0]
    exact max_le (by linarith [norm_nonneg (Y a)])
      (by linarith [norm_nonneg (X a)])

private theorem max_norm_rpow_memLp
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) (X Y : α → E) (hXm : Measurable X) (hYm : Measurable Y)
    {p s : ℝ} (hs : 0 < s)
    (hX : MemLp X (ENNReal.ofReal p) μ)
    (hY : MemLp Y (ENNReal.ofReal p) μ) :
    MemLp (fun a => (max ‖X a‖ ‖Y a‖) ^ s)
      (ENNReal.ofReal p / ENNReal.ofReal s) μ := by
  have hR := max_norm_memLp μ X Y hXm hYm hX hY
  have h := hR.norm_rpow_div (ENNReal.ofReal s)
  have hfun :
      (fun a => ‖max ‖X a‖ ‖Y a‖‖ ^ (ENNReal.ofReal s).toReal) =
        (fun a => (max ‖X a‖ ‖Y a‖) ^ s) := by
    funext a
    rw [ENNReal.toReal_ofReal hs.le, Real.norm_eq_abs,
      abs_of_nonneg ((norm_nonneg (X a)).trans (le_max_left _ _))]
  rw [hfun] at h
  exact h

/-- At fixed endpoints, the paper exponent turns the maximum residual's
`p` moment into the precise Hölder-conjugate moment.  Both residuals use the
same auxiliary seed. -/
theorem Admissible.same_seed_max_residual_rpow_memLp
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hq : 1 < q) (x x' w w' : Point d) :
    MemLp (fun ξ =>
      (max ‖I.oracle.response x' ξ - w'‖
        ‖I.oracle.response x ξ - w‖) ^ paperSexp p q)
      (ENNReal.ofReal (q / (q - 1))) I.oracle.law := by
  let s := paperSexp p q
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos (lt_trans zero_lt_one I.p_range.1)
    apply sub_pos.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa using hq)
  have hdiv : p / s = q / (q - 1) := by
    apply (div_eq_iff hs.ne').2
    simpa [mul_comm] using (paperSexp_mul_conjugate p q hq).symm
  have hexp : ENNReal.ofReal p / ENNReal.ofReal s =
      ENNReal.ofReal (q / (q - 1)) := by
    rw [← ENNReal.ofReal_div_of_pos hs, hdiv]
  have hresponse (a : Point d) : Measurable (I.oracle.response a) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hY := Admissible.residual_memLp I x' w'
  have hX := Admissible.residual_memLp I x w
  have h := max_norm_rpow_memLp I.oracle.law
    (fun ξ => I.oracle.response x' ξ - w')
    (fun ξ => I.oracle.response x ξ - w)
    ((hresponse x').sub measurable_const)
    ((hresponse x).sub measurable_const) hs hY hX
  rw [hexp] at h
  simpa only [s] using h

/-- Hölder for the one-seed product appearing after the active-dyadic
pointwise bound.  Its two factors may be arbitrarily correlated. -/
theorem Admissible.same_seed_residual_product_holder
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hq : 1 < q) (x x' w w' : Point d) :
    (∫ ξ : Seed,
      (max ‖I.oracle.response x' ξ - w'‖
          ‖I.oracle.response x ξ - w‖) ^ paperSexp p q *
        ‖(I.oracle.response x' ξ - w') -
          (I.oracle.response x ξ - w)‖ ∂I.oracle.law) ≤
      (∫ ξ : Seed,
        ((max ‖I.oracle.response x' ξ - w'‖
            ‖I.oracle.response x ξ - w‖) ^ paperSexp p q) ^
          (q / (q - 1)) ∂I.oracle.law) ^ (1 / (q / (q - 1))) *
      (∫ ξ : Seed,
        ‖(I.oracle.response x' ξ - w') -
          (I.oracle.response x ξ - w)‖ ^ q ∂I.oracle.law) ^ (1 / q) := by
  exact integral_mul_le_Lp_mul_Lq_of_nonneg
    (paperSexp_conjugate q hq)
    (Filter.Eventually.of_forall fun ξ =>
      Real.rpow_nonneg (le_trans (norm_nonneg _)
        (le_max_left _ _)) _)
    (Filter.Eventually.of_forall fun ξ => norm_nonneg _)
    (Admissible.same_seed_max_residual_rpow_memLp I hq x x' w w')
    (Admissible.same_seed_residual_increment_memLp I x x' w w').norm

end

end HeavyTailedNoise.UpperK1
