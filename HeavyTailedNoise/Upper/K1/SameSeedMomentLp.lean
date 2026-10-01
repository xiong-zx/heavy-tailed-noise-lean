import HeavyTailedNoise.Upper.K1.KernelSourceMeanDriftIntegrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
Convert the oracle's existing finite centered `p` and same-seed increment
`q` moments to `MemLp`. A residual at a fixed center inherits only a `p`
moment; its difference at two centers inherits a `q` moment solely from
q-WAS for the response increment and the deterministic center displacement.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

private theorem memLp_of_lintegral_norm_rpow_le
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) (f : α → E) (hf : Measurable f)
    {r C : ℝ} (hr : 0 < r)
    (hm : (∫⁻ a, ENNReal.ofReal (‖f a‖ ^ r) ∂μ) ≤
      ENNReal.ofReal C) :
    MemLp f (ENNReal.ofReal r) μ := by
  have hmeas : Measurable (fun a => ‖f a‖ ^ r) :=
    (Real.continuous_rpow_const hr.le).measurable.comp hf.norm
  have hnonneg : 0 ≤ᵐ[μ] (fun a => ‖f a‖ ^ r) :=
    Filter.Eventually.of_forall (fun a => Real.rpow_nonneg (norm_nonneg _) _)
  have hfinite : (∫⁻ a, ENNReal.ofReal (‖f a‖ ^ r) ∂μ) ≠
      (⊤ : ENNReal) :=
    ne_of_lt (lt_of_le_of_lt hm (by simp))
  have hint : Integrable (fun a => ‖f a‖ ^ r) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hmeas.aestronglyMeasurable hnonneg).mp hfinite
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable
    (p := ENNReal.ofReal r)
    (ENNReal.ofReal_ne_zero_iff.mpr hr)
    ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hr.le] using hint

theorem Admissible.centered_response_memLp
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x : Point d) :
    MemLp (fun ξ => I.oracle.response x ξ - I.objective.grad x)
      (ENNReal.ofReal p) I.oracle.law := by
  have hresponse : Measurable (I.oracle.response x) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  exact memLp_of_lintegral_norm_rpow_le I.oracle.law
    (fun ξ => I.oracle.response x ξ - I.objective.grad x)
    (hresponse.sub measurable_const)
    (lt_trans zero_lt_one I.p_range.1)
    (I.centered_moment x)

theorem Admissible.same_seed_increment_memLp
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x y : Point d) :
    MemLp (fun ξ => I.oracle.response x ξ - I.oracle.response y ξ)
      (ENNReal.ofReal q) I.oracle.law := by
  have hx : Measurable (I.oracle.response x) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hy : Measurable (I.oracle.response y) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  exact memLp_of_lintegral_norm_rpow_le I.oracle.law
    (fun ξ => I.oracle.response x ξ - I.oracle.response y ξ)
    (hx.sub hy) (lt_of_lt_of_le zero_lt_one I.q_range)
    (I.same_seed_increment x y)

theorem Admissible.residual_memLp
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x w : Point d) :
    MemLp (fun ξ => I.oracle.response x ξ - w)
      (ENNReal.ofReal p) I.oracle.law := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  have hcentered := Admissible.centered_response_memLp I x
  have hconst : MemLp (fun _ : Seed => I.objective.grad x - w)
      (ENNReal.ofReal p) I.oracle.law := memLp_const _
  have hfun : (fun ξ => I.oracle.response x ξ - w) =
      (fun ξ => I.oracle.response x ξ - I.objective.grad x) +
        (fun _ : Seed => I.objective.grad x - w) := by
    funext ξ
    simp only [Pi.add_apply]
    abel
  rw [hfun]
  exact hcentered.add hconst

theorem Admissible.same_seed_residual_increment_memLp
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (x x' w w' : Point d) :
    MemLp (fun ξ => (I.oracle.response x' ξ - w') -
      (I.oracle.response x ξ - w))
      (ENNReal.ofReal q) I.oracle.law := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  have hraw := Admissible.same_seed_increment_memLp I x' x
  have hconst : MemLp (fun _ : Seed => w' - w)
      (ENNReal.ofReal q) I.oracle.law := memLp_const _
  have hfun : (fun ξ => (I.oracle.response x' ξ - w') -
      (I.oracle.response x ξ - w)) =
      (fun ξ => I.oracle.response x' ξ - I.oracle.response x ξ) -
        (fun _ : Seed => w' - w) := by
    funext ξ
    simp only [Pi.sub_apply]
    abel
  rw [hfun]
  exact hraw.sub hconst

end

end HeavyTailedNoise.UpperK1
