import HeavyTailedNoise.Upper.Foundations.CoarseTrackerProbability

/-!
The pre-batch conditional drift bridge. Its scalar integral lemma applies on
arbitrary probability spaces. The first-coordinate event is transported from
one oracle seed to a whole fresh batch before the adaptive tracker is inserted.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

/-- A good-event decrement of `3a/8`, a universal increment cap `9a/8`,
and bad-event probability at most `1/6` give mean decrement `a/8`. -/
theorem integral_increment_le_of_bad_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : Set Ω) (hB : MeasurableSet B)
    (χ : Ω → ℝ) (hχ : Integrable χ μ) (a : ℝ) (ha : 0 ≤ a)
    (hgood : ∀ ω ∉ B, χ ω ≤ -(3 / 8 : ℝ) * a)
    (hglobal : ∀ ω, χ ω ≤ (9 / 8 : ℝ) * a)
    (hbad : μ B ≤ (1 / 6 : ENNReal)) :
    (∫ ω, χ ω ∂μ) ≤ -(1 / 8 : ℝ) * a := by
  have hbadreal : μ.real B ≤ (1 / 6 : ℝ) := by
    have h := (ENNReal.toReal_le_toReal (measure_ne_top μ B) (by finiteness)).mpr hbad
    norm_num [ENNReal.toReal_div] at h
    exact h
  have hbadInt :
      (∫ ω in B, χ ω ∂μ) ≤ μ.real B * ((9 / 8 : ℝ) * a) := by
    calc
      _ ≤ ∫ _ω in B, (9 / 8 : ℝ) * a ∂μ :=
        setIntegral_mono_on hχ.integrableOn integrableOn_const hB
          (fun ω _ => hglobal ω)
      _ = _ := by rw [setIntegral_const]; simp [smul_eq_mul]
  have hgoodInt :
      (∫ ω in Bᶜ, χ ω ∂μ) ≤ μ.real Bᶜ * (-(3 / 8 : ℝ) * a) := by
    calc
      _ ≤ ∫ _ω in Bᶜ, -(3 / 8 : ℝ) * a ∂μ :=
        setIntegral_mono_on hχ.integrableOn integrableOn_const hB.compl
          (fun ω hω => hgood ω (by simpa using hω))
      _ = _ := by rw [setIntegral_const]; simp [smul_eq_mul]
  have hproduct : a * μ.real B ≤ a / 6 := by
    calc
      _ ≤ a * (1 / 6 : ℝ) := mul_le_mul_of_nonneg_left hbadreal ha
      _ = a / 6 := by ring
  calc
    (∫ ω, χ ω ∂μ) = (∫ ω in B, χ ω ∂μ) +
        (∫ ω in Bᶜ, χ ω ∂μ) := (integral_add_compl hB hχ).symm
    _ ≤ μ.real B * ((9 / 8 : ℝ) * a) +
        μ.real Bᶜ * (-(3 / 8 : ℝ) * a) := add_le_add hbadInt hgoodInt
    _ = μ.real B * ((9 / 8 : ℝ) * a) +
        (1 - μ.real B) * (-(3 / 8 : ℝ) * a) := by
          rw [probReal_compl_eq_one_sub hB]
    _ ≤ -(1 / 8 : ℝ) * a := by nlinarith [hproduct]

variable {q : ℝ} (P : Schedule q)

/-- The first coordinate of the entire fresh runtime batch has the same bad
event probability as one new oracle seed. No part of the current batch enters
the choice of the pre-batch query point. -/
theorem Admissible.firstBatch_badEvent_measure_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar τ : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (hτ : 0 < τ) (hscale : 12 * σ ≤ τ) (x : Point d) :
    (freshSeedLaw I.oracle P.n)
      {seeds | τ / 2 < ‖I.oracle.response x (seeds ⟨0, P.n_pos⟩) -
        I.objective.grad x‖} ≤ (1 / 6 : ENNReal) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  let bad : Set Seed :=
    {ξ | τ / 2 < ‖I.oracle.response x ξ - I.objective.grad x‖}
  have hresponse : Measurable (I.oracle.response x) :=
    I.oracle.measurable_response.comp (measurable_const.prodMk measurable_id)
  have hbadMeas : MeasurableSet bad := by
    dsimp [bad]
    exact measurableSet_lt measurable_const (hresponse.sub measurable_const).norm
  have hpreserve := measurePreserving_eval
    (fun _ : Fin P.n => I.oracle.law) ⟨0, P.n_pos⟩
  have heq : (freshSeedLaw I.oracle P.n)
      {seeds | τ / 2 < ‖I.oracle.response x (seeds ⟨0, P.n_pos⟩) -
        I.objective.grad x‖} = I.oracle.law bad := by
    change (Measure.pi (fun _ : Fin P.n => I.oracle.law))
      ((Function.eval ⟨0, P.n_pos⟩) ⁻¹' bad) = I.oracle.law bad
    exact hpreserve.measure_preimage hbadMeas.nullMeasurableSet
  rw [heq]
  exact Admissible.firstResponse_badEvent_measure_le I hτ hscale x

end

end HeavyTailedNoise.UpperK1
