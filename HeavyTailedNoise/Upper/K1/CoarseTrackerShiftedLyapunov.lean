import HeavyTailedNoise.Upper.K1.CoarseTrackerExponential

/-!
A shifted exponential Lyapunov argument for a heavy-tailed initial tracker.
The shift by `b+C` is essential: on the small-error branch its next value is
at most one, independently of the initial error.  Thus the exponential tail
starts *after* the overshoot scale and does not incur `exp (lam*(b+C))`.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory ProbabilityTheory

noncomputable section

def shiftedTrackerWeight {Ω : Type*} (ρ : ℕ → Ω → ℝ)
    (b C lam : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Real.exp (lam * (ρ t ω - ρ 0 ω - (b + C)))

/-- Bounded one-step tracker changes make the shifted exponential weight
integrable at every fixed horizon, even when `ρ₀` itself has no exponential
moment. -/
theorem shiftedTrackerWeight_integrable_of_bounded_increments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ρ : ℕ → Ω → ℝ)
    (b C lam : ℝ) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (t : ℕ)
    (hρmeas : ∀ s ≤ t, Measurable (ρ s))
    (hstep : ∀ s < t, ∀ ω, |ρ (s + 1) ω - ρ s ω| ≤ C) :
    Integrable (shiftedTrackerWeight ρ b C lam t) μ := by
  have htel (s : ℕ) (hs : s ≤ t) (ω : Ω) :
      |ρ s ω - ρ 0 ω| ≤ (s : ℝ) * C := by
    induction s with
    | zero => simp
    | succ s ih =>
        have hslt : s < t := by omega
        have hsum : ρ (s + 1) ω - ρ 0 ω =
            (ρ (s + 1) ω - ρ s ω) + (ρ s ω - ρ 0 ω) := by ring
        rw [hsum]
        have htri := abs_add_le (ρ (s + 1) ω - ρ s ω)
          (ρ s ω - ρ 0 ω)
        have hinc := hstep s hslt ω
        have hprev := ih (Nat.le_of_lt hslt)
        push_cast
        linarith
  have hm : Measurable (shiftedTrackerWeight ρ b C lam t) := by
    exact Real.measurable_exp.comp
      (measurable_const.mul
        (((hρmeas t (le_refl t)).sub
          (hρmeas 0 (Nat.zero_le t))).sub measurable_const))
  have hbound (ω : Ω) :
      ‖shiftedTrackerWeight ρ b C lam t ω‖ ≤
        Real.exp (lam * ((t : ℝ) * C - (b + C))) := by
    have hdiff : ρ t ω - ρ 0 ω ≤ (t : ℝ) * C :=
      (le_abs_self _).trans (htel t (le_refl t) ω)
    change |Real.exp (lam * (ρ t ω - ρ 0 ω - (b + C)))| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hdiff _) hlam)
  exact Integrable.of_bound hm.aestronglyMeasurable
    (Real.exp (lam * ((t : ℝ) * C - (b + C))))
    (Filter.Eventually.of_forall hbound)

/-- The only probabilistic input is the true pre-step weighted contraction
on the event that the tracker error is large.  It can be discharged by the
actual-history product law and `tracker_stoppedWeight_exponential_le`. -/
theorem shiftedTrackerWeight_integral_uniform
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ρ : ℕ → Ω → ℝ)
    (b C lam r K : ℝ) (N : ℕ)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hr : 0 ≤ r)
    (hKbase : 1 ≤ K) (hKstep : r * K + 1 ≤ K)
    (hρ0 : ∀ ω, 0 ≤ ρ 0 ω)
    (hρmeas : ∀ t ≤ N, Measurable (ρ t))
    (hstep : ∀ t < N, ∀ ω, ρ (t + 1) ω ≤ ρ t ω + C)
    (hInt : ∀ t ≤ N,
      Integrable (shiftedTrackerWeight ρ b C lam t) μ)
    (hcontract : ∀ t < N,
      (∫ ω in {ω | b ≤ ρ t ω},
        shiftedTrackerWeight ρ b C lam (t + 1) ω ∂μ) ≤
      r * ∫ ω in {ω | b ≤ ρ t ω},
        shiftedTrackerWeight ρ b C lam t ω ∂μ) :
    ∀ t ≤ N,
      (∫ ω, shiftedTrackerWeight ρ b C lam t ω ∂μ) ≤ K := by
  intro t ht
  induction t with
  | zero =>
      have hnonpos : lam * (-(b + C)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
      calc
        (∫ ω, shiftedTrackerWeight ρ b C lam 0 ω ∂μ) =
            Real.exp (lam * (-(b + C))) := by
              simp [shiftedTrackerWeight]
        _ ≤ 1 := by
              rw [← Real.exp_zero]
              exact Real.exp_le_exp.mpr hnonpos
        _ ≤ K := hKbase
  | succ t ih =>
      have htN : t < N := by omega
      have htle : t ≤ N := Nat.le_of_lt htN
      have hmeas : MeasurableSet {ω | b ≤ ρ t ω} :=
        measurableSet_le measurable_const (hρmeas t htle)
      have hsmall (ω : Ω) (hω : ω ∈ {ω | b ≤ ρ t ω}ᶜ) :
          shiftedTrackerWeight ρ b C lam (t + 1) ω ≤ 1 := by
        have hbelow : ρ t ω < b := by
          have hnot : ¬ b ≤ ρ t ω := hω
          exact lt_of_not_ge hnot
        have hdiff : ρ (t + 1) ω - ρ 0 ω - (b + C) ≤ 0 := by
          linarith [hstep t htN ω, hρ0 ω]
        change Real.exp (lam * (ρ (t + 1) ω - ρ 0 ω - (b + C))) ≤ 1
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr
          (mul_nonpos_of_nonneg_of_nonpos hlam hdiff)
      have hsmallInt :
          (∫ ω in {ω | b ≤ ρ t ω}ᶜ,
            shiftedTrackerWeight ρ b C lam (t + 1) ω ∂μ) ≤ 1 := by
        calc
          _ ≤ ∫ _ω in {ω | b ≤ ρ t ω}ᶜ, (1 : ℝ) ∂μ :=
            setIntegral_mono_on (hInt (t + 1) ht).integrableOn
              integrableOn_const hmeas.compl hsmall
          _ = μ.real {ω | b ≤ ρ t ω}ᶜ := by
            rw [setIntegral_const]
            simp [smul_eq_mul]
          _ ≤ 1 := by
            exact (measureReal_mono (Set.subset_univ _)).trans (by simp)
      have hlargeInt :
          (∫ ω in {ω | b ≤ ρ t ω},
            shiftedTrackerWeight ρ b C lam t ω ∂μ) ≤
          ∫ ω, shiftedTrackerWeight ρ b C lam t ω ∂μ := by
        have hnonneg :
            0 ≤ ∫ ω in {ω | b ≤ ρ t ω}ᶜ,
              shiftedTrackerWeight ρ b C lam t ω ∂μ :=
          setIntegral_nonneg hmeas.compl (fun ω _ => Real.exp_nonneg _)
        have hsplit := integral_add_compl hmeas (hInt t htle)
        linarith
      calc
        (∫ ω, shiftedTrackerWeight ρ b C lam (t + 1) ω ∂μ) =
            (∫ ω in {ω | b ≤ ρ t ω},
                shiftedTrackerWeight ρ b C lam (t + 1) ω ∂μ) +
              (∫ ω in {ω | b ≤ ρ t ω}ᶜ,
                shiftedTrackerWeight ρ b C lam (t + 1) ω ∂μ) :=
                  (integral_add_compl hmeas (hInt (t + 1) ht)).symm
        _ ≤ r * (∫ ω in {ω | b ≤ ρ t ω},
              shiftedTrackerWeight ρ b C lam t ω ∂μ) + 1 :=
                add_le_add (hcontract t htN) hsmallInt
        _ ≤ r * (∫ ω, shiftedTrackerWeight ρ b C lam t ω ∂μ) + 1 :=
                add_le_add (mul_le_mul_of_nonneg_left hlargeInt hr) le_rfl
        _ ≤ r * K + 1 :=
                add_le_add (mul_le_mul_of_nonneg_left (ih htle) hr) le_rfl
        _ ≤ K := hKstep

/-- Uniform exponential upper tail above `ρ₀ + b + C`.  The prefactor `K`
does not contain an exponential in the physical noise ratio. -/
theorem shiftedTrackerWeight_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ρ : ℕ → Ω → ℝ)
    (b C lam K x : ℝ) (t : ℕ) (hlam : 0 ≤ lam)
    (hInt : Integrable (shiftedTrackerWeight ρ b C lam t) μ)
    (hbound : (∫ ω, shiftedTrackerWeight ρ b C lam t ω ∂μ) ≤ K) :
    μ.real {ω | x ≤ ρ t ω - ρ 0 ω - (b + C)} ≤
      Real.exp (-lam * x) * K := by
  have hchernoff := measure_ge_le_exp_mul_mgf
    (X := fun ω => ρ t ω - ρ 0 ω - (b + C))
    (μ := μ) x hlam hInt
  calc
    μ.real {ω | x ≤ ρ t ω - ρ 0 ω - (b + C)} ≤
        Real.exp (-lam * x) *
          mgf (fun ω => ρ t ω - ρ 0 ω - (b + C)) μ lam := hchernoff
    _ ≤ Real.exp (-lam * x) * K :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)

end

end HeavyTailedNoise.UpperK1
