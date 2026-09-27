import HeavyTailedNoise.Model.Basic

/-!
The quantifier step from one fixed distribution of instances to a deterministic
bad instance for each randomized full-history algorithm. This does not assume
that the algorithm respects the hidden coordinate order.
-/

open MeasureTheory

noncomputable section

namespace HeavyTailedNoise

/-- A strict lower bound on the average risk under a fixed probability law
forces at least one orientation to have strictly larger risk. The risk may be
infinite. -/
theorem bad_orientation_of_average
    {d N : ℕ} {Seed Frame Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Frame] [MeasurableSpace Private]
    {p q Δ σ Lbar ε : ℝ}
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (instanceAt : Frame → Admissible d Seed p q Δ σ Lbar)
    (A : RandomAlgorithm d N Private)
    (haverage : ENNReal.ofReal ε < ∫⁻ U, risk (instanceAt U) A ∂μ) :
    ∃ U : Frame, ENNReal.ofReal ε < risk (instanceAt U) A := by
  by_contra hnone
  have hpoint : ∀ U : Frame, risk (instanceAt U) A ≤ ENNReal.ofReal ε := by
    intro U
    exact le_of_not_gt (fun h => hnone ⟨U, h⟩)
  have hbound : (∫⁻ U, risk (instanceAt U) A ∂μ) ≤ ENNReal.ofReal ε := by
    calc
      (∫⁻ U, risk (instanceAt U) A ∂μ) ≤ ∫⁻ _ : Frame, ENNReal.ofReal ε ∂μ :=
        lintegral_mono hpoint
      _ = ENNReal.ofReal ε := by simp
  exact not_lt_of_ge hbound haverage

/-- The same `μ` precedes the universal quantifier over algorithms. -/
theorem fixed_average_refutes_uniform_guarantee
    {d N : ℕ} {Seed Frame Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Frame] [MeasurableSpace Private]
    {p q Δ σ Lbar ε : ℝ}
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (instanceAt : Frame → Admissible d Seed p q Δ σ Lbar)
    (haverage : ∀ A : RandomAlgorithm d N Private,
      ENNReal.ofReal ε < ∫⁻ U, risk (instanceAt U) A ∂μ) :
    ¬ ∃ A : RandomAlgorithm d N Private,
      ∀ U : Frame, risk (instanceAt U) A ≤ ENNReal.ofReal ε := by
  rintro ⟨A, hbound⟩
  obtain ⟨U, hbad⟩ := bad_orientation_of_average μ instanceAt A (haverage A)
  exact not_lt_of_ge (hbound U) hbad

universe u v

/-- The manuscript's dimension-uniform guarantee at a fixed padded response
budget. The algorithm and even its private randomness space may depend on the
dimension, whereas the guarantee ranges over every admissible oracle and
every seed space in that dimension. -/
def HasDimensionUniformGuarantee (N : ℕ) (p q Δ σ Lbar ε : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d →
    ∃ (Private : Type u) (privateSpace : MeasurableSpace Private)
      (A : @RandomAlgorithm d N Private privateSpace),
      ∀ (Seed : Type v) (seedSpace : MeasurableSpace Seed)
        (I : @Admissible d Seed seedSpace p q Δ σ Lbar),
        @risk d N Seed seedSpace Private privateSpace p q Δ σ Lbar I A ≤
          ENNReal.ofReal ε

/-- A single hard dimension and a single fixed instance distribution refute
the all-dimension minimax guarantee. The Haar law and hard dimension enter
before the quantifier over arbitrary randomized algorithms. -/
theorem fixed_average_refutes_dimension_uniform_guarantee
    {d N : ℕ} {Seed : Type v} {Frame : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Frame]
    {p q Δ σ Lbar ε : ℝ}
    (hd : 0 < d) (μ : Measure Frame) [IsProbabilityMeasure μ]
    (instanceAt : Frame → Admissible d Seed p q Δ σ Lbar)
    (haverage : ∀ (Private : Type u) (privateSpace : MeasurableSpace Private)
      (A : @RandomAlgorithm d N Private privateSpace),
      ENNReal.ofReal ε <
        ∫⁻ U, @risk d N Seed ‹MeasurableSpace Seed› Private privateSpace
          p q Δ σ Lbar (instanceAt U) A ∂μ) :
    ¬ HasDimensionUniformGuarantee.{u, v} N p q Δ σ Lbar ε := by
  intro hguarantee
  rcases hguarantee d hd with ⟨Private, privateSpace, A, hA⟩
  letI : MeasurableSpace Private := privateSpace
  obtain ⟨U, hbad⟩ :=
    bad_orientation_of_average μ instanceAt A (haverage Private privateSpace A)
  exact not_lt_of_ge (hA Seed ‹MeasurableSpace Seed› (instanceAt U)) hbad

end HeavyTailedNoise
