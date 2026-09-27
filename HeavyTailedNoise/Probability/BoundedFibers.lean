import HeavyTailedNoise.Model.Basic

namespace HeavyTailedNoise
open MeasureTheory ProbabilityTheory
noncomputable section

theorem measure_eq_sum_restrict_bounded_nat_fibers
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (τ : Ω → ℕ)
    (hτ : Measurable τ) (hbound : ∀ ω, τ ω < N + 2) :
    μ = Measure.sum (fun t : Fin (N + 2) =>
      μ.restrict {ω | τ ω = t.val}) := by
  let s : Fin (N + 2) → Set Ω := fun t => {ω | τ ω = t.val}
  have hd : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    have hiv : i.val = j.val := by
      dsimp [s] at hi hj
      omega
    exact hij (Fin.ext hiv)
  have hm (t : Fin (N + 2)) : MeasurableSet (s t) :=
    measurableSet_eq_fun hτ measurable_const
  have hcover : (⋃ t, s t) = Set.univ := by
    ext ω
    constructor
    · intro _
      trivial
    · intro _
      exact Set.mem_iUnion.mpr ⟨⟨τ ω, hbound ω⟩, rfl⟩
  have hpart := Measure.restrict_iUnion (μ := μ) hd hm
  rw [hcover] at hpart
  simpa [s] using hpart


end
end HeavyTailedNoise
