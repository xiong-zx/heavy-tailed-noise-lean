import HeavyTailedNoise.Probability.BoundedFibers

/-!
Finite disintegration principle for a bounded random time. A common tail law
on every disjoint time fiber implies unconditional independence of the record
and randomly selected tail. No conditional-probability existence assumption on
an arbitrary private-randomness space is needed.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem indepFun_and_tailLaw_of_bounded_nat_fiber_factors
    {Ω R Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace R] [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Y)
    (N : ℕ) (τ : Ω → ℕ) (hτ : Measurable τ)
    (hbound : ∀ ω, τ ω < N + 2)
    (record : Ω → R) (tail : Ω → Y)
    (hrecord : Measurable record) (htail : Measurable tail)
    (hslice : ∀ (t : Fin (N + 2)) (B : Set R) (C : Set Y),
      MeasurableSet B → MeasurableSet C →
      (μ.restrict {ω | τ ω = t.val})
          (record ⁻¹' B ∩ tail ⁻¹' C) =
        (μ.restrict {ω | τ ω = t.val}) (record ⁻¹' B) * ν C) :
    IndepFun record tail μ ∧ μ.map tail = ν := by
  let fiber : Fin (N + 2) → Set Ω := fun t => {ω | τ ω = t.val}
  have hpart : μ = Measure.sum (fun t : Fin (N + 2) =>
      μ.restrict (fiber t)) :=
    measure_eq_sum_restrict_bounded_nat_fibers μ N τ hτ hbound
  have hdecomp (D : Set Ω) (hD : MeasurableSet D) :
      μ D = ∑' t : Fin (N + 2), (μ.restrict (fiber t)) D := by
    calc
      μ D = (Measure.sum (fun t : Fin (N + 2) =>
          μ.restrict (fiber t))) D :=
        congrArg (fun η : Measure Ω => η D) hpart
      _ = _ := Measure.sum_apply _ hD
  have hfactor (B : Set R) (C : Set Y)
      (hB : MeasurableSet B) (hC : MeasurableSet C) :
      μ (record ⁻¹' B ∩ tail ⁻¹' C) =
        μ (record ⁻¹' B) * ν C := by
    have hRB : MeasurableSet (record ⁻¹' B) := hB.preimage hrecord
    have hTC : MeasurableSet (tail ⁻¹' C) := hC.preimage htail
    calc
      μ (record ⁻¹' B ∩ tail ⁻¹' C) =
          ∑' t : Fin (N + 2),
            (μ.restrict (fiber t))
              (record ⁻¹' B ∩ tail ⁻¹' C) :=
        hdecomp _ (hRB.inter hTC)
      _ = ∑' t : Fin (N + 2),
          (μ.restrict (fiber t)) (record ⁻¹' B) * ν C := by
        apply tsum_congr
        intro t
        exact hslice t B C hB hC
      _ = (∑' t : Fin (N + 2),
          (μ.restrict (fiber t)) (record ⁻¹' B)) * ν C := by
        rw [ENNReal.tsum_mul_right]
      _ = μ (record ⁻¹' B) * ν C := by
        rw [← hdecomp _ hRB]
  have htailLaw (C : Set Y) (hC : MeasurableSet C) :
      μ (tail ⁻¹' C) = ν C := by
    have h := hfactor Set.univ C MeasurableSet.univ hC
    simpa using h
  constructor
  · apply (indepFun_iff_measure_inter_preimage_eq_mul).2
    intro B C hB hC
    rw [htailLaw C hC]
    exact hfactor B C hB hC
  · ext C hC
    simpa only [Measure.map_apply htail hC] using htailLaw C hC

end

end HeavyTailedNoise
