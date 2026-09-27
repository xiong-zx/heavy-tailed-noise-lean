import HeavyTailedNoise.Probability.HaarConditionalFrame
import HeavyTailedNoise.Probability.FiberwiseFreshTail

/-!
Combine an existing conditional law with a fresh tail independent of the
conditioning variable and response jointly. The tail is unobserved; this
lemma identifies the joint law used by a later measurable continuation.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem hasCondDistrib_pair_fresh_tail
    {Ω A B Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (D : Ω → B) (Z : Ω → Y)
    (hX : Measurable X) (hD : Measurable D) (hZ : Measurable Z)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (ρ : Measure Y) [IsProbabilityMeasure ρ]
    (hcond : HasCondDistrib D X κ P)
    (hTail : P.map (fun ω => ((X ω, D ω), Z ω)) =
      (P.map (fun ω => (X ω, D ω))).prod ρ) :
    HasCondDistrib (fun ω => (D ω, Z ω)) X
      (κ ⊗ₖ Kernel.const (A × B) ρ) P := by
  refine ⟨(hX.prodMk (hD.prodMk hZ)).aemeasurable, ?_⟩
  change P.map (fun ω => (X ω, D ω, Z ω)) =
    (P.map X) ⊗ₘ (κ ⊗ₖ Kernel.const (A × B) ρ)
  calc
    _ = (P.map (fun ω => ((X ω, D ω), Z ω))).map
        (MeasurableEquiv.prodAssoc : ((A × B) × Y) → A × B × Y) := by
      rw [Measure.map_map (by fun_prop) ((hX.prodMk hD).prodMk hZ)]
      rfl
    _ = ((P.map (fun ω => (X ω, D ω))).prod ρ).map
        (MeasurableEquiv.prodAssoc : ((A × B) × Y) → A × B × Y) := by
      rw [hTail]
    _ = (((P.map X) ⊗ₘ κ).prod ρ).map
        (MeasurableEquiv.prodAssoc : ((A × B) × Y) → A × B × Y) := by
      rw [hcond.map_eq]
    _ = (((P.map X) ⊗ₘ κ) ⊗ₘ Kernel.const (A × B) ρ).map
        (MeasurableEquiv.prodAssoc : ((A × B) × Y) → A × B × Y) := by
      rw [Measure.compProd_const]
    _ = _ := Measure.compProd_assoc'

end

end HeavyTailedNoise
