import HeavyTailedNoise.Model.Basic

/-!
A fiberwise fresh-tail law remains a product law after mixing over a hidden
parameter. This is the measure-theoretic bridge needed when the stopping rule
depends on the full Haar frame.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

theorem fiberwise_fresh_tail_jointLaw
    {F Seed H Y : Type*}
    [MeasurableSpace F] [MeasurableSpace Seed]
    [MeasurableSpace H] [MeasurableSpace Y]
    (μ : Measure F) (ν : Measure Seed) (ρ : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ]
    (S : F → Seed → H) (Z : F → Seed → Y)
    (hS : Measurable (fun z : F × Seed => S z.1 z.2))
    (hZ : Measurable (fun z : F × Seed => Z z.1 z.2))
    (hFiber : ∀ f : F,
      ν.map (fun ξ => (S f ξ, Z f ξ)) =
        (ν.map (S f)).prod ρ) :
    (μ.prod ν).map (fun z : F × Seed => ((z.1, S z.1 z.2), Z z.1 z.2)) =
      ((μ.prod ν).map (fun z : F × Seed => (z.1, S z.1 z.2))).prod ρ := by
  let R : F × Seed → F × H := fun z => (z.1, S z.1 z.2)
  let W : F × Seed → (F × H) × Y := fun z => (R z, Z z.1 z.2)
  have hR : Measurable R := measurable_fst.prodMk hS
  have hW : Measurable W := hR.prodMk hZ
  apply Measure.ext_prod
  intro B C hB hC
  have hBC : MeasurableSet (B ×ˢ C) := hB.prod hC
  have hRB : MeasurableSet (R ⁻¹' B) := hB.preimage hR
  have hWBC : MeasurableSet (W ⁻¹' (B ×ˢ C)) := hBC.preimage hW
  have hfiber (f : F) :
      ν {ξ | (f, S f ξ) ∈ B ∧ Z f ξ ∈ C} =
        ν {ξ | (f, S f ξ) ∈ B} * ρ C := by
    let Bf : Set H := (Prod.mk f) ⁻¹' B
    have hBf : MeasurableSet Bf :=
      hB.preimage (measurable_const.prodMk measurable_id)
    have hSC : MeasurableSet (Bf ×ˢ C) := hBf.prod hC
    have hSf : Measurable (S f) := hS.comp (measurable_const.prodMk measurable_id)
    have hZf : Measurable (Z f) := hZ.comp (measurable_const.prodMk measurable_id)
    calc
      ν {ξ | (f, S f ξ) ∈ B ∧ Z f ξ ∈ C} =
          (ν.map (fun ξ => (S f ξ, Z f ξ))) (Bf ×ˢ C) := by
            rw [Measure.map_apply (hSf.prodMk hZf) hSC]
            rfl
      _ = ((ν.map (S f)).prod ρ) (Bf ×ˢ C) := by rw [hFiber f]
      _ = ν {ξ | (f, S f ξ) ∈ B} * ρ C := by
        rw [Measure.prod_prod, Measure.map_apply hSf hBf]
        rfl
  calc
    ((μ.prod ν).map W) (B ×ˢ C) =
        ∫⁻ f, ν {ξ | (f, S f ξ) ∈ B ∧ Z f ξ ∈ C} ∂μ := by
          rw [Measure.map_apply hW hBC, Measure.prod_apply hWBC]
          rfl
    _ = ∫⁻ f, ν {ξ | (f, S f ξ) ∈ B} * ρ C ∂μ := by
          simp_rw [hfiber]
    _ = (∫⁻ f, ν {ξ | (f, S f ξ) ∈ B} ∂μ) * ρ C := by
          have hsec : Measurable (fun f => ν {ξ | (f, S f ξ) ∈ B}) := by
            change Measurable (fun f => ν (Prod.mk f ⁻¹' (R ⁻¹' B)))
            exact measurable_measure_prodMk_left hRB
          exact lintegral_mul_const (ρ C) hsec
    _ = ((μ.prod ν).map R) B * ρ C := by
          rw [Measure.map_apply hR hB, Measure.prod_apply hRB]
          rfl
    _ = (((μ.prod ν).map R).prod ρ) (B ×ˢ C) := by
          rw [Measure.prod_prod]

end

end HeavyTailedNoise
