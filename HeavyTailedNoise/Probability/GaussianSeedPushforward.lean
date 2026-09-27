import HeavyTailedNoise.Model.Basic

/-!
Push a deterministic measurable state map through the first coordinate of a
product law. This identifies the law of the old state plus a fresh seed in
the adaptive Gaussian recursion.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

theorem map_prod_seed_state
    {A H Seed Y : Type*}
    [MeasurableSpace A] [MeasurableSpace H]
    [MeasurableSpace Seed] [MeasurableSpace Y]
    (P : Measure A) [SFinite P]
    (ν : Measure Seed) [SFinite ν]
    (F : A → H) (hF : Measurable F)
    (u : H × Seed → Y) (hu : Measurable u) :
    (P.prod ν).map (fun z : A × Seed => u (F z.1, z.2)) =
      ((P.map F).prod ν).map u := by
  have hpair : Measurable (Prod.map F (id : Seed → Seed)) :=
    hF.prodMap measurable_id
  calc
    (P.prod ν).map (fun z : A × Seed => u (F z.1, z.2)) =
        ((P.prod ν).map (Prod.map F id)).map u := by
          rw [Measure.map_map hu hpair]
          rfl
    _ = (((P.map F).prod (ν.map id))).map u := by
          rw [Measure.map_prod_map P ν hF measurable_id]
    _ = ((P.map F).prod ν).map u := by simp

end

end HeavyTailedNoise
