import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! Fixing the first coordinate of a jointly measurable function preserves
measurability in the second coordinate. -/

namespace HeavyTailedNoise.UpperK1

theorem measurable_fixed_first_arg
    {History Batch Value : Type*}
    [MeasurableSpace History] [MeasurableSpace Batch]
    [MeasurableSpace Value]
    (f : History × Batch → Value) (hf : Measurable f)
    (H : History) :
    Measurable (fun batch => f (H, batch)) :=
  hf.comp (measurable_const.prodMk measurable_id)

end HeavyTailedNoise.UpperK1
