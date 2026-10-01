import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! A jointly measurable scalar readout remains measurable after two
measurable inputs are paired.  No oracle or algorithm structure is used. -/

namespace HeavyTailedNoise.UpperK1

theorem measurable_pair_readout
    {α X Y : Type*}
    [MeasurableSpace α] [MeasurableSpace X] [MeasurableSpace Y]
    (readout : X × Y → ℝ) (hreadout : Measurable readout)
    (x : α → X) (y : α → Y)
    (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun a => readout (x a, y a)) :=
  hreadout.comp (hx.prodMk hy)

end HeavyTailedNoise.UpperK1
