import HeavyTailedNoise.Upper.K1.Algorithm

/-!
Measurability of the scalar tracker increment as a composition of four
already measurable inputs.  This statement is independent of a particular
history type, seed space, or algorithm transcript.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem measurable_trackerIncrement_composition
    {α : Type*} [MeasurableSpace α]
    {d : ℕ}
    (readout : Point d × Point d → ℝ) (hreadout : Measurable readout)
    (x w estimate y : α → Point d)
    (hx : Measurable x) (hw : Measurable w)
    (hestimate : Measurable estimate) (hy : Measurable y) :
    Measurable (fun z =>
      readout (x z - P.h • direction (estimate z),
        coarseCenter P (w z) (y z)) - readout (x z, w z)) := by
  have hnext : Measurable (fun z =>
      x z - P.h • direction (estimate z)) :=
    hx.sub ((measurable_const : Measurable (fun _ : α => P.h)).smul
      (measurable_direction.comp hestimate))
  have hcenter : Measurable (fun z => coarseCenter P (w z) (y z)) :=
    measurable_coarseCenter P hw hy
  exact (hreadout.comp (hnext.prodMk hcenter)).sub
    (hreadout.comp (hx.prodMk hw))

end

end HeavyTailedNoise.UpperK1
