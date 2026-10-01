import HeavyTailedNoise.Upper.K1.StationarityAssembly

/-!
The existing canonical runtime query is measurable as a function of the full
fresh seed tape. This only exposes a property of `canonicalRuntimePoint`;
it defines no second query or algorithm state.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem measurable_canonicalRuntimePoint {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (r : Fin P.T) :
    Measurable (canonicalRuntimePoint P O r) := by
  have hprefix : Measurable
      (fun seeds : Fin (responseCount P) → Seed =>
        fun j : Fin (batchStart P r.val) =>
          seeds ⟨j.val, lt_trans j.isLt (outputIndex P r).isLt⟩) := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply _
  have hanchor : Measurable
      (fun _ : Fin (responseCount P) → Seed =>
        (⟨0, P.T_pos⟩ : Fin P.T)) := measurable_const
  have hhistory : Measurable
      (fun seeds : Fin (responseCount P) → Seed =>
        runTranscript O (algorithm (d := d) P)
          (⟨0, P.T_pos⟩ : Fin P.T) (batchStart P r.val)
          (fun j : Fin (batchStart P r.val) =>
            seeds ⟨j.val, lt_trans j.isLt (outputIndex P r).isLt⟩)) :=
    (measurable_runTranscript O (algorithm (d := d) P)
      (batchStart P r.val)).comp (hanchor.prodMk hprefix)
  exact (measurable_query P (batchStart P r.val)).comp hhistory

end

end HeavyTailedNoise.UpperK1
