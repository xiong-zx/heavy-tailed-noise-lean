import HeavyTailedNoise.Model.Basic

/-!
Split a finite iid seed tape into its first `n` seeds and its last fresh seed.
This is the finite product-law identity used to identify a deterministic
Gaussian recursion with `adaptiveGaussianLaw` by induction.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem iidSeedLaw_map_prefix_last
    {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.pi (fun _ : Fin (n + 1) => ν)).map
      (fun ξ : Fin (n + 1) → Seed =>
        ((fun i : Fin n => ξ i.castSucc), ξ (Fin.last n))) =
      (Measure.pi (fun _ : Fin n => ν)).prod ν := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Seed) (Fin.last n)
  have hmp := (Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ν) (Fin.last n))).map_eq
  have heq : (Prod.swap ∘ e) =
      (fun ξ : Fin (n + 1) → Seed =>
        ((fun i : Fin n => ξ i.castSucc), ξ (Fin.last n))) := by
    funext ξ
    apply Prod.ext
    · funext i
      simp [e, Fin.init]
    · simp [e]
  rw [heq] at hmp
  exact hmp

end

end HeavyTailedNoise
