import HeavyTailedNoise.Lower.Gated.IdealExtendedNoise

/-!
Adding independent auxiliary Gaussian coordinates does not change the
original N-coordinate tape or its independent joint law with the frame.
Auxiliary coordinates are analysis variables, never extra oracle responses.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem idealExtendedNoiseTake_law {d N m : ℕ} :
    (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).map
      (idealExtendedNoiseTake (d := d) (N := N) (m := m)) =
        Measure.pi (fun _ : Fin N => standardGaussianLaw d) := by
  let ν := Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)
  have hind : iIndepFun
      (fun i (ξ : Fin (N + m) → Point d) => ξ i) ν :=
    iIndepFun_pi (X := fun _ : Fin (N + m) => id)
      (fun _ => aemeasurable_id)
  have hinj : Function.Injective (fun i : Fin N =>
      (⟨i.val, by omega⟩ : Fin (N + m))) := by
    intro i j hij
    exact Fin.ext (congrArg (Fin.val : Fin (N + m) → ℕ) hij)
  have hindHead : iIndepFun (fun i : Fin N =>
      fun ξ : Fin (N + m) → Point d => ξ ⟨i.val, by omega⟩) ν :=
    hind.precomp (g := fun i : Fin N =>
      (⟨i.val, by omega⟩ : Fin (N + m))) hinj
  have hcoord (i : Fin N) :
      HasLaw (fun ξ : Fin (N + m) → Point d => ξ ⟨i.val, by omega⟩)
        (standardGaussianLaw d) ν := by
    exact ⟨(measurable_pi_apply (⟨i.val, by omega⟩ : Fin (N + m))).aemeasurable,
      (measurePreserving_eval
        (fun _ : Fin (N + m) => standardGaussianLaw d)
        (⟨i.val, by omega⟩ : Fin (N + m))).map_eq⟩
  exact (hindHead.hasLaw_pi hcoord).map_eq

theorem idealExtendedNoiseTake_jointLaw
    {F : Type*} [MeasurableSpace F] {d N m : ℕ}
    (μ : Measure F) [IsProbabilityMeasure μ] :
    (μ.prod (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d))).map
      (fun z : F × (Fin (N + m) → Point d) =>
        (z.1, idealExtendedNoiseTake z.2)) =
      μ.prod (Measure.pi (fun _ : Fin N => standardGaussianLaw d)) := by
  have h := (Measure.map_prod_map μ
    (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d))
    measurable_id (measurable_idealExtendedNoiseTake (d := d) (N := N) (m := m))).symm
  have hfun : Prod.map (id : F → F)
      (idealExtendedNoiseTake (d := d) (N := N) (m := m)) =
      (fun z : F × (Fin (N + m) → Point d) =>
        (z.1, idealExtendedNoiseTake z.2)) := by funext z; rfl
  simpa only [hfun, Measure.map_id, idealExtendedNoiseTake_law] using h

theorem idealExtendedNoiseTail_jointLaw
    {F : Type*} [MeasurableSpace F] {d N m : ℕ}
    (μ : Measure F) [IsProbabilityMeasure μ] (t : ℕ) (ht : t ≤ N) :
    (μ.prod (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d))).map
      (fun z : F × (Fin (N + m) → Point d) =>
        (z.1, idealExtendedNoiseTail t ht z.2)) =
      μ.prod (Measure.pi (fun _ : Fin m => standardGaussianLaw d)) := by
  have h := (Measure.map_prod_map μ
    (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d))
    measurable_id (measurable_idealExtendedNoiseTail (d := d) (m := m) t ht)).symm
  have hfun : Prod.map (id : F → F)
      (idealExtendedNoiseTail (d := d) (m := m) t ht) =
      (fun z : F × (Fin (N + m) → Point d) =>
        (z.1, idealExtendedNoiseTail t ht z.2)) := by funext z; rfl
  simpa only [hfun, Measure.map_id, idealExtendedNoiseTail_law] using h

end

end HeavyTailedNoise
