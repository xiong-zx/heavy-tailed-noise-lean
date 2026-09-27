import HeavyTailedNoise.Lower.Gated.IdealStoppedNoiseIndependent

/-!
Product-law form of fixed-time fresh Gaussian noise at a possible stage start.
This is the measure identity needed for finite slicing over the random start.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem idealNoiseSuffixLaw {d N : ℕ} (t : ℕ) :
    (Measure.pi (fun _ : Fin N => standardGaussianLaw d)).map
      (fun ξ : Fin N → Point d =>
        fun i : idealNoiseSuffixIndices N t => ξ i.1) =
      Measure.pi (fun _ : idealNoiseSuffixIndices N t =>
        standardGaussianLaw d) := by
  let ν : Measure (Fin N → Point d) :=
    Measure.pi (fun _ : Fin N => standardGaussianLaw d)
  let S := idealNoiseSuffixIndices N t
  have hind : iIndepFun (fun i (ξ : Fin N → Point d) => ξ i) ν :=
    iIndepFun_pi (X := fun _ : Fin N => id)
      (fun _ => aemeasurable_id)
  have hindS : iIndepFun (fun i : S =>
      fun ξ : Fin N → Point d => ξ i.1) ν :=
    hind.precomp (g := fun i : S => i.1) Subtype.val_injective
  have hcoord (i : S) :
      HasLaw (fun ξ : Fin N → Point d => ξ i.1)
        (standardGaussianLaw d) ν := by
    exact ⟨(measurable_pi_apply i.1).aemeasurable,
      (measurePreserving_eval
        (fun _ : Fin N => standardGaussianLaw d) i.1).map_eq⟩
  exact (hindS.hasLaw_pi hcoord).map_eq

theorem idealStoppedEventTuple_jointLaw
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (t : ℕ) (htN : t ≤ N) :
    (Measure.pi (fun _ : Fin N => standardGaussianLaw d)).map
      (fun ξ : Fin N → Point d =>
        (idealStoppedEventTuple hT U k A r a t ξ,
          fun i : idealNoiseSuffixIndices N t => ξ i.1)) =
      ((Measure.pi (fun _ : Fin N => standardGaussianLaw d)).map
        (idealStoppedEventTuple hT U k A r a t)).prod
          (Measure.pi (fun _ : idealNoiseSuffixIndices N t =>
            standardGaussianLaw d)) := by
  have hrecord := measurable_idealStoppedEventTuple hT U k A r a t
  have hsuffix : Measurable (fun ξ : Fin N → Point d =>
      fun i : idealNoiseSuffixIndices N t => ξ i.1) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply i.1
  have hprod := (idealStoppedEventTuple_indep_suffix
    hT U k A r a t htN).map_prod_eq_prod_map_map
      hrecord.aemeasurable hsuffix.aemeasurable
  rw [idealNoiseSuffixLaw t] at hprod
  exact hprod

end

end HeavyTailedNoise
