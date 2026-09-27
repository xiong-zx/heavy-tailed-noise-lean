import HeavyTailedNoise.Probability.ConditionalFreshTail

/-!
A continuation may depend jointly on the conditioning snapshot and the
unobserved random response. Its conditional law is the corresponding
measurable kernel map, with no regularity assumption on the snapshot space.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem compProd_joint_map
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C]
    (q : Measure A) [IsProbabilityMeasure q]
    (κ : Kernel A B) [IsMarkovKernel κ]
    (f : A × B → C) (hf : Measurable f) :
    (q ⊗ₘ κ).map (fun p : A × B => (p.1, f p)) =
      q ⊗ₘ ((Kernel.prod
        (Kernel.deterministic (id : A → A) measurable_id) κ).map f) := by
  have hG : Measurable (fun p : A × B => (p.1, f p)) :=
    measurable_fst.prodMk hf
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map hφ hG]
  have hφG : Measurable (fun p : A × B => φ (p.1, f p)) := hφ.comp hG
  rw [Measure.lintegral_compProd hφG, Measure.lintegral_compProd hφ]
  apply lintegral_congr
  intro a
  rw [Kernel.map_apply _ hf, Kernel.prod_apply,
    Kernel.deterministic_apply measurable_id, Measure.dirac_prod]
  have hφa : Measurable (fun c : C => φ (a, c)) :=
    hφ.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map hφa hf]
  have hφaf : Measurable (fun p : A × B => φ (a, f p)) := hφa.comp hf
  rw [lintegral_map hφaf measurable_prodMk_left]
  rfl

theorem hasCondDistrib_joint_map
    {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (hcond : HasCondDistrib Y X κ P)
    (f : A × B → C) (hf : Measurable f) :
    HasCondDistrib (fun ω => f (X ω, Y ω)) X
      ((Kernel.prod
        (Kernel.deterministic (id : A → A) measurable_id) κ).map f) P := by
  refine ⟨(hX.prodMk (hf.comp (hX.prodMk hY))).aemeasurable, ?_⟩
  change P.map (fun ω => (X ω, f (X ω, Y ω))) = _
  calc
    _ = (P.map (fun ω => (X ω, Y ω))).map
        (fun p : A × B => (p.1, f p)) := by
      rw [Measure.map_map (measurable_fst.prodMk hf) (hX.prodMk hY)]
      rfl
    _ = ((P.map X) ⊗ₘ κ).map (fun p : A × B => (p.1, f p)) := by
      rw [hcond.map_eq]
    _ = _ := compProd_joint_map (P.map X) κ f hf

end

end HeavyTailedNoise
