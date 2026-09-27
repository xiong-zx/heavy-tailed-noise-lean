import HeavyTailedNoise.Lower.Gated.JointFrozenSnapshotMeas
import HeavyTailedNoise.Probability.ConditionalParametricMap
import HeavyTailedNoise.Lower.Gated.NextDirectionFrozenKernel

/-!
One jointly measurable kernel on revealed-prefix/stopped-snapshot data.
Its value is exactly the fixed-prefix direction/transcript composition
product already controlled by the KL and pinhole theorems.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem kernel_compProd_const_eq_prod
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (κ : Kernel A B) [IsMarkovKernel κ]
    (ρ : Measure C) [IsProbabilityMeasure ρ] :
    κ ⊗ₖ Kernel.const (A × B) ρ =
      Kernel.prod κ (Kernel.const A ρ) := by
  ext a s hs
  rw [Kernel.compProd_apply hs, Kernel.prod_apply, Measure.prod_apply hs]
  simp only [Kernel.const_apply]

def frozenSnapshotPairMap
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (z : ((Fin j.val → Point d) ×
      (Bool × ℕ × Transcript d N × Point d)) ×
      (Point d × (Fin m → Point d))) : Point d × Transcript d N :=
  (z.2.1,
    actualFrozenGaussianSeedState hT
      (nextDirectionPrefixFrame j z.1.1 z.2.1) j A r
      (idealPreResponseHistoryOfTuple z.1.2) a m z.2.2)

theorem measurable_frozenSnapshotPairMap
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Measurable (frozenSnapshotPairMap (m := m) hT j A r a) :=
  (measurable_fst.comp measurable_snd).prodMk
    (measurable_joint_nextDirectionFrozenState_snapshot_tuple hT j A r a)

def frozenSnapshotPairKernel
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Kernel ((Fin j.val → Point d) ×
      (Bool × ℕ × Transcript d N × Point d)) (Point d × Transcript d N) :=
  (Kernel.prod (Kernel.deterministic id measurable_id)
    (Kernel.prod
      ((frameNextKernel d j.val).comap
        (Prod.fst : ((Fin j.val → Point d) ×
          (Bool × ℕ × Transcript d N × Point d)) →
            (Fin j.val → Point d)) measurable_fst)
      (Kernel.const _ (Measure.pi
        (fun _ : Fin m => standardGaussianLaw d))))).map
    (frozenSnapshotPairMap hT j A r a)

instance frozenSnapshotPairKernel_markov
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    IsMarkovKernel (frozenSnapshotPairKernel (m := m) hT j A r a) := by
  unfold frozenSnapshotPairKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_frozenSnapshotPairMap hT j A r a)

theorem frozenSnapshotPairKernel_apply
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (p : (Fin j.val → Point d) ×
      (Bool × ℕ × Transcript d N × Point d)) :
    frozenSnapshotPairKernel (m := m) hT j A r a p =
      (frameNextKernel d j.val p.1) ⊗ₘ
        nextDirectionFrozenKernel (m := m) hT j p.1 A r
          (idealPreResponseHistoryOfTuple p.2) a := by
  unfold frozenSnapshotPairKernel
  rw [Kernel.map_apply _ (measurable_frozenSnapshotPairMap hT j A r a),
    Kernel.prod_apply, Kernel.deterministic_apply measurable_id,
    Measure.dirac_prod, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply,
    Measure.map_map (measurable_frozenSnapshotPairMap hT j A r a)
      measurable_prodMk_left]
  change ((frameNextKernel d j.val p.1).prod
      (Measure.pi (fun _ : Fin m => standardGaussianLaw d))).map
        (fun z : Point d × (Fin m → Point d) =>
          (z.1, actualFrozenGaussianSeedState hT
            (nextDirectionPrefixFrame j p.1 z.1) j A r
            (idealPreResponseHistoryOfTuple p.2) a m z.2)) = _
  rw [← Measure.compProd_const]
  exact compProd_joint_map (frameNextKernel d j.val p.1)
    (Kernel.const (Point d)
      (Measure.pi (fun _ : Fin m => standardGaussianLaw d)))
    (fun z : Point d × (Fin m → Point d) =>
      actualFrozenGaussianSeedState hT
        (nextDirectionPrefixFrame j p.1 z.1) j A r
        (idealPreResponseHistoryOfTuple p.2) a m z.2)
    (measurable_joint_nextDirectionFrozenState hT j p.1 A r
      (idealPreResponseHistoryOfTuple p.2) a)

end

end HeavyTailedNoise
