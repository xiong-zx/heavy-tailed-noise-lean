import HeavyTailedNoise.Lower.Gated.IdealStoppedDirectionTailLaw
import HeavyTailedNoise.Lower.Gated.FrozenSnapshotJointKernel
import HeavyTailedNoise.Lower.Gated.ActualPrefixFrozenIdentity

/-!
Conditional law of the actual full-frame frozen continuation at a positive
stage start. The canonical prefix representation is proved equal to the
original full-frame truncated response, then the checked conditional
direction/tail law is pushed through the jointly measurable continuation.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem idealStopped_actualFrozen_hasCondDistrib
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hTd : T ≤ d)
    (k : Fin T) (hk : k.val + 1 + 1 ≤ T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    let j : Fin T := ⟨k.val + 1, by omega⟩
    let μ := preselectedOrthonormalFrameLaw d T hTd
    let ν := Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)
    HasCondDistrib
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} ×
          (Fin (N + m) → Point d) =>
        (z.1.1 j,
          actualFrozenGaussianSeedState hT z.1.1 j A r
            (idealStoppedPreHistory hT z.1.1 k A r
              (idealExtendedNoiseTake z.2) a)
            a m (idealRandomStartTail hT z.1.1 k A r a z.2)))
      (idealStoppedDirectionData hT k A r a)
      (frozenSnapshotPairKernel (m := m) hT j A r a)
      (μ.prod ν) := by
  dsimp only
  let j : Fin T := ⟨k.val + 1, by omega⟩
  let P := (preselectedOrthonormalFrameLaw d T hTd).prod
    (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d))
  let X := idealStoppedDirectionData (m := m) hT k A r a
  let Y : ({U : Fin T → Point d // Orthonormal ℝ U} ×
      (Fin (N + m) → Point d)) → Point d × (Fin m → Point d) :=
    fun z => ((framePrefix hk z.1.1) (Fin.last (k.val + 1)),
      idealRandomStartTail hT z.1.1 k A r a z.2)
  let κ : Kernel ((Fin (k.val + 1) → Point d) ×
      (Bool × ℕ × Transcript d N × Point d)) (Point d) :=
    (frameNextKernel d (k.val + 1)).comap Prod.fst measurable_fst
  have hX : Measurable X := measurable_idealStoppedDirectionData hT k A r a
  have hco : Measurable
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} ×
          (Fin (N + m) → Point d) => (z.1.1, z.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hD : Measurable
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} ×
          (Fin (N + m) → Point d) =>
        (framePrefix hk z.1.1) (Fin.last (k.val + 1))) :=
    (((measurable_pi_apply (Fin.last (k.val + 1))).comp
      (measurable_framePrefix hk)).comp measurable_subtype_coe).comp measurable_fst
  have hY : Measurable Y := hD.prodMk
    ((measurable_joint_idealRandomStartTail hT k A r a).comp hco)
  have hcond := idealStopped_nextDirection_tail_hasCondDistrib
    (m := m) hT hTd k hk A r a
  dsimp only at hcond
  rw [kernel_compProd_const_eq_prod] at hcond
  have hmap := hasCondDistrib_joint_map P X Y hX hY
    (Kernel.prod κ
      (Kernel.const _ (Measure.pi (fun _ : Fin m => standardGaussianLaw d))))
    hcond (frozenSnapshotPairMap hT j A r a)
    (measurable_frozenSnapshotPairMap hT j A r a)
  have hresult : HasCondDistrib
      (fun z => frozenSnapshotPairMap hT j A r a (X z, Y z))
      X (frozenSnapshotPairKernel (m := m) hT j A r a) P := by
    simpa only [frozenSnapshotPairKernel, κ] using hmap
  have hfun :
      (fun z => frozenSnapshotPairMap hT j A r a (X z, Y z)) =
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} ×
          (Fin (N + m) → Point d) =>
        (z.1.1 j,
          actualFrozenGaussianSeedState hT z.1.1 j A r
            (idealStoppedPreHistory hT z.1.1 k A r
              (idealExtendedNoiseTake z.2) a)
            a m (idealRandomStartTail hT z.1.1 k A r a z.2))) := by
    funext z
    have hθ : (framePrefix hk z.1.1) (Fin.last (k.val + 1)) = z.1.1 j := by
      apply congrArg z.1.1
      apply Fin.ext
      rfl
    dsimp only [frozenSnapshotPairMap, X, Y, idealStoppedDirectionData]
    rw [idealPreResponseHistoryOfTuple_tuple, hθ]
    exact congrArg (fun tr : Transcript d N => (z.1.1 j, tr))
      (actualFrozenGaussianSeedState_nextDirectionPrefixFrame hT z.1.1 j A r
        (idealStoppedPreHistory hT z.1.1 k A r
          (idealExtendedNoiseTake z.2) a)
        a (idealRandomStartTail hT z.1.1 k A r a z.2))
  rw [hfun] at hresult
  exact hresult

end

end HeavyTailedNoise
