import HeavyTailedNoise.Probability.FiberwiseFreshTail
import HeavyTailedNoise.Lower.Gated.IdealRandomStartFreshNoise
import HeavyTailedNoise.Lower.Gated.JointPrefixGradientMeas

/-!
The random-start Gaussian suffix stays independent after mixing over a hidden
full frame. The frame is included in the recorded variable, so this assertion
also applies when the stopping time depends on unrevealed frame columns.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem measurable_joint_idealStoppedRecordExtended
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Measurable
      (fun z : (Fin T → Point d) × (Fin (N + m) → Point d) =>
        idealPreResponseTuple
          (idealStoppedPreHistory hT z.1 k A r
            (idealExtendedNoiseTake z.2) a)) := by
  have hinput : Measurable
      (fun z : (Fin T → Point d) × (Fin (N + m) → Point d) =>
        (framePrefix (Nat.succ_le_iff.mpr k.isLt) z.1,
          (r, idealExtendedNoiseTake z.2))) :=
    ((measurable_framePrefix (Nat.succ_le_iff.mpr k.isLt)).comp
      measurable_fst).prodMk
      (measurable_const.prodMk
        (measurable_idealExtendedNoiseTake.comp measurable_snd))
  have hc := (measurable_idealStoppedPreHistoryFromPrefix hT k A a).comp hinput
  convert hc using 1
  funext z
  exact idealStoppedPreHistoryFromPrefix_eq hT z.1 k A r
    (idealExtendedNoiseTake z.2) a

theorem measurable_joint_idealRandomStartTail
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Measurable
      (fun z : (Fin T → Point d) × (Fin (N + m) → Point d) =>
        idealRandomStartTail hT z.1 k A r a z.2) := by
  have hS := measurable_joint_idealStoppedRecordExtended (m := m) hT k A r a
  have hτ : Measurable
      (fun z : (Fin T → Point d) × (Fin (N + m) → Point d) =>
        idealExtendedStageStart hT z.1 k A r a z.2) := by
    have hp : Measurable
        (fun z : Bool × ℕ × Transcript d N × Point d => z.2.1) :=
      measurable_fst.comp measurable_snd
    have hc := hp.comp hS
    convert hc using 1
    funext z
    exact (idealStoppedPreTuple_time hT z.1 k A r
      (idealExtendedNoiseTake z.2) a).symm
  let tail : ((Fin (N + m) → Point d) × ℕ) → (Fin m → Point d) :=
    fun z => idealExtendedNoiseTail (min z.2 N)
      (Nat.min_le_right _ _) z.1
  have ht : Measurable tail :=
    measurable_from_prod_countable_left (fun t =>
      measurable_idealExtendedNoiseTail (min t N)
        (Nat.min_le_right _ _))
  have hpair : Measurable
      (fun z : (Fin T → Point d) × (Fin (N + m) → Point d) =>
        (z.2, idealExtendedStageStart hT z.1 k A r a z.2)) :=
    measurable_snd.prodMk hτ
  exact ht.comp hpair

theorem idealRandomStart_record_tail_jointLaw_mixedFrame
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (μ : Measure (Fin T → Point d)) [IsProbabilityMeasure μ] :
    let ν := Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)
    let ρ := Measure.pi (fun _ : Fin m => standardGaussianLaw d)
    (μ.prod ν).map (fun z : (Fin T → Point d) × (Fin (N + m) → Point d) =>
      ((z.1,
        idealPreResponseTuple
          (idealStoppedPreHistory hT z.1 k A r
            (idealExtendedNoiseTake z.2) a)),
        idealRandomStartTail hT z.1 k A r a z.2)) =
      ((μ.prod ν).map
        (fun z : (Fin T → Point d) × (Fin (N + m) → Point d) =>
          (z.1,
            idealPreResponseTuple
              (idealStoppedPreHistory hT z.1 k A r
                (idealExtendedNoiseTake z.2) a)))).prod ρ := by
  dsimp only
  let S : (Fin T → Point d) → (Fin (N + m) → Point d) →
      Bool × ℕ × Transcript d N × Point d :=
    fun U ξ => idealPreResponseTuple
      (idealStoppedPreHistory hT U k A r
        (idealExtendedNoiseTake ξ) a)
  let Z : (Fin T → Point d) → (Fin (N + m) → Point d) →
      (Fin m → Point d) :=
    fun U ξ => idealRandomStartTail hT U k A r a ξ
  have hS := measurable_joint_idealStoppedRecordExtended (m := m) hT k A r a
  have hZ := measurable_joint_idealRandomStartTail (m := m) hT k A r a
  have hFiber (U : Fin T → Point d) :
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).map
          (fun ξ => (S U ξ, Z U ξ)) =
        ((Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).map
          (S U)).prod
          (Measure.pi (fun _ : Fin m => standardGaussianLaw d)) :=
    idealRandomStart_record_tail_jointLaw hT U k A r a
  exact fiberwise_fresh_tail_jointLaw μ
    (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d))
    (Measure.pi (fun _ : Fin m => standardGaussianLaw d)) S Z hS hZ hFiber

end

end HeavyTailedNoise
