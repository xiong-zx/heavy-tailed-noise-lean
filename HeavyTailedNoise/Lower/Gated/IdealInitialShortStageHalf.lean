import HeavyTailedNoise.Lower.Gated.InitialFrozenHaarLaw
import HeavyTailedNoise.Lower.Gated.ExtendedGaussianMarginal
import HeavyTailedNoise.Lower.Gated.FrozenSnapshotCapProbability
import HeavyTailedNoise.Lower.Gated.FrozenCapFinalEventEquivalence
import HeavyTailedNoise.Lower.Gated.IdealStageFiltration

/-!
The actual initial short-stage ordinary mean is at most one half under the
preselected full-frame Haar law and the original `N` Gaussian coordinates.
The initial frozen joint law and numerical cap theorem are instantiated, not
assumed. Head/tail-zero marginals of an extended analysis tape connect the
original and auxiliary experiments without issuing extra oracle responses.
The canonical initial record includes the arbitrary output when `N=0`.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

/-- A view of the existing initial frozen continuation; no new recursion. -/
def idealInitialFrozenObservable
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin m → Point d)) :
    Point d × Transcript d N :=
  (z.1.1 ⟨0, hT⟩,
    actualFrozenGaussianSeedState hT z.1.1 ⟨0, hT⟩ A r
      (idealInitialPreHistory A r) a m z.2)

theorem measurable_idealInitialFrozenObservable
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Measurable (idealInitialFrozenObservable (m := m) hT A r a) := by
  let j : Fin T := ⟨0, hT⟩
  let v := emptyRevealedPrefix d
  let s := idealInitialPreHistory A r
  let f : Point d × (Fin m → Point d) → Point d × Transcript d N := fun z =>
    (z.1, actualFrozenGaussianSeedState hT
      (nextDirectionPrefixFrame j v z.1) j A r s a m z.2)
  let g : {U : Fin T → Point d // Orthonormal ℝ U} ×
      (Fin m → Point d) → Point d × (Fin m → Point d) := fun z => (z.1.1 j, z.2)
  have hf : Measurable f := measurable_fst.prodMk
    (measurable_joint_nextDirectionFrozenState (m := m) hT j v A r s a)
  have hg : Measurable g :=
    ((measurable_pi_apply j).comp
      (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd
  have heq : idealInitialFrozenObservable (m := m) hT A r a = f ∘ g := by
    funext z
    apply Prod.ext
    · rfl
    · have hp : framePrefix (Nat.le_of_lt j.isLt) z.1.1 = v := by
        funext i
        exact i.elim0
      have hs := actualFrozenGaussianSeedState_nextDirectionPrefixFrame
        hT z.1.1 j A r s a z.2
      rw [hp] at hs
      exact hs.symm
  rw [heq]
  exact hf.comp hg

/-- The checked original (unrepaired) joint snapshot kernel gives the
initial frozen cap probability bound under the actual full-frame marginal.
-/
theorem idealInitialFrozenCap_probability_half
    {d T N m : ℕ} {S : ℝ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hdim : 2 * T ≤ d) (hS : 0 < S)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / (16 * 300 ^ 2)))
    (hdimlog : 21400 * (1 + Real.log (2 * (gatedStageLength d T S : ℝ))) ≤
      (d - T : ℕ))
    (hm : m ≤ gatedStageLength d T S)
    (A : RandomAlgorithm d N Private) (r : Private) :
    (((preselectedOrthonormalFrameLaw d T (by omega)).prod
      (Measure.pi (fun _ : Fin m => standardGaussianLaw d))).real
      ((idealInitialFrozenObservable (m := m) hT A r ((S / 80) / Real.sqrt d)) ⁻¹'
        nextDirectionFinalCapEvent (m := m) hT (emptyRevealedPrefix d) A r
          (idealInitialPreHistory A r))) ≤ (1 : ℝ) / 2 := by
  have hTd : T ≤ d := by omega
  let j : Fin T := ⟨0, hT⟩
  let v := emptyRevealedPrefix d
  let s := idealInitialPreHistory A r
  let a := (S / 80) / Real.sqrt d
  let p := (v, idealPreResponseTuple s)
  let P := (preselectedOrthonormalFrameLaw d T hTd).prod
    (Measure.pi (fun _ : Fin m => standardGaussianLaw d))
  let G := idealInitialFrozenObservable (m := m) hT A r a
  let E := nextDirectionFinalCapEvent (m := m) hT v A r s
  have hG : Measurable G := measurable_idealInitialFrozenObservable hT A r a
  have hE : MeasurableSet E := measurableSet_nextDirectionFinalCapEvent hT v A r s
  have hlaw := initialFrozenHaarJointLaw (m := m) hT hTd A r a
  change P.map G = (frameNextKernel d 0 v) ⊗ₘ
    nextDirectionFrozenKernel (m := m) hT j v A r s a at hlaw
  have hv : Orthonormal ℝ v := Orthonormal.of_isEmpty v
  have hhalf := frozenSnapshotPairKernel_cap_probability_half_actual_parameters
    (m := m) hT hdim hS hlarge hdimlog hm j A r p hv
  rw [frozenSnapshotPairKernel_apply] at hhalf
  have hsection := frozenSnapshotFinalCapEvent_section (m := m) hT j A r p
  rw [hsection] at hhalf
  simp only [p, idealPreResponseHistoryOfTuple_tuple] at hhalf
  calc
    P.real (G ⁻¹' E) = (P.map G).real E := by
      rw [measureReal_def, measureReal_def, Measure.map_apply hG hE]
    _ = ((frameNextKernel d 0 v) ⊗ₘ
        nextDirectionFrozenKernel (m := m) hT j v A r s a).real E := by rw [hlaw]
    _ ≤ (1 : ℝ) / 2 := hhalf

/-- The genuine initial short-completed-stage event on the original tape. -/
def idealInitialShortEvent
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) (m : ℕ) :
    Set ({U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d)) :=
  {z | idealShortCompletedStage hT z.1.1 A r z.2 a m ⟨0, hT⟩}

theorem measurableSet_idealInitialShortEvent
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) (m : ℕ) :
    MeasurableSet (idealInitialShortEvent hT A r a m) := by
  classical
  let F := {U : Fin T → Point d // Orthonormal ℝ U}
  let U : F × (Fin N → Point d) → Fin T → Point d := fun z => z.1.1
  let ξ : F × (Fin N → Point d) → Fin N → Point d := Prod.snd
  have hU : Measurable U := measurable_subtype_coe.comp measurable_fst
  have hξ : Measurable ξ := measurable_snd
  let ℱ := idealStageFiltration hT A r a U ξ hU hξ
  have hs := idealShortStageIndicator_stronglyAdapted hT A r a U ξ hU hξ m
  have hX : Measurable (fun z : F × (Fin N → Point d) =>
      idealShortStageIndicator hT z.1.1 A r z.2 a m 0) :=
    ((hs 0).mono (ℱ.le 0)).measurable
  have hset : MeasurableSet {z : F × (Fin N → Point d) |
      idealShortStageIndicator hT z.1.1 A r z.2 a m 0 = (1 : ℝ)} :=
    measurableSet_eq_fun hX measurable_const
  have heq : idealInitialShortEvent hT A r a m =
      {z : F × (Fin N → Point d) |
        idealShortStageIndicator hT z.1.1 A r z.2 a m 0 = (1 : ℝ)} := by
    ext z
    change idealShortCompletedStage hT z.1.1 A r z.2 a m ⟨0, hT⟩ ↔
      idealShortStageIndicator hT z.1.1 A r z.2 a m 0 = (1 : ℝ)
    simp only [idealShortStageIndicator, dite_eq_left hT]
    by_cases hz : idealShortCompletedStage hT z.1.1 A r z.2 a m ⟨0, hT⟩
    <;> simp [hz]
  rw [heq]
  exact hset

theorem idealInitialShortCompleted_implies_initialFrozenCap
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d))
    (hshort : idealShortCompletedStage hT z.1.1 A r
      (idealExtendedNoiseTake z.2) a m ⟨0, hT⟩) :
    idealInitialFrozenObservable (m := m) hT A r a
      (z.1, idealExtendedNoiseTail 0 (Nat.zero_le N) z.2) ∈
        nextDirectionFinalCapEvent (m := m) hT (emptyRevealedPrefix d) A r
          (idealInitialPreHistory A r) := by
  let j : Fin T := ⟨0, hT⟩
  have hnext : idealStageStart hT z.1.1 A r (idealExtendedNoiseTake z.2) a 1 ≤ N := hshort.1
  have hlen : idealStageStart hT z.1.1 A r (idealExtendedNoiseTake z.2) a 1 ≤ m := by
    simpa [idealStageLength, idealStageStart_zero] using hshort.2
  have hhit := zeroShortStage_implies_frozenCapHit hT z.1.1 A r z.2 a hnext hlen
  rw [idealPreHistoryAtTime_zero_eq_initial] at hhit
  have hfinal := (frozenPrefixCapHitWithin_iff_finalCapHit
    hT z.1.1 j A r (idealInitialPreHistory A r) a
      (idealExtendedNoiseTail 0 (Nat.zero_le N) z.2)).mp hhit
  have hcap := (frozenFinalCapHit_iff_referenceCap (m := m) hT z.1.1 j A r
    (idealInitialPreHistory A r)
    (actualFrozenGaussianSeedState hT z.1.1 j A r (idealInitialPreHistory A r)
      a m (idealExtendedNoiseTail 0 (Nat.zero_le N) z.2))).mp hfinal
  have hp : framePrefix (Nat.le_of_lt j.isLt) z.1.1 = emptyRevealedPrefix d := by
    funext i
    exact i.elim0
  rw [hp] at hcap
  exact hcap

/-- The original-law ordinary initial mean, with no initial probability or
conditional-law premise. Auxiliary coordinates remain analysis variables.
-/
theorem idealInitialShortStage_mean_half_actual_parameters
    {d T N : ℕ} {S : ℝ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hdim : 2 * T ≤ d) (hS : 0 < S)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / (16 * 300 ^ 2)))
    (hdimlog : 21400 * (1 + Real.log (2 * (gatedStageLength d T S : ℝ))) ≤
      (d - T : ℕ))
    (A : RandomAlgorithm d N Private) (r : Private) :
    (∫ z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d),
      idealShortStageIndicator hT z.1.1 A r z.2 ((S / 80) / Real.sqrt d)
        (gatedStageLength d T S) 0
      ∂(preselectedOrthonormalFrameLaw d T (by omega)).prod
        (Measure.pi (fun _ : Fin N => standardGaussianLaw d))) ≤ (1 : ℝ) / 2 := by
  classical
  have hTd : T ≤ d := by omega
  let F := {U : Fin T → Point d // Orthonormal ℝ U}
  let m := gatedStageLength d T S
  let a := (S / 80) / Real.sqrt d
  let μ := preselectedOrthonormalFrameLaw d T hTd
  let P := μ.prod (Measure.pi (fun _ : Fin N => standardGaussianLaw d))
  let Pext := μ.prod (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d))
  let Paux := μ.prod (Measure.pi (fun _ : Fin m => standardGaussianLaw d))
  let H : F × (Fin (N + m) → Point d) → F × (Fin N → Point d) :=
    fun z => (z.1, idealExtendedNoiseTake z.2)
  let L : F × (Fin (N + m) → Point d) → F × (Fin m → Point d) :=
    fun z => (z.1, idealExtendedNoiseTail 0 (Nat.zero_le N) z.2)
  let G := idealInitialFrozenObservable (m := m) hT A r a
  let E := nextDirectionFinalCapEvent (m := m) hT (emptyRevealedPrefix d) A r
    (idealInitialPreHistory A r)
  let W := idealInitialShortEvent hT A r a m
  have hH : Measurable H := measurable_fst.prodMk
    (measurable_idealExtendedNoiseTake.comp measurable_snd)
  have hL : Measurable L := measurable_fst.prodMk
    ((measurable_idealExtendedNoiseTail 0 (Nat.zero_le N)).comp measurable_snd)
  have hG : Measurable G := measurable_idealInitialFrozenObservable hT A r a
  have hE : MeasurableSet E := measurableSet_nextDirectionFinalCapEvent
    hT (emptyRevealedPrefix d) A r (idealInitialPreHistory A r)
  have hW : MeasurableSet W := measurableSet_idealInitialShortEvent hT A r a m
  have hhead : Pext.map H = P := idealExtendedNoiseTake_jointLaw (m := m) μ
  have htail : Pext.map L = Paux := idealExtendedNoiseTail_jointLaw (m := m) μ 0 (Nat.zero_le N)
  have hsubset : H ⁻¹' W ⊆ L ⁻¹' (G ⁻¹' E) := by
    intro z hz
    exact idealInitialShortCompleted_implies_initialFrozenCap hT A r a z hz
  have hprob : P.real W ≤ (1 : ℝ) / 2 := by
    calc
      P.real W = Pext.real (H ⁻¹' W) := by
        rw [← hhead, measureReal_def, measureReal_def, Measure.map_apply hH hW]
      _ ≤ Pext.real (L ⁻¹' (G ⁻¹' E)) := measureReal_mono hsubset
      _ = Paux.real (G ⁻¹' E) := by
        rw [← htail, measureReal_def, measureReal_def,
          Measure.map_apply hL (hE.preimage hG)]
      _ ≤ (1 : ℝ) / 2 := idealInitialFrozenCap_probability_half
        hT hdim hS hlarge hdimlog le_rfl A r
  have hfun : (fun z : F × (Fin N → Point d) =>
      idealShortStageIndicator hT z.1.1 A r z.2 a m 0) =
        W.indicator (fun _ => (1 : ℝ)) := by
    funext z
    simp only [idealShortStageIndicator, dite_eq_left hT, W, idealInitialShortEvent,
      Set.mem_ofPred_eq, Set.indicator_apply]
  change (∫ z, idealShortStageIndicator hT z.1.1 A r z.2 a m 0 ∂P) ≤ (1 : ℝ) / 2
  rw [hfun]
  change (∫ z : F × (Fin N → Point d), W.indicator (1 : F × (Fin N → Point d) → ℝ) z ∂P) ≤
    (1 : ℝ) / 2
  rw [integral_indicator_one hW]
  exact hprob

end

end HeavyTailedNoise
