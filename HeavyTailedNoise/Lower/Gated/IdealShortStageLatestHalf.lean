import HeavyTailedNoise.Lower.Gated.IdealStoppedFrozenCondLaw
import HeavyTailedNoise.Lower.Gated.FrozenSnapshotCapProbability
import HeavyTailedNoise.Lower.Gated.LowerBoundCouplingAssembly
import HeavyTailedNoise.Lower.Gated.FrozenCapFinalEventEquivalence

/-!
The actual positive short-completed-stage event has the half bound tested
against every measurable set of the latest revealed-prefix/pre-response
data.  The source is the fixed full-frame prior and extended independent
Gaussian tape.  The concrete stopped conditional law is instantiated, not
assumed.  No cumulative-stage filtration assertion is made here.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

private theorem conditionalKernel_event_test_half
    {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → X) (Z : Ω → Y) (hD : Measurable D)
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (hcond : HasCondDistrib Z D κ P)
    (E : Set (X × Y)) (hE : MeasurableSet E)
    (hhalf : ∀ᵐ x ∂P.map D, κ x ((Prod.mk x) ⁻¹' E) ≤ (1 / 2 : ℝ≥0∞))
    (S : Set Ω) (hS : S ⊆ (fun ω => (D ω, Z ω)) ⁻¹' E)
    (B : Set X) (hB : MeasurableSet B) :
    P (S ∩ D ⁻¹' B) ≤ (1 / 2 : ℝ≥0∞) * P (D ⁻¹' B) := by
  classical
  let F : Set (X × Y) := E ∩ Prod.fst ⁻¹' B
  have hF : MeasurableSet F := hE.inter (hB.preimage measurable_fst)
  have hsubset : S ∩ D ⁻¹' B ⊆ (fun ω => (D ω, Z ω)) ⁻¹' F := by
    intro ω hω
    exact ⟨hS hω.1, hω.2⟩
  have hbound :
      ∫⁻ x, κ x ((Prod.mk x) ⁻¹' F) ∂P.map D ≤
        ∫⁻ x, B.indicator (fun _ => (1 / 2 : ℝ≥0∞)) x ∂P.map D := by
    apply lintegral_mono_ae
    filter_upwards [hhalf] with x hx
    by_cases hxb : x ∈ B
    · have hsection : (Prod.mk x) ⁻¹' F = (Prod.mk x) ⁻¹' E := by
        ext y
        simp [F, hxb]
      simpa [hsection, hxb] using hx
    · have hsection : (Prod.mk x) ⁻¹' F = ∅ := by
        ext y
        simp [F, hxb]
      simp [hsection, hxb]
  calc
    P (S ∩ D ⁻¹' B) ≤ P ((fun ω => (D ω, Z ω)) ⁻¹' F) :=
      measure_mono hsubset
    _ = (P.map (fun ω => (D ω, Z ω))) F :=
      (Measure.map_apply_of_aemeasurable hcond.aemeasurable hF).symm
    _ = ((P.map D) ⊗ₘ κ) F := by rw [hcond.map_eq]
    _ = ∫⁻ x, κ x ((Prod.mk x) ⁻¹' F) ∂P.map D :=
      Measure.compProd_apply hF
    _ ≤ ∫⁻ x, B.indicator (fun _ => (1 / 2 : ℝ≥0∞)) x ∂P.map D := hbound
    _ = (1 / 2 : ℝ≥0∞) * (P.map D) B := by
      rw [lintegral_indicator hB, setLIntegral_const]
    _ = (1 / 2 : ℝ≥0∞) * P (D ⁻¹' B) := by
      rw [Measure.map_apply hD hB]

/-- The same full-frame frozen continuation appearing in the existing
concrete positive-stage conditional-law theorem. -/
def idealPositiveStoppedFrozenOutput
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T) (hk : k.val + 1 + 1 ≤ T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (z : {U : Fin T → Point d // Orthonormal ℝ U} ×
      (Fin (N + m) → Point d)) : Point d × Transcript d N :=
  let j : Fin T := ⟨k.val + 1, by omega⟩
  (z.1.1 j,
    actualFrozenGaussianSeedState hT z.1.1 j A r
      (idealStoppedPreHistory hT z.1.1 k A r
        (idealExtendedNoiseTake z.2) a)
      a m (idealRandomStartTail hT z.1.1 k A r a z.2))

theorem idealPositiveShortCompleted_implies_jointCap
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T) (hk : k.val + 1 + 1 ≤ T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (z : {U : Fin T → Point d // Orthonormal ℝ U} ×
      (Fin (N + m) → Point d))
    (hshort : idealShortCompletedStage hT z.1.1 A r
      (idealExtendedNoiseTake z.2) a m ⟨k.val + 1, by omega⟩) :
    (idealStoppedDirectionData hT k A r a z,
      idealPositiveStoppedFrozenOutput hT k hk A r a z) ∈
      frozenSnapshotFinalCapEvent (m := m) hT ⟨k.val + 1, by omega⟩ A r := by
  let j : Fin T := ⟨k.val + 1, by omega⟩
  let s := idealStoppedPreHistory hT z.1.1 k A r
    (idealExtendedNoiseTake z.2) a
  let ζ := idealRandomStartTail hT z.1.1 k A r a z.2
  have hnext : idealStageStart hT z.1.1 A r
      (idealExtendedNoiseTake z.2) a (j.val + 1) ≤ N := hshort.1
  have hlength : idealStageStart hT z.1.1 A r
      (idealExtendedNoiseTake z.2) a (j.val + 1) -
      idealStageStart hT z.1.1 A r
        (idealExtendedNoiseTake z.2) a (k.val + 1) ≤ m := hshort.2
  have hhit : frozenPrefixCapHitWithin hT z.1.1 j A r s a ζ :=
    positiveShortStage_implies_frozenCapHit hT z.1.1 k j rfl A r z.2 a hnext hlength
  have hfinal := (frozenPrefixCapHitWithin_iff_finalCapHit
    hT z.1.1 j A r s a ζ).mp hhit
  have hreference := (frozenFinalCapHit_iff_referenceCap
    (m := m) hT z.1.1 j A r s
      (actualFrozenGaussianSeedState hT z.1.1 j A r s a m ζ)).mp hfinal
  simpa only [frozenSnapshotFinalCapEvent, nextDirectionFinalCapEvent,
    idealStoppedDirectionData, idealPositiveStoppedFrozenOutput,
    idealPreResponseHistoryOfTuple_tuple, Set.mem_ofPred_eq, j, s, ζ] using hreference

-- Subsequent probability composition uses the checked observable/event
-- interfaces without reducing the underlying algorithm or frozen recursion.
attribute [local irreducible] idealPositiveStoppedFrozenOutput
  idealStoppedDirectionData frozenSnapshotFinalCapEvent

/-- Integral-test half bound for a genuine positive short-completed stage,
conditioned on its latest prefix and full pre-response tuple. -/
theorem idealPositiveShortCompleted_latestData_half
    {d T N : ℕ} {S : ℝ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hdim : 2 * T ≤ d) (hS : 0 < S)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2)))
    (hdimlog : 21400 *
      (1 + Real.log (2 * (gatedStageLength d T S : ℝ))) ≤ (d - T : ℕ))
    (k : Fin T) (hk : k.val + 1 + 1 ≤ T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (B : Set ((Fin (k.val + 1) → Point d) ×
      (Bool × ℕ × Transcript d N × Point d))) (hB : MeasurableSet B) :
    let n₀ := gatedStageLength d T S
    let a := (S / 80) / Real.sqrt d
    let j : Fin T := ⟨k.val + 1, by omega⟩
    let P := (preselectedOrthonormalFrameLaw d T (by omega)).prod
      (Measure.pi (fun _ : Fin (N + n₀) => standardGaussianLaw d))
    let D := idealStoppedDirectionData (m := n₀) hT k A r a
    P.real {z | idealShortCompletedStage hT z.1.1 A r
        (idealExtendedNoiseTake z.2) a n₀ j ∧ D z ∈ B} ≤
      (1 / 2 : ℝ) * P.real {z | D z ∈ B} := by
  dsimp only
  let n₀ := gatedStageLength d T S
  let a := (S / 80) / Real.sqrt d
  let j : Fin T := ⟨k.val + 1, by omega⟩
  have hTd : T ≤ d := by omega
  let P := (preselectedOrthonormalFrameLaw d T hTd).prod
    (Measure.pi (fun _ : Fin (N + n₀) => standardGaussianLaw d))
  let D := idealStoppedDirectionData (m := n₀) hT k A r a
  let Z := idealPositiveStoppedFrozenOutput (m := n₀) hT k hk A r a
  let κ := frozenSnapshotPairKernel (m := n₀) hT j A r a
  haveI : IsMarkovKernel κ :=
    frozenSnapshotPairKernel_markov (m := n₀) hT j A r a
  let E := frozenSnapshotFinalCapEvent (m := n₀) hT j A r
  let W : Set ({U : Fin T → Point d // Orthonormal ℝ U} ×
      (Fin (N + n₀) → Point d)) :=
    {z | idealShortCompletedStage hT z.1.1 A r
      (idealExtendedNoiseTake z.2) a n₀ j}
  have hD : Measurable D := measurable_idealStoppedDirectionData hT k A r a
  have hcond : HasCondDistrib Z D κ P := by
    unfold Z idealPositiveStoppedFrozenOutput κ P
    exact idealStopped_actualFrozen_hasCondDistrib (m := n₀) hT hTd k hk A r a
  have hE : MeasurableSet E := measurableSet_frozenSnapshotFinalCapEvent hT j A r
  have hvalidSet : MeasurableSet {p : (Fin (k.val + 1) → Point d) ×
      (Bool × ℕ × Transcript d N × Point d) | Orthonormal ℝ p.1} :=
    (measurableSet_orthonormal_fin d (k.val + 1)).preimage measurable_fst
  have hvalid : ∀ᵐ p ∂P.map D, Orthonormal ℝ p.1 := by
    apply (ae_map_iff hD.aemeasurable hvalidSet).mpr
    apply Filter.Eventually.of_forall
    intro z
    unfold D idealStoppedDirectionData
    exact orthonormal_framePrefix z.1.1 z.1.2 (Nat.succ_le_iff.mpr k.isLt)
  have hhalf : ∀ᵐ p ∂P.map D,
      κ p ((Prod.mk p) ⁻¹' E) ≤ (1 / 2 : ℝ≥0∞) := by
    filter_upwards [hvalid] with p hp
    have h := frozenSnapshotPairKernel_cap_probability_half_actual_parameters
      (m := n₀) hT hdim hS hlarge hdimlog le_rfl j A r p hp
    apply (ENNReal.toReal_le_toReal
      (measure_ne_top (κ p) ((Prod.mk p) ⁻¹' E)) (by norm_num)).mp
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  have hW : W ⊆ (fun z => (D z, Z z)) ⁻¹' E := by
    intro z hz
    exact idealPositiveShortCompleted_implies_jointCap hT k hk A r a z hz
  have htest := conditionalKernel_event_test_half P D Z hD κ hcond E hE hhalf W hW B hB
  have hne : (1 / 2 : ℝ≥0∞) * P (D ⁻¹' B) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (measure_ne_top P (D ⁻¹' B))
  have hreal := ENNReal.toReal_mono hne htest
  have hleft : W ∩ D ⁻¹' B =
      {z | idealShortCompletedStage hT z.1.1 A r
        (idealExtendedNoiseTake z.2) a n₀ j ∧ D z ∈ B} := by
    ext z
    rfl
  have hright : D ⁻¹' B = {z | D z ∈ B} := rfl
  rw [hleft, hright] at hreal
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_ofPred_eq, W, P, D, n₀, a, j] using hreal

end

end HeavyTailedNoise
