import HeavyTailedNoise.Lower.Gated.IdealShortStageLatestHalf
import HeavyTailedNoise.Lower.Gated.ExtendedGaussianMarginal
import HeavyTailedNoise.Lower.Gated.ActualStageLatestEncoding
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
Positive-stage latest-data half bounds on the original N-coordinate Gaussian
tape.  The extended-source integral test is transferred through the checked
head marginal, then converted to conditional expectation on the short-prefix
and pre-response-tuple comap sigma-algebra.  No test or conditional-law
probability premise is added to the concrete theorem.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory MeasurableSpace

noncomputable section

private theorem indicator_condExp_half_of_comap_tests
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → X) (hD : Measurable D)
    (W : Set Ω) (hW : MeasurableSet W)
    (htest : ∀ B : Set X, MeasurableSet B →
      P.real (W ∩ D ⁻¹' B) ≤ (1 / 2 : ℝ) * P.real (D ⁻¹' B)) :
    ∀ᵐ ω ∂P,
      P[W.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap D inferInstance] ω ≤ (1 / 2 : ℝ) := by
  let m := MeasurableSpace.comap D inferInstance
  have hm : m ≤ mΩ := hD.comap_le
  let f := W.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f P := (integrable_const (1 : ℝ)).indicator hW
  have hCE : StronglyMeasurable[m] (P[f | m]) := stronglyMeasurable_condExp
  have hCEint : Integrable (P[f | m]) (P.trim hm) :=
    integrable_condExp.trim hm hCE
  have horder : (P[f | m]) ≤ᵐ[P.trim hm] (fun _ => (1 / 2 : ℝ)) := by
    apply ae_le_of_forall_setIntegral_le hCEint (integrable_const (1 / 2 : ℝ))
    intro s hs _
    obtain ⟨B, hB, hBs⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [← setIntegral_trim hm hCE hs,
      ← setIntegral_trim hm stronglyMeasurable_const hs,
      setIntegral_condExp hm hf hs]
    change (∫ ω in s, W.indicator (fun _ => (1 : ℝ)) ω ∂P) ≤ _
    rw [setIntegral_indicator hW, setIntegral_const, setIntegral_const,
      smul_eq_mul, smul_eq_mul, mul_one]
    have h := htest B hB
    rw [hBs] at h
    simpa only [Set.inter_comm, mul_comm] using h
  exact ae_le_of_ae_le_trim horder

theorem measurableSet_idealShortCompletedStage_source
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [MeasurableSpace Ω]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) (m : ℕ) (j : Fin T) :
    MeasurableSet {ω | idealShortCompletedStage hT (U ω) A r (ξ ω) a m j} := by
  classical
  have hX : Measurable (fun ω =>
      idealShortStageIndicator hT (U ω) A r (ξ ω) a m j.val) :=
    ((idealShortStageIndicator_stronglyAdapted hT A r a U ξ hU hξ m j.val).measurable).mono
      ((idealStageFiltration hT A r a U ξ hU hξ).le j.val) le_rfl
  have hset : {ω | idealShortCompletedStage hT (U ω) A r (ξ ω) a m j} =
      (fun ω => idealShortStageIndicator hT (U ω) A r (ξ ω) a m j.val) ⁻¹'
        ({1} : Set ℝ) := by
    ext ω
    by_cases h : idealShortCompletedStage hT (U ω) A r (ξ ω) a m j
    · simp [idealShortStageIndicator, j.isLt, h]
    · simp [idealShortStageIndicator, j.isLt, h]
  rw [hset]
  exact (measurableSet_singleton (1 : ℝ)).preimage hX

/-- The verified latest-data integral test on the original N-seed source. -/
theorem idealPositiveShortCompleted_original_latestData_half
    {d T N : ℕ} {S : ℝ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hdim : 2 * T ≤ d) (hS : 0 < S)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / (16 * 300 ^ 2)))
    (hdimlog : 21400 * (1 + Real.log (2 * (gatedStageLength d T S : ℝ))) ≤
      (d - T : ℕ))
    (k : Fin T) (hk : k.val + 1 + 1 ≤ T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (B : Set (IdealLatestPrefixData d T N k)) (hB : MeasurableSet B) :
    let n₀ := gatedStageLength d T S
    let a := (S / 80) / Real.sqrt d
    let j : Fin T := ⟨k.val + 1, by omega⟩
    let P := (preselectedOrthonormalFrameLaw d T (by omega)).prod
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d))
    let D := idealLatestShortPrefixData hT A r a
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d) => z.1.1)
      (Prod.snd : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d) →
        (Fin N → Point d)) k
    P.real {z | idealShortCompletedStage hT z.1.1 A r z.2 a n₀ j ∧ D z ∈ B} ≤
      (1 / 2 : ℝ) * P.real {z | D z ∈ B} := by
  dsimp only
  let n₀ := gatedStageLength d T S
  let a := (S / 80) / Real.sqrt d
  let j : Fin T := ⟨k.val + 1, by omega⟩
  have hTd : T ≤ d := by omega
  let μ := preselectedOrthonormalFrameLaw d T hTd
  let P := μ.prod (Measure.pi (fun _ : Fin N => standardGaussianLaw d))
  let Pe := μ.prod (Measure.pi (fun _ : Fin (N + n₀) => standardGaussianLaw d))
  let D := idealLatestShortPrefixData hT A r a
    (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d) => z.1.1)
    (Prod.snd : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d) →
      (Fin N → Point d)) k
  let W : Set ({U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d)) :=
    {z | idealShortCompletedStage hT z.1.1 A r z.2 a n₀ j}
  let R : ({U : Fin T → Point d // Orthonormal ℝ U} ×
      (Fin (N + n₀) → Point d)) →
      ({U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d)) :=
    fun z => (z.1, idealExtendedNoiseTake z.2)
  have hR : Measurable R :=
    measurable_fst.prodMk (measurable_idealExtendedNoiseTake.comp measurable_snd)
  have hU : Measurable (fun z :
      {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d) => z.1.1) :=
    measurable_subtype_coe.comp measurable_fst
  have hD : Measurable D :=
    measurable_idealLatestShortPrefixData hT A r a _ _ hU measurable_snd k
  have hW : MeasurableSet W :=
    measurableSet_idealShortCompletedStage_source hT A r a _ _ hU measurable_snd n₀ j
  have hlaw : Pe.map R = P := idealExtendedNoiseTake_jointLaw (m := n₀) μ
  have hdata (z) : D (R z) = idealStoppedDirectionData (m := n₀) hT k A r a z := rfl
  have hleft : Pe.real (R ⁻¹' (W ∩ D ⁻¹' B)) = P.real (W ∩ D ⁻¹' B) := by
    rw [← hlaw, measureReal_def, measureReal_def,
      Measure.map_apply hR (hW.inter (hB.preimage hD))]
  have hright : Pe.real (R ⁻¹' (D ⁻¹' B)) = P.real (D ⁻¹' B) := by
    rw [← hlaw, measureReal_def, measureReal_def, Measure.map_apply hR (hB.preimage hD)]
  have ht := idealPositiveShortCompleted_latestData_half
    hT hdim hS hlarge hdimlog k hk A r B hB
  dsimp only at ht
  have heleft : R ⁻¹' (W ∩ D ⁻¹' B) =
      {z | idealShortCompletedStage hT z.1.1 A r
        (idealExtendedNoiseTake z.2) a n₀ j ∧
        idealStoppedDirectionData (m := n₀) hT k A r a z ∈ B} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, W, R, hdata]
  have heright : R ⁻¹' (D ⁻¹' B) =
      {z | idealStoppedDirectionData (m := n₀) hT k A r a z ∈ B} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hdata]
  have hgoalleft :
      {z | idealShortCompletedStage hT z.1.1 A r z.2 a n₀ j ∧ D z ∈ B} =
        W ∩ D ⁻¹' B := by
    ext z
    rfl
  have hgoalright : {z | D z ∈ B} = D ⁻¹' B := rfl
  rw [hgoalleft, hgoalright, ← hleft, ← hright, heleft, heright]
  exact ht

/-- Conditional mean half bound under the latest short-prefix/tuple sigma
on the original Haar × N-seed source, for the genuine next short indicator. -/
theorem idealPositiveStage_latestShortPrefix_condExp_half
    {d T N : ℕ} {S : ℝ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hdim : 2 * T ≤ d) (hS : 0 < S)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / (16 * 300 ^ 2)))
    (hdimlog : 21400 * (1 + Real.log (2 * (gatedStageLength d T S : ℝ))) ≤
      (d - T : ℕ))
    (k : Fin T) (hk : k.val + 1 + 1 ≤ T)
    (A : RandomAlgorithm d N Private) (r : Private) :
    let n₀ := gatedStageLength d T S
    let a := (S / 80) / Real.sqrt d
    let P := (preselectedOrthonormalFrameLaw d T (by omega)).prod
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d))
    let D := idealLatestShortPrefixData hT A r a
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d) => z.1.1)
      (Prod.snd : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d) →
        (Fin N → Point d)) k
    ∀ᵐ z ∂P,
      P[(fun z => idealShortStageIndicator hT z.1.1 A r z.2 a n₀ (k.val + 1)) |
        MeasurableSpace.comap D inferInstance] z ≤ (1 / 2 : ℝ) := by
  classical
  dsimp only
  let n₀ := gatedStageLength d T S
  let a := (S / 80) / Real.sqrt d
  let j : Fin T := ⟨k.val + 1, by omega⟩
  have hTd : T ≤ d := by omega
  let P := (preselectedOrthonormalFrameLaw d T hTd).prod
    (Measure.pi (fun _ : Fin N => standardGaussianLaw d))
  let U := fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d) => z.1.1
  let ξ := (Prod.snd : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d) →
    (Fin N → Point d))
  let D := idealLatestShortPrefixData hT A r a U ξ k
  let W : Set ({U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d)) :=
    {z | idealShortCompletedStage hT z.1.1 A r z.2 a n₀ j}
  have hU : Measurable U := measurable_subtype_coe.comp measurable_fst
  have hD : Measurable D := measurable_idealLatestShortPrefixData hT A r a U ξ hU measurable_snd k
  have hW : MeasurableSet W :=
    measurableSet_idealShortCompletedStage_source hT A r a U ξ hU measurable_snd n₀ j
  have htest : ∀ B : Set (IdealLatestPrefixData d T N k), MeasurableSet B →
      P.real (W ∩ D ⁻¹' B) ≤ (1 / 2 : ℝ) * P.real (D ⁻¹' B) := by
    intro B hB
    have h := idealPositiveShortCompleted_original_latestData_half
      hT hdim hS hlarge hdimlog k hk A r B hB
    have hleft : W ∩ D ⁻¹' B =
        {z | idealShortCompletedStage hT z.1.1 A r z.2 a n₀ j ∧ D z ∈ B} := by
      ext z
      rfl
    have hright : D ⁻¹' B = {z | D z ∈ B} := rfl
    rw [hleft, hright]
    exact h
  have hCE := indicator_condExp_half_of_comap_tests P D hD W hW htest
  have hfun :
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d) =>
        idealShortStageIndicator hT z.1.1 A r z.2 a n₀ (k.val + 1)) =
      W.indicator (fun _ => (1 : ℝ)) := by
    funext z
    by_cases hz : idealShortCompletedStage hT z.1.1 A r z.2 a n₀ j
    · simp [idealShortStageIndicator, show k.val + 1 < T by omega, W, j, hz]
    · simp [idealShortStageIndicator, show k.val + 1 < T by omega, W, j, hz]
  rw [hfun]
  exact hCE

end

end HeavyTailedNoise
