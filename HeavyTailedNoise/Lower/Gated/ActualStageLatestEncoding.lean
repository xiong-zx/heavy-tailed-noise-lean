import HeavyTailedNoise.Lower.Gated.ActualStageSigmaTrace
import HeavyTailedNoise.Lower.Gated.IdealStoppedDirectionTailLaw

/-!
The latest observation and the latest-law short-prefix conditioning data
generate the same source sigma-algebra.  Extraction and embedding are
measurable, and their compositions agree on actual source observations.
The generic source permits either the original noise tape or a measurable
restriction of an extended tape.  No assumption on Private beyond its
measurable space is introduced.

On a never-started latest record, the genuine next completed-short-stage
indicator is exactly zero.  These are deterministic interfaces for the
separate conditional-half localization and latest integral test.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory MeasurableSpace

noncomputable section

set_option autoImplicit false

abbrev IdealLatestPrefixData (d T N : ℕ) (k : Fin T) :=
  (Fin (k.val + 1) → Point d) × (Bool × ℕ × Transcript d N × Point d)

def extractLatestPrefixData {d T N : ℕ} (k : Fin T)
    (z : IdealStageAnalysisData d T N) : IdealLatestPrefixData d T N k :=
  (framePrefix (Nat.succ_le_iff.mpr k.isLt) z.1, z.2)

def embedLatestPrefixData {d T N : ℕ} (k : Fin T)
    (z : IdealLatestPrefixData d T N k) : IdealStageAnalysisData d T N :=
  (idealPrefixExtension k z.1, z.2)

theorem measurable_extractLatestPrefixData {d T N : ℕ} (k : Fin T) :
    Measurable (extractLatestPrefixData (d := d) (N := N) k) :=
  ((measurable_framePrefix (Nat.succ_le_iff.mpr k.isLt)).comp measurable_fst).prodMk measurable_snd

theorem measurable_embedLatestPrefixData {d T N : ℕ} (k : Fin T) :
    Measurable (embedLatestPrefixData (d := d) (N := N) k) :=
  ((measurable_idealPrefixExtension k).comp measurable_fst).prodMk measurable_snd

theorem framePrefix_prefixFrame_latest {d T : ℕ} (U : Fin T → Point d) (k : Fin T) :
    framePrefix (Nat.succ_le_iff.mpr k.isLt) (prefixFrame U k) =
      framePrefix (Nat.succ_le_iff.mpr k.isLt) U := by
  classical
  funext i
  have hi : (i.castLE (Nat.succ_le_iff.mpr k.isLt) : Fin T) ≤ k := by
    change i.val ≤ k.val
    omega
  simp only [framePrefix, prefixFrame, ite_eq_left hi]

theorem prefixFrame_eq_latestPrefixExtension {d T : ℕ}
    (U : Fin T → Point d) (k : Fin T) :
    prefixFrame U k = idealPrefixExtension k
      (framePrefix (Nat.succ_le_iff.mpr k.isLt) U) := by
  classical
  funext i
  by_cases hi : i ≤ k
  · simpa only [prefixFrame, ite_eq_left hi] using idealPrefixExtension_agree U k i hi
  · have hlt : ¬ i.val < k.val + 1 := by
      change ¬ i.val ≤ k.val at hi
      omega
    simp only [prefixFrame, ite_eq_right hi, idealPrefixExtension, dite_eq_right hlt]

def idealLatestShortPrefixData
    {d T N : ℕ} {Private Ω : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d) (k : Fin T)
    (ω : Ω) : IdealLatestPrefixData d T N k :=
  (framePrefix (Nat.succ_le_iff.mpr k.isLt) (U ω),
    idealPreResponseTuple (idealStoppedPreHistory hT (U ω) k A r (ξ ω) a))

theorem extractLatestPrefixData_eq_actual_short
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (ξ : Fin N → Point d) (a : ℝ) :
    extractLatestPrefixData k (idealStageObservation hT U A r ξ a k.val) =
      (framePrefix (Nat.succ_le_iff.mpr k.isLt) U,
        idealPreResponseTuple (idealStoppedPreHistory hT U k A r ξ a)) := by
  have hi : idealPrefixIndex hT k.val = k := by
    apply Fin.ext
    simp only [idealPrefixIndex]
    omega
  simp only [extractLatestPrefixData, idealStageObservation, hi, framePrefix_prefixFrame_latest]

theorem embedLatestPrefixData_eq_actual_observation
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (ξ : Fin N → Point d) (a : ℝ) :
    embedLatestPrefixData k
      (framePrefix (Nat.succ_le_iff.mpr k.isLt) U,
        idealPreResponseTuple (idealStoppedPreHistory hT U k A r ξ a)) =
      idealStageObservation hT U A r ξ a k.val := by
  have hi : idealPrefixIndex hT k.val = k := by
    apply Fin.ext
    simp only [idealPrefixIndex]
    omega
  simp only [embedLatestPrefixData, idealStageObservation, hi, prefixFrame_eq_latestPrefixExtension]

theorem measurable_idealLatestShortPrefixData
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [MeasurableSpace Ω]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d)
    (hU : Measurable U) (hξ : Measurable ξ) (k : Fin T) :
    Measurable (idealLatestShortPrefixData hT A r a U ξ k) := by
  have hm := (measurable_extractLatestPrefixData k).comp
    (measurable_idealStageObservation hT A r a U ξ hU hξ k.val)
  have heq : idealLatestShortPrefixData hT A r a U ξ k =
      extractLatestPrefixData k ∘ (fun ω => idealStageObservation hT (U ω) A r (ξ ω) a k.val) := by
    funext ω
    exact (extractLatestPrefixData_eq_actual_short hT (U ω) k A r (ξ ω) a).symm
  rw [heq]
  exact hm

/-- Exact equality with the sigma-algebra used by the short-prefix latest
conditional law.  The statement is independent of any probability measure. -/
theorem idealLatestObservationSigma_eq_shortPrefixData
    {d T N : ℕ} {Private Ω : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (U : Ω → Fin T → Point d) (ξ : Ω → Fin N → Point d) (k : Fin T) :
    idealLatestObservationSigma hT A r a U ξ k =
      MeasurableSpace.comap (idealLatestShortPrefixData hT A r a U ξ k) inferInstance := by
  have hemb : (fun ω => idealStageObservation hT (U ω) A r (ξ ω) a k.val) =
      embedLatestPrefixData k ∘ idealLatestShortPrefixData hT A r a U ξ k := by
    funext ω
    exact (embedLatestPrefixData_eq_actual_observation hT (U ω) k A r (ξ ω) a).symm
  have hext : idealLatestShortPrefixData hT A r a U ξ k =
      extractLatestPrefixData k ∘ (fun ω => idealStageObservation hT (U ω) A r (ξ ω) a k.val) := by
    funext ω
    exact (extractLatestPrefixData_eq_actual_short hT (U ω) k A r (ξ ω) a).symm
  apply le_antisymm
  · exact MeasurableSpace.comap_le_comap_of_eq_comp (embedLatestPrefixData k)
      (measurable_embedLatestPrefixData k) hemb
  · exact MeasurableSpace.comap_le_comap_of_eq_comp (extractLatestPrefixData k)
      (measurable_extractLatestPrefixData k) hext

theorem idealLatestShortPrefixData_eq_stoppedDirectionData
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T) (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    idealLatestShortPrefixData hT A r a
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => z.1.1)
      (fun z => idealExtendedNoiseTake z.2) k = idealStoppedDirectionData hT k A r a := rfl

theorem idealNextShortStageIndicator_eq_zero_of_latest_never_started
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T) (hk : k.val + 1 < T)
    (A : RandomAlgorithm d N Private) (r : Private) (ξ : Fin N → Point d) (a : ℝ) (m : ℕ)
    (hs : (idealStoppedPreHistory hT U k A r ξ a).started = false) :
    idealShortStageIndicator hT U A r ξ a m (k.val + 1) = 0 := by
  classical
  have hcur : ¬ idealStageStart hT U A r ξ a (k.val + 1) ≤ N := by
    intro hh
    rw [idealStoppedPreHistory_eq_started_record hT U k A r ξ a hh] at hs
    cases hs
  have hnxt : ¬ idealStageStart hT U A r ξ a ((k.val + 1) + 1) ≤ N := by
    intro hh
    exact hcur ((idealStageStart_mono_target hT U A r ξ a
      (k.val + 1) ((k.val + 1) + 1) (Nat.le_succ _)).trans hh)
  have hshort : ¬ idealShortCompletedStage hT U A r ξ a m ⟨k.val + 1, hk⟩ :=
    fun hh => hnxt hh.1
  simp only [idealShortStageIndicator, dite_eq_left hk, ite_eq_right hshort]

end

end HeavyTailedNoise
