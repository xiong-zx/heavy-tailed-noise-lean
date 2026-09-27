import HeavyTailedNoise.Lower.Gated.IdealRandomStartSliceLaw

/-!
The never-started `N+1` slice uses an auxiliary Gaussian block after the
algorithm's last permitted response. This block is invisible to the algorithm
and independent of its complete `N`-response transcript.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

lemma idealExtendedNoiseTake_truncate_cap {d N m : ℕ}
    (ξ : Fin (N + m) → Point d) :
    idealExtendedNoiseTake (idealNoiseTruncate N ξ) =
      idealExtendedNoiseTake ξ := by
  rw [idealExtendedNoiseTake_truncate]
  funext i
  simp [idealNoiseTruncate, i.isLt]

theorem idealExtendedNoiseTake_indep_capTail {d N m : ℕ} :
    IndepFun
      (idealExtendedNoiseTake (d := d) (N := N) (m := m))
      (idealExtendedNoiseTail (d := d) (m := m) N le_rfl)
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)) := by
  have hbase := idealExtendedNoiseTruncate_indep_tail
    (d := d) (m := m) N le_rfl
  have hc := hbase.comp measurable_idealExtendedNoiseTake measurable_id
  have hc' : IndepFun
      (fun ξ : Fin (N + m) → Point d =>
        idealExtendedNoiseTake (idealNoiseTruncate N ξ))
      (idealExtendedNoiseTail (d := d) (m := m) N le_rfl)
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)) := by
    simpa only [Function.comp_def, id_eq] using hc
  have heq :
      (fun ξ : Fin (N + m) → Point d =>
        idealExtendedNoiseTake (idealNoiseTruncate N ξ)) =
      idealExtendedNoiseTake := by
    funext ξ
    exact idealExtendedNoiseTake_truncate_cap ξ
  rw [heq] at hc'
  exact hc'

theorem idealStoppedSentinelEvent_indep_tail
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    IndepFun
      (idealStoppedExtendedEventTuple (m := m) hT U k A r a (N + 1))
      (idealExtendedNoiseTail (d := d) (m := m) N le_rfl)
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)) := by
  have hc := (idealExtendedNoiseTake_indep_capTail (d := d) (m := m)).comp
    (measurable_idealStoppedEventTuple hT U k A r a (N + 1))
    measurable_id
  change IndepFun
      (idealStoppedExtendedEventTuple (m := m) hT U k A r a (N + 1))
      (idealExtendedNoiseTail (d := d) (m := m) N le_rfl)
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)) at hc
  exact hc

theorem idealSentinelSlice_measure_inter_tail
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (B : Set (Bool × ℕ × Transcript d N × Point d))
    (C : Set (Fin m → Point d))
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    let μ : Measure (Fin (N + m) → Point d) :=
      Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)
    let R : (Fin (N + m) → Point d) →
        Bool × ℕ × Transcript d N × Point d :=
      fun ξ => idealPreResponseTuple
        (idealStoppedPreHistory hT U k A r (idealExtendedNoiseTake ξ) a)
    μ ({ξ | idealExtendedStageStart hT U k A r a ξ = N + 1 ∧ R ξ ∈ B} ∩
      {ξ | idealExtendedNoiseTail N le_rfl ξ ∈ C}) =
      μ {ξ | idealExtendedStageStart hT U k A r a ξ = N + 1 ∧ R ξ ∈ B} *
        (Measure.pi (fun _ : Fin m => standardGaussianLaw d)) C := by
  dsimp only
  let μ : Measure (Fin (N + m) → Point d) :=
    Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)
  let R : (Fin (N + m) → Point d) →
      Bool × ℕ × Transcript d N × Point d :=
    fun ξ => idealPreResponseTuple
      (idealStoppedPreHistory hT U k A r (idealExtendedNoiseTake ξ) a)
  let E : (Fin (N + m) → Point d) →
      Bool × (Bool × ℕ × Transcript d N × Point d) :=
    idealStoppedExtendedEventTuple hT U k A r a (N + 1)
  let D : Set (Bool × (Bool × ℕ × Transcript d N × Point d)) :=
    {z | z.1 = true ∧ z.2 ∈ B}
  have hD : MeasurableSet D :=
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      (hB.preimage measurable_snd)
  have hpre : E ⁻¹' D =
      {ξ | idealExtendedStageStart hT U k A r a ξ = N + 1 ∧ R ξ ∈ B} := by
    ext ξ
    by_cases ht : idealStageStart hT U A r
        (idealExtendedNoiseTake ξ) a (k.val + 1) = N + 1
    · simp [E, D, R, idealStoppedExtendedEventTuple,
        idealStoppedEventTuple, idealExtendedStageStart, ht]
    · simp [E, D, R, idealStoppedExtendedEventTuple,
        idealStoppedEventTuple, idealExtendedStageStart, ht]
  have hfact := (idealStoppedSentinelEvent_indep_tail
    (m := m) hT U k A r a).measure_inter_preimage_eq_mul
      D C hD hC
  have htail : μ ((idealExtendedNoiseTail N le_rfl) ⁻¹' C) =
      (Measure.pi (fun _ : Fin m => standardGaussianLaw d)) C := by
    have hmap := idealExtendedNoiseTail_law (d := d) (m := m) N le_rfl
    have hc := congrArg
      (fun ν : Measure (Fin m → Point d) => ν C) hmap
    simpa only [μ, Measure.map_apply
      (measurable_idealExtendedNoiseTail N le_rfl) hC] using hc
  rw [hpre, htail] at hfact
  exact hfact

end

end HeavyTailedNoise
