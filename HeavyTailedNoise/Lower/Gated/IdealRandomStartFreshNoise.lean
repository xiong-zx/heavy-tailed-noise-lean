import HeavyTailedNoise.Probability.FiniteSliceIndependence
import HeavyTailedNoise.Lower.Gated.IdealSentinelSliceLaw

/-!
Fresh Gaussian noise after the actual bounded random stage-start time. The
algorithm still sees only its original `N` responses. This theorem is for a
fixed frame and private tape; the full Haar/private mixture is later.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem idealRandomStartTail_indep_and_law
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    IndepFun
      (fun ξ : Fin (N + m) → Point d =>
        idealPreResponseTuple
          (idealStoppedPreHistory hT U k A r
            (idealExtendedNoiseTake ξ) a))
      (idealRandomStartTail hT U k A r a)
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)) ∧
    (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).map
      (idealRandomStartTail hT U k A r a) =
        Measure.pi (fun _ : Fin m => standardGaussianLaw d) := by
  let μ : Measure (Fin (N + m) → Point d) :=
    Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)
  let ν : Measure (Fin m → Point d) :=
    Measure.pi (fun _ : Fin m => standardGaussianLaw d)
  let τ : (Fin (N + m) → Point d) → ℕ :=
    idealExtendedStageStart hT U k A r a
  let R : (Fin (N + m) → Point d) →
      Bool × ℕ × Transcript d N × Point d :=
    fun ξ => idealPreResponseTuple
      (idealStoppedPreHistory hT U k A r (idealExtendedNoiseTake ξ) a)
  let Z : (Fin (N + m) → Point d) → (Fin m → Point d) :=
    idealRandomStartTail hT U k A r a
  have hR : Measurable R :=
    (measurable_idealStoppedPreTuple_fixed hT U k A r a).comp
      measurable_idealExtendedNoiseTake
  have hZ : Measurable Z := measurable_idealRandomStartTail hT U k A r a
  have hτ : Measurable τ := measurable_idealExtendedStageStart hT U k A r a
  have hbound (ξ : Fin (N + m) → Point d) : τ ξ < N + 2 := by
    have hb := idealStageStart_le_succ hT U A r
      (idealExtendedNoiseTake ξ) a (k.val + 1)
    dsimp [τ, idealExtendedStageStart]
    omega
  have hslice (t : Fin (N + 2))
      (B : Set (Bool × ℕ × Transcript d N × Point d))
      (C : Set (Fin m → Point d))
      (hB : MeasurableSet B) (hC : MeasurableSet C) :
      (μ.restrict {ξ | τ ξ = t.val})
          (R ⁻¹' B ∩ Z ⁻¹' C) =
        (μ.restrict {ξ | τ ξ = t.val}) (R ⁻¹' B) * ν C := by
    have hRB : MeasurableSet (R ⁻¹' B) := hB.preimage hR
    have hZC : MeasurableSet (Z ⁻¹' C) := hC.preimage hZ
    rw [Measure.restrict_apply (hRB.inter hZC),
      Measure.restrict_apply hRB]
    by_cases htN : t.val ≤ N
    · have hleft :
          (R ⁻¹' B ∩ Z ⁻¹' C) ∩ {ξ | τ ξ = t.val} =
          {ξ | τ ξ = t.val ∧ R ξ ∈ B} ∩
            {ξ | idealExtendedNoiseTail t.val htN ξ ∈ C} := by
        ext ξ
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨hrec, htail⟩, hstart⟩
          have hz := idealRandomStartTail_on_start
            hT U k A r a htN ξ hstart
          exact ⟨⟨hstart, hrec⟩, by simpa [Z, hz] using htail⟩
        · rintro ⟨⟨hstart, hrec⟩, htail⟩
          have hz := idealRandomStartTail_on_start
            hT U k A r a htN ξ hstart
          exact ⟨⟨hrec, by simpa [Z, hz] using htail⟩, hstart⟩
      have hright : (R ⁻¹' B) ∩ {ξ | τ ξ = t.val} =
          {ξ | τ ξ = t.val ∧ R ξ ∈ B} := by
        ext ξ
        simp [and_comm]
      rw [hleft, hright]
      exact idealStartSlice_measure_inter_tail
        hT U k A r a t.val htN B C hB hC
    · have ht : t.val = N + 1 := by omega
      have hleft :
          (R ⁻¹' B ∩ Z ⁻¹' C) ∩ {ξ | τ ξ = t.val} =
          {ξ | τ ξ = N + 1 ∧ R ξ ∈ B} ∩
            {ξ | idealExtendedNoiseTail N le_rfl ξ ∈ C} := by
        ext ξ
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨hrec, htail⟩, hstart⟩
          have hsent : τ ξ = N + 1 := by omega
          have hz := idealRandomStartTail_never_started
            hT U k A r a ξ hsent
          exact ⟨⟨hsent, hrec⟩, by simpa [Z, hz] using htail⟩
        · rintro ⟨⟨hstart, hrec⟩, htail⟩
          have hz := idealRandomStartTail_never_started
            hT U k A r a ξ hstart
          exact ⟨⟨hrec, by simpa [Z, hz] using htail⟩, by omega⟩
      have hright : (R ⁻¹' B) ∩ {ξ | τ ξ = t.val} =
          {ξ | τ ξ = N + 1 ∧ R ξ ∈ B} := by
        ext ξ
        simp [ht, and_comm]
      rw [hleft, hright]
      exact idealSentinelSlice_measure_inter_tail
        hT U k A r a B C hB hC
  exact indepFun_and_tailLaw_of_bounded_nat_fiber_factors μ ν N τ hτ hbound
    R Z hR hZ hslice

theorem idealRandomStartTail_indep_stoppedPreTuple
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    IndepFun
      (fun ξ : Fin (N + m) → Point d =>
        idealPreResponseTuple
          (idealStoppedPreHistory hT U k A r
            (idealExtendedNoiseTake ξ) a))
      (idealRandomStartTail hT U k A r a)
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)) :=
  (idealRandomStartTail_indep_and_law hT U k A r a).1

theorem idealRandomStartTail_law
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).map
      (idealRandomStartTail hT U k A r a) =
        Measure.pi (fun _ : Fin m => standardGaussianLaw d) :=
  (idealRandomStartTail_indep_and_law hT U k A r a).2

theorem idealRandomStart_record_tail_jointLaw
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).map
      (fun ξ : Fin (N + m) → Point d =>
        (idealPreResponseTuple
          (idealStoppedPreHistory hT U k A r
            (idealExtendedNoiseTake ξ) a),
          idealRandomStartTail hT U k A r a ξ)) =
      ((Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).map
        (fun ξ : Fin (N + m) → Point d =>
          idealPreResponseTuple
            (idealStoppedPreHistory hT U k A r
              (idealExtendedNoiseTake ξ) a))).prod
          (Measure.pi (fun _ : Fin m => standardGaussianLaw d)) := by
  have hrecord := (measurable_idealStoppedPreTuple_fixed hT U k A r a).comp
    (measurable_idealExtendedNoiseTake (d := d) (N := N) (m := m))
  have htail := measurable_idealRandomStartTail (m := m) hT U k A r a
  have hprod := (idealRandomStartTail_indep_stoppedPreTuple
    (m := m) hT U k A r a).map_prod_eq_prod_map_map
      hrecord.aemeasurable htail.aemeasurable
  rw [idealRandomStartTail_law hT U k A r a] at hprod
  exact hprod

end

end HeavyTailedNoise
