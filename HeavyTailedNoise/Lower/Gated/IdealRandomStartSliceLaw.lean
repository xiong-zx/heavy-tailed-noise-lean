import HeavyTailedNoise.Lower.Gated.IdealRandomStartPartition

/-!
Event-probability form of one responsive stage-start slice. The tagged
fixed-time product law gives the exact probability factorization needed to
sum over the random bounded start time.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem idealStartSlice_measure_inter_tail
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (t : ℕ) (htN : t ≤ N)
    (B : Set (Bool × ℕ × Transcript d N × Point d))
    (C : Set (Fin m → Point d))
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    let μ : Measure (Fin (N + m) → Point d) :=
      Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)
    let R : (Fin (N + m) → Point d) →
        Bool × ℕ × Transcript d N × Point d :=
      fun ξ => idealPreResponseTuple
        (idealStoppedPreHistory hT U k A r (idealExtendedNoiseTake ξ) a)
    μ ({ξ | idealExtendedStageStart hT U k A r a ξ = t ∧ R ξ ∈ B} ∩
      {ξ | idealExtendedNoiseTail t htN ξ ∈ C}) =
      μ {ξ | idealExtendedStageStart hT U k A r a ξ = t ∧ R ξ ∈ B} *
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
    idealStoppedExtendedEventTuple hT U k A r a t
  let D : Set (Bool × (Bool × ℕ × Transcript d N × Point d)) :=
    {z | z.1 = true ∧ z.2 ∈ B}
  have hD : MeasurableSet D :=
    (measurableSet_eq_fun measurable_fst measurable_const).inter
      (hB.preimage measurable_snd)
  have hpre : E ⁻¹' D =
      {ξ | idealExtendedStageStart hT U k A r a ξ = t ∧ R ξ ∈ B} := by
    ext ξ
    by_cases ht : idealStageStart hT U A r
        (idealExtendedNoiseTake ξ) a (k.val + 1) = t
    · simp [E, D, R, idealStoppedExtendedEventTuple,
        idealStoppedEventTuple, idealExtendedStageStart, ht]
    · simp [E, D, R, idealStoppedExtendedEventTuple,
        idealStoppedEventTuple, idealExtendedStageStart, ht]
  have hind := idealStoppedExtendedEventTuple_indep_tail
    (m := m) hT U k A r a t htN
  have hfact := hind.measure_inter_preimage_eq_mul D C hD hC
  have htail : μ ((idealExtendedNoiseTail t htN) ⁻¹' C) =
      (Measure.pi (fun _ : Fin m => standardGaussianLaw d)) C := by
    have hmap := idealExtendedNoiseTail_law (d := d) (m := m) t htN
    have hc := congrArg
      (fun ν : Measure (Fin m → Point d) => ν C) hmap
    simpa only [μ, Measure.map_apply
      (measurable_idealExtendedNoiseTail t htN) hC] using hc
  rw [hpre, htail] at hfact
  exact hfact

end

end HeavyTailedNoise
