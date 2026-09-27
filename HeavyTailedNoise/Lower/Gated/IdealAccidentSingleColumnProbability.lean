import HeavyTailedNoise.Lower.Gated.IdealFutureAccidentBound
import HeavyTailedNoise.Lower.Gated.FrozenHaarReferenceCap

/-!
Conditional next-column integration for the ideal accident event. The only
undischarged analytic input is joint measurability of the projected masked
factor, explicitly supplied as a theorem parameter. No suffix conditional law
is assumed. Private randomness is fixed outside the Haar/noise experiment;
its measurable space is arbitrary.

The existing sharp coordinate-cap theorem needs
`4096 R² ≤ d-T`. This hypothesis is explicit and implies its per-column
requirement `4096 R² ≤ d-i-1`. The finite union runs over `N+1` decisions,
including the response-free output, and `T` columns only.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The actual next-column law, conditioned on the earlier prefix and an
independent complete tape, controls every jointly measurable bounded query
factor. The tape space need not be standard Borel. -/
theorem preselectedHaar_prefix_coordinate_probability_bound
    {d T : ℕ} {Tape : Type*} [MeasurableSpace Tape]
    (hTd : T ≤ d) (k : Fin T) (hk : k.val + 1 + 1 ≤ T)
    (ν : Measure Tape) [IsProbabilityMeasure ν]
    (q : (Fin (k.val + 1) → Point d) × Tape → Point d)
    (hq : Measurable q) {R : ℝ} (hR : 1 ≤ R)
    (hqnorm : ∀ p, ‖q p‖ ≤ R)
    (hDim : 4096 * R ^ 2 ≤ ((d - T : ℕ) : ℝ)) :
    ((preselectedOrthonormalFrameLaw d T hTd).prod ν)
      {z : {U : Fin T → Point d // Orthonormal ℝ U} × Tape |
        (1 / 32 : ℝ) ≤ |inner ℝ
          (q (framePrefix (Nat.succ_le_iff.mpr k.isLt) z.1.1, z.2))
          ((framePrefix hk z.1.1) (Fin.last (k.val + 1)))|} ≤
      ENNReal.ofReal (2 * Real.exp (-((d - T : ℕ) : ℝ) / (2048 * R ^ 2))) := by
  let F := {U : Fin T → Point d // Orthonormal ℝ U}
  let V := Fin (k.val + 1) → Point d
  let μ := preselectedOrthonormalFrameLaw d T hTd
  let P := μ.prod ν
  let X : F × Tape → V × Tape := fun z =>
    (framePrefix (Nat.succ_le_iff.mpr k.isLt) z.1.1, z.2)
  let D : F × Tape → Point d := fun z =>
    (framePrefix hk z.1.1) (Fin.last (k.val + 1))
  let κ : Kernel (V × Tape) (Point d) :=
    (frameNextKernel d (k.val + 1)).comap Prod.fst measurable_fst
  have hX : Measurable X :=
    (((measurable_framePrefix (Nat.succ_le_iff.mpr k.isLt)).comp
      measurable_subtype_coe).comp measurable_fst).prodMk measurable_snd
  have hD : Measurable D :=
    (((measurable_pi_apply (Fin.last (k.val + 1))).comp
      (measurable_framePrefix hk)).comp measurable_subtype_coe).comp measurable_fst
  have hInd : (Prod.fst : F × Tape → F) ⟂ᵢ[P] (Prod.snd : F × Tape → Tape) :=
    indepFun_prod measurable_id measurable_id
  have hLaw : P.map (Prod.fst : F × Tape → F) = μ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hcond : HasCondDistrib D X κ P := by
    have hc := preselectedOrthonormalFrameLaw_column_independent_history
      P d (k.val + 1) T hTd hk
      (Prod.fst : F × Tape → F) (Prod.snd : F × Tape → Tape)
      measurable_fst measurable_snd hInd hLaw
      (Prod.snd : V × Tape → Tape) measurable_snd
    simpa only [init_framePrefix_eq, X, D, κ] using hc
  let E : Set ((V × Tape) × Point d) :=
    {p | (1 / 32 : ℝ) ≤ |inner ℝ (q p.1) p.2|}
  have hE : MeasurableSet E := by
    have hqfst : Measurable (fun p : (V × Tape) × Point d => q p.1) :=
      hq.comp measurable_fst
    exact measurableSet_le measurable_const (by fun_prop)
  let G : F × Tape → (V × Tape) × Point d := fun z => (X z, D z)
  have hG : Measurable G := hX.prodMk hD
  have hsection : Measurable (fun p : V × Tape => κ p (Prod.mk p ⁻¹' E)) :=
    Kernel.measurable_kernel_prodMk_left hE
  let b : ℝ := 2 * Real.exp (-((d - T : ℕ) : ℝ) / (2048 * R ^ 2))
  change P (G ⁻¹' E) ≤ ENNReal.ofReal b
  calc
    P (G ⁻¹' E) = (P.map G) E := (Measure.map_apply hG hE).symm
    _ = ((P.map X) ⊗ₘ κ) E := by rw [hcond.map_eq]
    _ = ∫⁻ p, κ p (Prod.mk p ⁻¹' E) ∂P.map X := Measure.compProd_apply hE
    _ = ∫⁻ z, κ (X z) (Prod.mk (X z) ⁻¹' E) ∂P :=
      lintegral_map hsection hX
    _ ≤ ∫⁻ _ : F × Tape, ENNReal.ofReal b ∂P := by
      apply lintegral_mono
      intro z
      let v := framePrefix (Nat.succ_le_iff.mpr k.isLt) z.1.1
      have hv : Orthonormal ℝ v :=
        orthonormal_framePrefix z.1.1 z.1.2 (Nat.succ_le_iff.mpr k.isLt)
      have hjd : k.val + 1 < d := by omega
      have hres : ((d - T : ℕ) : ℝ) ≤ ((d - (k.val + 1) - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show d - T ≤ d - (k.val + 1) - 1 by omega)
      have hcap := frameNextKernel_small_coordinate_bound hjd v hv hR
        (hDim.trans hres) (q (X z)) (hqnorm (X z))
      have hdimR : ((d - T : ℕ) : ℝ) ≤ ((d - (k.val + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show d - T ≤ d - (k.val + 1) by omega)
      have hRpos : 0 < R := by linarith
      have hexp : -((d - (k.val + 1) : ℕ) : ℝ) / (2048 * R ^ 2) ≤
          -((d - T : ℕ) : ℝ) / (2048 * R ^ 2) :=
        div_le_div_of_nonneg_right (neg_le_neg hdimR) (by positivity)
      have hbound := hcap.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)))
      simpa only [κ, Kernel.comap_apply, E, X, v, b, Set.preimage,
        Set.mem_ofPred_eq] using hbound
    _ = ENNReal.ofReal b := by
      rw [lintegral_const, measure_univ, mul_one]

abbrev IdealAccidentSample (d T N : ℕ) :=
  {U : Fin T → Point d // Orthonormal ℝ U} × (Fin N → Point d)

/-- The existing masked factor followed by the original soft projection. -/
def idealFutureProjectedFactor
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T) (A : RandomAlgorithm d N Private)
    (r : Private) (a : ℝ) (t : ℕ) :
    (Fin (k.val + 1) → Point d) × (Fin N → Point d) → Point d :=
  fun p => softProjection (hardRadius T)
    (idealPrefixMaskedQueryFromPrefix hT k A r p.2 a t p.1)

/-- One actual future-column event before any response at the decision. -/
def idealFutureCoordinateEvent
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private)
    (r : Private) (a : ℝ) (t : ℕ) (i : Fin T) : Set (IdealAccidentSample d T N) :=
  {z | (idealStateAt hT z.1.1 A r z.2 a t).stage < i.val ∧
    (1 / 32 : ℝ) ≤ |frameCoordinates z.1.1
      (softProjection (hardRadius T) (idealDecisionAt hT z.1.1 A r z.2 a t)) i|}

/-- Single-column accident control in the actual Haar and independent Gaussian
tape experiment. Measurability is the sole unproved factor-map input. -/
theorem idealFutureCoordinate_probability_bound
    {d T N t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hTd : T ≤ d)
    (hDim : 4096 * (hardRadius T) ^ 2 ≤ ((d - T : ℕ) : ℝ))
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (i : Fin T) (hi : 0 < i.val) (htN : t ≤ N)
    (hFactorMeas : Measurable
      (idealFutureProjectedFactor hT (idealFuturePredecessor i hi) A r a t)) :
    (((preselectedOrthonormalFrameLaw d T hTd).prod
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d))).real
      (idealFutureCoordinateEvent hT A r a t i)) ≤
      2 * Real.exp (-((d - T : ℕ) : ℝ) / (2048 * (hardRadius T) ^ 2)) := by
  let k := idealFuturePredecessor i hi
  have hik : i.val = k.val + 1 := by dsimp [k, idealFuturePredecessor]; omega
  have hk : k.val + 1 + 1 ≤ T := by have hiT := i.isLt; omega
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast Nat.succ_le_of_lt hT
  have hsqrt : 1 ≤ Real.sqrt T := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
    nlinarith [Real.sqrt_nonneg (T : ℝ)]
  have hR : 1 ≤ hardRadius T := by unfold hardRadius; nlinarith
  have hnorm : ∀ p, ‖idealFutureProjectedFactor hT k A r a t p‖ ≤ hardRadius T := by
    intro p
    exact (norm_projected_idealPrefixMaskedQueryFromPrefix_lt_radius
      hT k A r p.2 a t p.1).le
  have h := preselectedHaar_prefix_coordinate_probability_bound
    hTd k hk (Measure.pi (fun _ : Fin N => standardGaussianLaw d))
    (idealFutureProjectedFactor hT k A r a t) hFactorMeas hR hnorm hDim
  have hcolumn (U : Fin T → Point d) :
      (framePrefix hk U) (Fin.last (k.val + 1)) = U i := by
    apply congrArg U
    apply Fin.ext
    exact hik.symm
  have hevent :
      {z : IdealAccidentSample d T N |
        (1 / 32 : ℝ) ≤ |inner ℝ
          (idealFutureProjectedFactor hT k A r a t
            (framePrefix (Nat.succ_le_iff.mpr k.isLt) z.1.1, z.2))
          ((framePrefix hk z.1.1) (Fin.last (k.val + 1)))|} =
        idealFutureCoordinateEvent hT A r a t i := by
    ext z
    simp only [Set.mem_ofPred_eq, idealFutureCoordinateEvent]
    rw [hcolumn]
    exact (idealFutureCoordinate_event_iff_prefix_masked hT z.1.1 k i hik
      A r z.2 a htN).symm
  rw [hevent] at h
  have hb : 0 ≤ 2 * Real.exp (-((d - T : ℕ) : ℝ) / (2048 * (hardRadius T) ^ 2)) :=
    by positivity
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [measureReal_def, ENNReal.toReal_ofReal hb] using hr

/-- The complete ideal prefix accident event is a union over future columns,
without another union over stage values. This identity also covers saturation.
-/
theorem idealPrefixAccidentAt_iff_exists_futureCoordinate
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private)
    (r : Private) (a : ℝ) (t : ℕ) (z : IdealAccidentSample d T N) :
    idealPrefixAccidentAt hT z.1.1 A r z.2 a t ↔
      ∃ i, z ∈ idealFutureCoordinateEvent hT A r a t i := by
  change (∃ i, idealPrefixIndex hT (idealStateAt hT z.1.1 A r z.2 a t).stage < i ∧
      (1 / 32 : ℝ) ≤ |frameCoordinates z.1.1
        (softProjection (hardRadius T) (idealDecisionAt hT z.1.1 A r z.2 a t)) i|) ↔ _
  constructor
  · rintro ⟨i, hfuture, hcoord⟩
    have hiT := i.isLt
    change min (idealStateAt hT z.1.1 A r z.2 a t).stage (T - 1) < i.val at hfuture
    exact ⟨i, by change _ ∧ _; exact ⟨by omega, hcoord⟩⟩
  · rintro ⟨i, hs, hcoord⟩
    refine ⟨i, ?_, hcoord⟩
    change min (idealStateAt hT z.1.1 A r z.2 a t).stage (T - 1) < i.val
    omega

/-- The frozen full-horizon accident bound, conditional only on the displayed
factor measurability and sharp-cap dimension hypotheses. The `N+1` decisions
include the unqueried final output and are conservatively bounded by `N+2`.
-/
theorem idealPrefixAccident_horizon_probability_bound
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hTd : T ≤ d)
    (hDim : 4096 * (hardRadius T) ^ 2 ≤ ((d - T : ℕ) : ℝ))
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (hFactorMeas : ∀ (t : Fin (N + 1)) (i : Fin T) (hi : 0 < i.val),
      Measurable (idealFutureProjectedFactor hT (idealFuturePredecessor i hi)
        A r a t.val)) :
    (((preselectedOrthonormalFrameLaw d T hTd).prod
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d))).real
      {z : IdealAccidentSample d T N |
        ∃ t ≤ N, idealPrefixAccidentAt hT z.1.1 A r z.2 a t}) ≤
      2 * (N + 2 : ℕ) * T *
        Real.exp (-((d - T : ℕ) : ℝ) / (2048 * (hardRadius T) ^ 2)) := by
  let P := (preselectedOrthonormalFrameLaw d T hTd).prod
    (Measure.pi (fun _ : Fin N => standardGaussianLaw d))
  let b : ℝ := 2 * Real.exp (-((d - T : ℕ) : ℝ) / (2048 * (hardRadius T) ^ 2))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcolumn (t : Fin (N + 1)) (i : Fin T) :
      P.real (idealFutureCoordinateEvent hT A r a t.val i) ≤ b := by
    by_cases hi : 0 < i.val
    · exact idealFutureCoordinate_probability_bound hT hTd hDim A r a i hi
        (by have ht := t.isLt; omega) (hFactorMeas t i hi)
    · have hi0 : i.val = 0 := by omega
      have he : idealFutureCoordinateEvent hT A r a t.val i = ∅ := by
        ext z
        simp [idealFutureCoordinateEvent, hi0]
      rw [he]
      simpa using hb
  have htime (t : Fin (N + 1)) :
      P.real (⋃ i : Fin T, idealFutureCoordinateEvent hT A r a t.val i) ≤ (T : ℝ) * b := by
    calc
      _ ≤ ∑ i : Fin T, P.real (idealFutureCoordinateEvent hT A r a t.val i) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _ : Fin T, b := Finset.sum_le_sum (fun i _ => hcolumn t i)
      _ = (T : ℝ) * b := by simp
  have hsubset :
      {z : IdealAccidentSample d T N |
        ∃ t ≤ N, idealPrefixAccidentAt hT z.1.1 A r z.2 a t} ⊆
      ⋃ t : Fin (N + 1), ⋃ i : Fin T, idealFutureCoordinateEvent hT A r a t.val i := by
    rintro z ⟨t, htN, hacc⟩
    obtain ⟨i, hi⟩ := (idealPrefixAccidentAt_iff_exists_futureCoordinate hT A r a t z).mp hacc
    exact Set.mem_iUnion.mpr ⟨⟨t, by omega⟩, Set.mem_iUnion.mpr ⟨i, hi⟩⟩
  calc
    _ ≤ P.real (⋃ t : Fin (N + 1), ⋃ i : Fin T,
        idealFutureCoordinateEvent hT A r a t.val i) := measureReal_mono hsubset
    _ ≤ (N + 2 : ℕ) * ((T : ℝ) * b) :=
      preselected_union_bound P (by omega) _ (by positivity) htime
    _ = _ := by dsimp [b]; ring

end

end HeavyTailedNoise
