import HeavyTailedNoise.Lower.Gated.FrozenSnapshotJointKernel
import HeavyTailedNoise.Lower.Gated.LowerBoundPinholeParameters

/-!
The final frozen cap event is measurable jointly in conditioning data
`(revealed prefix, stopped tuple)` and output `(next direction, transcript)`.
For every valid prefix, the original jointly measurable snapshot kernel has
cap probability at most one half under the manuscript's public parameters.
Reference directions are selected only inside each fixed-data proof.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem measurable_joint_frozenFinalQueryList_tuple
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private) (r : Private) :
    Measurable (fun z :
        (Bool × ℕ × Transcript d N × Point d) × Transcript d N =>
      frozenFinalQueryList (m := m) hT A r
        (idealPreResponseHistoryOfTuple z.1) z.2) := by
  have hR : 0 < hardRadius T := by
    unfold hardRadius
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    positivity
  have hsoft : Measurable (softProjection (hardRadius T) : Point d → Point d) :=
    (contDiff_softProjection_two hR).continuous.measurable
  apply measurable_pi_iff.mpr
  intro i
  exact hsoft.comp (measurable_joint_actualFrozenQuery_tuple A r i.val)

/-- The exact fixed-snapshot cap events assembled into one joint set. -/
def frozenSnapshotFinalCapEvent
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) :
    Set (((Fin j.val → Point d) ×
      (Bool × ℕ × Transcript d N × Point d)) ×
      (Point d × Transcript d N)) :=
  {z | z.2 ∈ nextDirectionFinalCapEvent (m := m) hT z.1.1 A r
    (idealPreResponseHistoryOfTuple z.1.2)}

@[simp] theorem frozenSnapshotFinalCapEvent_section
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (p : (Fin j.val → Point d) ×
      (Bool × ℕ × Transcript d N × Point d)) :
    (Prod.mk p) ⁻¹' frozenSnapshotFinalCapEvent (m := m) hT j A r =
      nextDirectionFinalCapEvent (m := m) hT p.1 A r
        (idealPreResponseHistoryOfTuple p.2) := rfl

/-- The cap geometry is measurable with prefix, query, and direction all
variable.  Keeping this geometry separate avoids expanding the query rule. -/
theorem measurableSet_fixedPrefixCap_graph {d k : ℕ} :
    MeasurableSet {z : (Fin k → Point d) × (Point d × Point d) |
      z.2.2 ∈ fixedPrefixCap z.1 z.2.1} := by
  have hleft : MeasurableSet {z : (Fin k → Point d) × (Point d × Point d) |
      (1 / 2 : ℝ) ≤ |inner ℝ z.2.1 z.2.2|} :=
    measurableSet_le measurable_const (by fun_prop)
  have hright : MeasurableSet {z : (Fin k → Point d) × (Point d × Point d) |
      ‖frameResidual z.1 z.2.1 - inner ℝ z.2.1 z.2.2 • z.2.2‖ ^ 2 ≤
        1000 + 1 / 16 + 1} := by
    unfold frameResidual
    exact measurableSet_le (by fun_prop) measurable_const
  exact hleft.inter hright

theorem measurableSet_prefixQueryCapEvent
    {X : Type*} [MeasurableSpace X] {d k m : ℕ}
    (v : X → Fin k → Point d) (hv : Measurable v)
    (θ : X → Point d) (hθ : Measurable θ)
    (q : X → Fin (m + 1) → Point d) (hq : Measurable q) :
    MeasurableSet {x : X | ∃ i : Fin (m + 1),
      θ x ∈ fixedPrefixCap (v x) (q x i)} := by
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  have hinput : Measurable (fun x : X => (v x, (q x i, θ x))) :=
    hv.prodMk (((measurable_pi_iff.mp hq) i).prodMk hθ)
  exact (measurableSet_fixedPrefixCap_graph (d := d) (k := k)).preimage hinput

-- Compose the proved measurable interfaces without reducing the algorithm
-- or cap geometry inside the concrete snapshot event.
attribute [local irreducible] frozenFinalQueryList fixedPrefixCap

theorem measurableSet_frozenSnapshotFinalCapEvent
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) :
    MeasurableSet (frozenSnapshotFinalCapEvent (m := m) hT j A r) := by
  change MeasurableSet {z :
      ((Fin j.val → Point d) ×
        (Bool × ℕ × Transcript d N × Point d)) ×
      (Point d × Transcript d N) | ∃ i : Fin (m + 1),
      z.2.1 ∈ fixedPrefixCap z.1.1
        (frozenFinalQueryList (m := m) hT A r
          (idealPreResponseHistoryOfTuple z.1.2) z.2.2 i)}
  have hinput : Measurable (fun z :
      ((Fin j.val → Point d) ×
        (Bool × ℕ × Transcript d N × Point d)) ×
      (Point d × Transcript d N) => (z.1.2, z.2.2)) :=
    (measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)
  have hq : Measurable (fun z :
      ((Fin j.val → Point d) ×
        (Bool × ℕ × Transcript d N × Point d)) ×
      (Point d × Transcript d N) => frozenFinalQueryList (m := m) hT A r
        (idealPreResponseHistoryOfTuple z.1.2) z.2.2) :=
    (measurable_joint_frozenFinalQueryList_tuple (m := m) hT A r).comp hinput
  exact measurableSet_prefixQueryCapEvent
    (X := ((Fin j.val → Point d) ×
      (Bool × ℕ × Transcript d N × Point d)) ×
      (Point d × Transcript d N)) (d := d) (k := j.val) (m := m)
    (fun z => z.1.1) (measurable_fst.comp measurable_fst)
    (fun z => z.2.1) (measurable_fst.comp measurable_snd)
    (fun z => frozenFinalQueryList (m := m) hT A r
      (idealPreResponseHistoryOfTuple z.1.2) z.2.2) hq

/-- The original snapshot kernel obeys the checked pinhole bound at every
valid prefix.  Its globally measurable definition needs no reference choice;
the repaired fixed-prefix kernel is equal under its Haar composition law. -/
theorem frozenSnapshotPairKernel_cap_probability_half_actual_parameters
    {d T N m : ℕ} {S : ℝ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hdim : 2 * T ≤ d) (hS : 0 < S)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2)))
    (hdimlog : 21400 *
      (1 + Real.log (2 * (gatedStageLength d T S : ℝ))) ≤ (d - T : ℕ))
    (hm : m ≤ gatedStageLength d T S)
    (j : Fin T) (A : RandomAlgorithm d N Private) (r : Private)
    (p : (Fin j.val → Point d) ×
      (Bool × ℕ × Transcript d N × Point d))
    (hv : Orthonormal ℝ p.1) :
    (frozenSnapshotPairKernel (m := m) hT j A r ((S / 80) / Real.sqrt d) p
      ((Prod.mk p) ⁻¹' frozenSnapshotFinalCapEvent (m := m) hT j A r)).toReal ≤
      1 / 2 := by
  have hTd : T ≤ d := by omega
  have hjd : j.val < d := j.isLt.trans_le hTd
  obtain ⟨θ₀, hθ₀⟩ := exists_validNextDirection hjd p.1 hv
  have hhalf := nextDirection_frozenCap_probability_half_actual_parameters
    hT hdim hS hlarge hdimlog hm j p.1 hv θ₀ hθ₀ A r
      (idealPreResponseHistoryOfTuple p.2)
  dsimp only at hhalf
  have hae := repairedNextDirectionFrozenKernel_ae_eq_original
    (m := m) hT j p.1 hjd hv A r (idealPreResponseHistoryOfTuple p.2)
      ((S / 80) / Real.sqrt d) θ₀
  have hlaw :
      (frameNextKernel d j.val p.1) ⊗ₘ
        repairedNextDirectionFrozenKernel (m := m) hT j p.1 A r
          (idealPreResponseHistoryOfTuple p.2) ((S / 80) / Real.sqrt d) θ₀ =
      (frameNextKernel d j.val p.1) ⊗ₘ
        nextDirectionFrozenKernel (m := m) hT j p.1 A r
          (idealPreResponseHistoryOfTuple p.2) ((S / 80) / Real.sqrt d) :=
    Measure.compProd_congr hae
  rw [frozenSnapshotPairKernel_apply, frozenSnapshotFinalCapEvent_section, ← hlaw]
  exact hhalf

end

end HeavyTailedNoise
