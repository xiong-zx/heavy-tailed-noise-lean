import HeavyTailedNoise.Lower.Gated.PrefixHaarCapBridge

/-!
The frozen candidate-query list is read from a final full transcript and is
therefore independent of the hidden next Haar direction under a reference
product law. The list and its cap event are measurable.
-/

namespace HeavyTailedNoise

noncomputable section

theorem measurableSet_prefixCapSet
    {d T : ℕ} (U : Fin T → Point d) (j : Fin T) :
    MeasurableSet (prefixCapSet U j) := by
  have hcoord : Measurable (fun y : Point d => frameCoordinates U y j) := by
    unfold frameCoordinates
    fun_prop
  have hres : Measurable (fun y : Point d =>
      frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) y) := by
    unfold frameOrthogonalResidual frameCoordinates
    fun_prop
  have h1 : MeasurableSet {y : Point d |
      (1 / 2 : ℝ) ≤ |frameCoordinates U y j|} :=
    measurableSet_le measurable_const hcoord.abs
  have h2 : MeasurableSet {y : Point d |
      ‖frameOrthogonalResidual U (Finset.univ.filter (· ≤ j)) y‖ ^ 2 ≤
        1000 + 1 / 16 + 1} :=
    measurableSet_le (by fun_prop) measurable_const
  exact h1.inter h2

def frozenFinalQueryList
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N) :
    Transcript d N → Fin (m + 1) → Point d :=
  fun tr i => softProjection (hardRadius T)
    (actualFrozenQuery A r s i.val tr)

theorem measurable_frozenFinalQueryList
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N) :
    Measurable (frozenFinalQueryList (m := m) hT A r s) := by
  have hR : 0 < hardRadius T := by
    unfold hardRadius
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    positivity
  have hsoft : Measurable (softProjection (hardRadius T) : Point d → Point d) :=
    (contDiff_softProjection_two hR).continuous.measurable
  apply measurable_pi_iff.mpr
  intro i
  exact hsoft.comp (measurable_actualFrozenQuery A r s i.val)

def frozenFinalCapHit
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) : Set (Transcript d N) :=
  {tr | ∃ i : Fin (m + 1),
    frozenFinalQueryList (m := m) hT A r s tr i ∈ prefixCapSet U j}

theorem measurableSet_frozenFinalCapHit
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) :
    MeasurableSet (frozenFinalCapHit (m := m) hT U j A r s) := by
  have hq := measurable_frozenFinalQueryList (m := m) hT A r s
  have hcap := measurableSet_prefixCapSet U j
  unfold frozenFinalCapHit
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  exact hcap.preimage ((measurable_pi_iff.mp hq) i)

end

end HeavyTailedNoise
