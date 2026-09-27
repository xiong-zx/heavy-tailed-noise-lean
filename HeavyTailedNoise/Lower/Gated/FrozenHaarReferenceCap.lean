import HeavyTailedNoise.Lower.Gated.FrozenFinalCapMeas

/-!
The measurable frozen final-transcript cap event is exactly the event to
which the checked fixed-prefix Haar reference-product bound applies. The
query list is a function of the response transcript and is independent of
the next direction under the reference product measure.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem orthonormal_framePrefix
    {d T : ℕ} (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    {j : ℕ} (hj : j ≤ T) :
    Orthonormal ℝ (framePrefix hj U) := by
  change Orthonormal ℝ (U ∘ Fin.castLE hj)
  exact hU.comp (Fin.castLE hj) (Fin.castLE_injective hj)

theorem frozenFinalCapHit_iff_referenceCap
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) (tr : Transcript d N) :
    tr ∈ frozenFinalCapHit (m := m) hT U j A r s ↔
      ∃ i : Fin (m + 1),
        U j ∈ fixedPrefixCap
          (framePrefix (Nat.le_of_lt j.isLt) U)
          (frozenFinalQueryList (m := m) hT A r s tr i) := by
  unfold frozenFinalCapHit
  simp_rw [mem_prefixCapSet_iff_fixedPrefixCap U j]
  rfl

theorem frozenReferenceProduct_cap_bound
    {d T N m budget : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (hU : Orthonormal ℝ U) (j : Fin T)
    (hjd : j.val < d) (hm : 16022 ≤ d - j.val)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N)
    (ν : Measure (Transcript d N)) [IsProbabilityMeasure ν]
    (hlen : m + 1 ≤ budget + 2) :
    ((frameNextKernel d j.val
      (framePrefix (Nat.le_of_lt j.isLt) U)).prod ν).real
      {p : Point d × Transcript d N |
        ∃ i : Fin (m + 1),
          p.1 ∈ fixedPrefixCap
            (framePrefix (Nat.le_of_lt j.isLt) U)
            (frozenFinalQueryList (m := m) hT A r s p.2 i)} ≤
      2 * (budget + 2 : ℕ) *
        Real.exp (-((d - j.val : ℕ) : ℝ) * haarCapAngleSq / 2) := by
  exact fixedPrefixCap_reference_product_union hjd
    (framePrefix (Nat.le_of_lt j.isLt) U)
    (orthonormal_framePrefix U hU (Nat.le_of_lt j.isLt))
    hm ν (frozenFinalQueryList hT A r s)
    (measurable_frozenFinalQueryList hT A r s) hlen

end

end HeavyTailedNoise
