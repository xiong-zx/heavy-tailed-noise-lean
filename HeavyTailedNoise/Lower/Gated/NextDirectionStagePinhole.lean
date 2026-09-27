import HeavyTailedNoise.Lower.Gated.NextDirectionJointKL

/-!
At one fixed valid revealed prefix and stopped pre-response snapshot, the
checked joint Gaussian KL and independent Haar cap bound imply a half
probability bound for the measurable frozen cap event. Numerical budget
hypotheses are explicit and will be discharged by the public dimension choice.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

theorem measurableSet_nextDirectionFinalCapEvent
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (v : Fin j → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) :
    MeasurableSet (nextDirectionFinalCapEvent (m := m) hT v A r s) := by
  unfold nextDirectionFinalCapEvent
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  have hq : Measurable (fun p : Point d × Transcript d N =>
      frozenFinalQueryList (m := m) hT A r s p.2 i) :=
    ((measurable_pi_iff.mp
      (measurable_frozenFinalQueryList (m := m) hT A r s)) i).comp
      measurable_snd
  have h1 : MeasurableSet {p : Point d × Transcript d N |
      (1 / 2 : ℝ) ≤
        |inner ℝ (frozenFinalQueryList (m := m) hT A r s p.2 i) p.1|} :=
    measurableSet_le measurable_const (by fun_prop)
  have h2 : MeasurableSet {p : Point d × Transcript d N |
      ‖frameResidual v
          (frozenFinalQueryList (m := m) hT A r s p.2 i) -
        inner ℝ (frozenFinalQueryList (m := m) hT A r s p.2 i) p.1 • p.1‖ ^ 2 ≤
          1000 + 1 / 16 + 1} := by
    unfold frameResidual
    exact measurableSet_le (by fun_prop) measurable_const
  change MeasurableSet
    ({p : Point d × Transcript d N |
      (1 / 2 : ℝ) ≤
        |inner ℝ (frozenFinalQueryList (m := m) hT A r s p.2 i) p.1|} ∩
     {p : Point d × Transcript d N |
      ‖frameResidual v
          (frozenFinalQueryList (m := m) hT A r s p.2 i) -
        inner ℝ (frozenFinalQueryList (m := m) hT A r s p.2 i) p.1 • p.1‖ ^ 2 ≤
          1000 + 1 / 16 + 1})
  exact h1.inter h2

theorem nextDirection_frozenCap_probability_half
    {d T N m budget : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hd : 0 < d) (hT : 0 < T) (hTd : T ≤ d)
    (j : Fin T) (v : Fin j.val → Point d)
    (hv : Orthonormal ℝ v) (hjd : j.val < d)
    (hDim : 16022 ≤ d - j.val)
    (θ₀ : Point d) (hθ₀ : Orthonormal ℝ (Fin.snoc v θ₀))
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀)
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N)
    (hlen : m + 1 ≤ budget + 2)
    (I qcap : ℝ) (hI : 0 ≤ I)
    (hKLbudget : (m : ENNReal) * ENNReal.ofReal
        ((d : ℝ) * (300 : ℝ) ^ 2 / (2 * σ₀ ^ 2)) ≤ ENNReal.ofReal I)
    (hqcap₀ : 0 < qcap) (hqcap₁ : qcap < 1)
    (hcapBudget : 2 * (budget + 2 : ℕ) *
        Real.exp (-((d - j.val : ℕ) : ℝ) * haarCapAngleSq / 2) ≤ qcap)
    (hlogBudget : I + Real.log 2 ≤
      (1 / 2 : ℝ) * Real.log qcap⁻¹) :
    let K := repairedNextDirectionFrozenKernel
      (m := m) hT j v A r s (σ₀ / Real.sqrt d) θ₀
    let E := nextDirectionFinalCapEvent (m := m) hT v A r s
    (((frameNextKernel d j.val v) ⊗ₘ K) E).toReal ≤ 1 / 2 := by
  dsimp only
  let π := frameNextKernel d j.val v
  let K := repairedNextDirectionFrozenKernel
    (m := m) hT j v A r s (σ₀ / Real.sqrt d) θ₀
  let R := nextDirectionFrozenKernel
    (m := m) hT j v A r s (σ₀ / Real.sqrt d) θ₀
  let E := nextDirectionFinalCapEvent (m := m) hT v A r s
  have hE : MeasurableSet E :=
    measurableSet_nextDirectionFinalCapEvent hT v A r s
  have hKL : klDiv (π ⊗ₘ K) (π.prod R) ≤ ENNReal.ofReal I :=
    (nextDirection_jointKL_le hd hT hTd j v θ₀ hθ₀
      σ₀ hσ₀ A r s).trans hKLbudget
  have hRef : ((π.prod R) E).toReal ≤ qcap := by
    have h := nextDirection_referenceProduct_cap_bound
      hT j v hv hjd hDim A r s θ₀ σ₀ hlen
    have hBase : ((π.prod R) E).toReal ≤
        2 * (budget + 2 : ℕ) *
          Real.exp (-((d - j.val : ℕ) : ℝ) * haarCapAngleSq / 2) := by
      simpa [π, R, E, measureReal_def] using h
    exact hBase.trans hcapBudget
  exact pinhole_half_of_referenceKL_cap_or_zero
    (π ⊗ₘ K) (π.prod R) E hE I qcap hI
    hqcap₀ hqcap₁ hRef hKL hlogBudget

end

end HeavyTailedNoise
