import HeavyTailedNoise.Lower.Gated.ActualPrefixFrozenIdentity
import HeavyTailedNoise.Probability.ConditionalParametricMap

/-!
The virtual stage-zero frozen law, before any returned response.  The source
is the preselected full orthonormal-frame law and an independent finite
Gaussian auxiliary tail.  No original `N+m` tape marginal is identified here.
The canonical initial record includes the arbitrary output when `N=0`.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

def emptyRevealedPrefix (d : ℕ) : Fin 0 → Point d := fun i => i.elim0

/-- The initial pre-response snapshot depends only on the algorithm and its
fixed private realization, including the response-free `N=0` case. -/
def idealInitialPreHistory
    {d N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm d N Private) (r : Private) :
    IdealPreResponseHistory d N :=
  ⟨true, 0, (fun _ => (0, 0)),
    if 0 < N then A.decide 0 r (fun i : Fin 0 => i.elim0)
    else A.output r (fun _ => (0, 0))⟩

theorem idealPreHistoryAtTime_zero_eq_initial
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) :
    idealPreHistoryAtTime hT U A r ξ a 0 = idealInitialPreHistory A r := by
  classical
  have htr : idealPadTranscript
      (idealStateAt hT U A r ξ a 0).transcript =
      (fun _ : Fin N => ((0 : Point d), (0 : Point d))) := by
    funext i
    simp [idealStateAt, idealPadTranscript]
  have hq : idealDecisionAt hT U A r ξ a 0 =
      (idealInitialPreHistory A r).query := by
    by_cases hN : 0 < N
    · simp [idealDecisionAt, idealStateAt, idealInitialPreHistory, hN]
    · have hN0 : N = 0 := by omega
      subst N
      have hnil :
          (fun _ : Fin 0 => ((0 : Point d), (0 : Point d))) =
          (fun i : Fin 0 => i.elim0) := by
        funext i
        exact i.elim0
      simp [idealDecisionAt, idealStateAt, idealInitialPreHistory, hnil]
  simp only [idealPreHistoryAtTime, dite_eq_left (Nat.zero_le N)]
  rw [htr, hq]
  rfl

/-- The first full-frame column has exactly the existing empty-prefix Haar
next-direction law.  This is a marginal of the fixed full-frame prior. -/
theorem preselectedOrthonormalFrameLaw_firstColumn_map
    {d T : ℕ} (hT : 0 < T) (hTd : T ≤ d) :
    (preselectedOrthonormalFrameLaw d T hTd).map
      (fun U : {v : Fin T → Point d // Orthonormal ℝ v} => U.1 ⟨0, hT⟩) =
      frameNextKernel d 0 (emptyRevealedPrefix d) := by
  let first : {v : Fin T → Point d // Orthonormal ℝ v} → Point d :=
    fun U => U.1 ⟨0, hT⟩
  have hfirst : Measurable first :=
    (measurable_pi_apply (⟨0, hT⟩ : Fin T)).comp measurable_subtype_coe
  have h1T : 0 + 1 ≤ T := by omega
  have hprefix (U : {v : Fin T → Point d // Orthonormal ℝ v}) :
      Fin.init (framePrefix h1T U.1) = emptyRevealedPrefix d := by
    funext i
    exact i.elim0
  have hcolumn (U : {v : Fin T → Point d // Orthonormal ℝ v}) :
      (framePrefix h1T U.1) (Fin.last 0) = first U := rfl
  have hcond := preselectedOrthonormalFrameLaw_column_hasCondDistrib
    d 0 T hTd h1T
  have hjoint := hcond.map_eq
  simp only [hprefix, hcolumn, Measure.map_const, measure_univ, one_smul] at hjoint
  apply Measure.ext
  intro B hB
  have h := congrArg (fun ν : Measure ((Fin 0 → Point d) × Point d) =>
    ν (Set.univ ×ˢ B)) hjoint
  rw [Measure.map_apply (measurable_const.prodMk hfirst)
      (MeasurableSet.univ.prod hB),
    Measure.dirac_compProd_apply (MeasurableSet.univ.prod hB)] at h
  have hleft :
      (fun U : {v : Fin T → Point d // Orthonormal ℝ v} =>
        (emptyRevealedPrefix d, first U)) ⁻¹' (Set.univ ×ˢ B) = first ⁻¹' B := by
    ext U
    simp
  have hright :
      (Prod.mk (emptyRevealedPrefix d)) ⁻¹' (Set.univ ×ˢ B) = B := by
    ext θ
    simp
  rw [hleft, hright] at h
  rw [Measure.map_apply hfirst hB]
  exact h

/-- Stage zero's first direction and full frozen transcript have the exact
unconditional joint law used by the fixed-prefix information bound.  The
Gaussian auxiliary tail is independent of the preselected full-frame law. -/
theorem initialFrozenHaarJointLaw
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hTd : T ≤ d)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    ((preselectedOrthonormalFrameLaw d T hTd).prod
      (Measure.pi (fun _ : Fin m => standardGaussianLaw d))).map
      (fun z : {v : Fin T → Point d // Orthonormal ℝ v} ×
          (Fin m → Point d) =>
        (z.1.1 ⟨0, hT⟩,
          actualFrozenGaussianSeedState hT z.1.1 ⟨0, hT⟩ A r
            (idealInitialPreHistory A r) a m z.2)) =
      (frameNextKernel d 0 (emptyRevealedPrefix d)) ⊗ₘ
        nextDirectionFrozenKernel (m := m) hT ⟨0, hT⟩
          (emptyRevealedPrefix d) A r (idealInitialPreHistory A r) a := by
  let μ := preselectedOrthonormalFrameLaw d T hTd
  let ρ := Measure.pi (fun _ : Fin m => standardGaussianLaw d)
  let j₀ : Fin T := ⟨0, hT⟩
  let first : {v : Fin T → Point d // Orthonormal ℝ v} → Point d :=
    fun U => U.1 j₀
  let π := frameNextKernel d 0 (emptyRevealedPrefix d)
  let state : Point d × (Fin m → Point d) → Transcript d N := fun z =>
    actualFrozenGaussianSeedState hT
      (nextDirectionPrefixFrame j₀ (emptyRevealedPrefix d) z.1)
      j₀ A r (idealInitialPreHistory A r) a m z.2
  let f : Point d × (Fin m → Point d) → Point d × Transcript d N :=
    fun z => (z.1, state z)
  have hfirst : Measurable first :=
    (measurable_pi_apply j₀).comp measurable_subtype_coe
  have hstate : Measurable state :=
    measurable_joint_nextDirectionFrozenState hT j₀
      (emptyRevealedPrefix d) A r (idealInitialPreHistory A r) a
  have hf : Measurable f := measurable_fst.prodMk hstate
  have hfirstlaw : μ.map first = π :=
    preselectedOrthonormalFrameLaw_firstColumn_map hT hTd
  have hsource := (Measure.map_prod_map μ ρ hfirst
    (measurable_id : Measurable (id :
      (Fin m → Point d) → (Fin m → Point d)))).symm
  simp only [Measure.map_id] at hsource
  change (μ.prod ρ).map (fun z => (first z.1, z.2)) =
    (μ.map first).prod ρ at hsource
  rw [hfirstlaw] at hsource
  have hsourceMeas : Measurable (fun z :
      {v : Fin T → Point d // Orthonormal ℝ v} × (Fin m → Point d) =>
      (first z.1, z.2)) :=
    (hfirst.comp measurable_fst).prodMk measurable_snd
  calc
    _ = (μ.prod ρ).map (f ∘ (fun z => (first z.1, z.2))) := by
      congr 1
      funext z
      apply Prod.ext
      · rfl
      · have hprefix : framePrefix (Nat.le_of_lt j₀.isLt) z.1.1 =
            emptyRevealedPrefix d := by
          funext i
          exact i.elim0
        have h := actualFrozenGaussianSeedState_nextDirectionPrefixFrame
          hT z.1.1 j₀ A r (idealInitialPreHistory A r) a z.2
        rw [hprefix] at h
        exact h.symm
    _ = ((μ.prod ρ).map (fun z => (first z.1, z.2))).map f :=
      (Measure.map_map hf hsourceMeas).symm
    _ = (π.prod ρ).map f := by rw [hsource]
    _ = _ := by
      rw [← Measure.compProd_const]
      exact compProd_joint_map π (Kernel.const (Point d) ρ) state hstate

end

end HeavyTailedNoise
