import HeavyTailedNoise.Lower.Gated.IdealRandomStartMixedFreshNoise
import HeavyTailedNoise.Probability.ConditionalFreshTail

/-!
The actual positive-stage stopped experiment under the preselected full-frame
Haar law. For each fixed arbitrary private tape, the next direction and the
unobserved random-start Gaussian tail have the claimed conditional joint law
given the revealed prefix and complete pre-response snapshot.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

def idealStoppedDirectionData
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (z : {U : Fin T → Point d // Orthonormal ℝ U} ×
      (Fin (N + m) → Point d)) :
    (Fin (k.val + 1) → Point d) ×
      (Bool × ℕ × Transcript d N × Point d) :=
  (framePrefix (Nat.succ_le_iff.mpr k.isLt) z.1.1,
    idealPreResponseTuple
      (idealStoppedPreHistory hT z.1.1 k A r
        (idealExtendedNoiseTake z.2) a))

theorem measurable_idealStoppedDirectionData
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Measurable (idealStoppedDirectionData (m := m) hT k A r a) := by
  have hco : Measurable
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} ×
          (Fin (N + m) → Point d) => (z.1.1, z.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  exact (((measurable_framePrefix (Nat.succ_le_iff.mpr k.isLt)).comp
    (measurable_subtype_coe.comp measurable_fst)).prodMk
      ((measurable_joint_idealStoppedRecordExtended hT k A r a).comp hco))

theorem idealStopped_nextDirection_tail_hasCondDistrib
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hTd : T ≤ d)
    (k : Fin T) (hk : k.val + 1 + 1 ≤ T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    let μ := preselectedOrthonormalFrameLaw d T hTd
    let ν := Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)
    let ρ := Measure.pi (fun _ : Fin m => standardGaussianLaw d)
    let κ := (frameNextKernel d (k.val + 1)).comap
      (Prod.fst : ((Fin (k.val + 1) → Point d) ×
        (Bool × ℕ × Transcript d N × Point d)) →
          (Fin (k.val + 1) → Point d)) measurable_fst
    HasCondDistrib
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} ×
          (Fin (N + m) → Point d) =>
        ((framePrefix hk z.1.1) (Fin.last (k.val + 1)),
          idealRandomStartTail hT z.1.1 k A r a z.2))
      (idealStoppedDirectionData hT k A r a)
      (κ ⊗ₖ Kernel.const
        (((Fin (k.val + 1) → Point d) ×
          (Bool × ℕ × Transcript d N × Point d)) × Point d) ρ)
      (μ.prod ν) := by
  dsimp only
  let μ := preselectedOrthonormalFrameLaw d T hTd
  let ν := Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)
  let ρ := Measure.pi (fun _ : Fin m => standardGaussianLaw d)
  let P := μ.prod ν
  let S : {U : Fin T → Point d // Orthonormal ℝ U} → (Fin (N + m) → Point d) → (Bool × ℕ × Transcript d N × Point d) := fun U ξ =>
    idealPreResponseTuple (idealStoppedPreHistory hT U.1 k A r
      (idealExtendedNoiseTake ξ) a)
  let Z : {U : Fin T → Point d // Orthonormal ℝ U} → (Fin (N + m) → Point d) → (Fin m → Point d) :=
    fun U ξ => idealRandomStartTail hT U.1 k A r a ξ
  let X := idealStoppedDirectionData (m := m) hT k A r a
  let D : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) → Point d :=
    fun z => (framePrefix hk z.1.1) (Fin.last (k.val + 1))
  let κ : Kernel ((Fin (k.val + 1) → Point d) × (Bool × ℕ × Transcript d N × Point d)) (Point d) :=
    (frameNextKernel d (k.val + 1)).comap
    (Prod.fst : ((Fin (k.val + 1) → Point d) × (Bool × ℕ × Transcript d N × Point d)) →
      (Fin (k.val + 1) → Point d))
    (measurable_fst : Measurable
      (Prod.fst : ((Fin (k.val + 1) → Point d) × (Bool × ℕ × Transcript d N × Point d)) →
        (Fin (k.val + 1) → Point d)))
  have hco : Measurable (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => (z.1.1, z.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hS : Measurable (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => S z.1 z.2) :=
    (measurable_joint_idealStoppedRecordExtended hT k A r a).comp hco
  have hZ : Measurable (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => Z z.1 z.2) :=
    (measurable_joint_idealRandomStartTail hT k A r a).comp hco
  have hX : Measurable X := measurable_idealStoppedDirectionData hT k A r a
  have hD : Measurable D :=
    (((measurable_pi_apply (Fin.last (k.val + 1))).comp
      (measurable_framePrefix hk)).comp measurable_subtype_coe).comp measurable_fst
  have hinput : Measurable (fun ξ : (Fin (N + m) → Point d) =>
      (r, idealExtendedNoiseTake ξ)) :=
    measurable_const.prodMk measurable_idealExtendedNoiseTake
  have hInd : (Prod.fst : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) → {U : Fin T → Point d // Orthonormal ℝ U}) ⟂ᵢ[P]
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => (r, idealExtendedNoiseTake z.2)) :=
    indepFun_prod measurable_id hinput
  have hLaw : P.map (Prod.fst : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) → {U : Fin T → Point d // Orthonormal ℝ U}) = μ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hcond : HasCondDistrib D X κ P := by
    have hc := idealStoppedPreHistory_nextColumn_hasCondDistrib_complete
      P hT hTd k hk A a (Prod.fst : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) → {U : Fin T → Point d // Orthonormal ℝ U})
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => (r, idealExtendedNoiseTake z.2))
      measurable_fst (hinput.comp measurable_snd) hInd hLaw
    change HasCondDistrib D
      (fun z : {U : Fin T → Point d // Orthonormal ℝ U} ×
          (Fin (N + m) → Point d) =>
        (framePrefix (Nat.succ_le_iff.mpr k.isLt) z.1.1,
          idealPreResponseTuple
            (idealStoppedPreHistory hT z.1.1 k A r
              (idealExtendedNoiseTake z.2) a))) κ P
    simpa only [init_framePrefix_eq, D, κ] using hc
  have hFiber (U : {U : Fin T → Point d // Orthonormal ℝ U}) :
      ν.map (fun ξ => (S U ξ, Z U ξ)) = (ν.map (S U)).prod ρ :=
    idealRandomStart_record_tail_jointLaw hT U.1 k A r a
  have hFull := fiberwise_fresh_tail_jointLaw μ ν ρ S Z hS hZ hFiber
  let f : {U : Fin T → Point d // Orthonormal ℝ U} × (Bool × ℕ × Transcript d N × Point d) → ((Fin (k.val + 1) → Point d) × (Bool × ℕ × Transcript d N × Point d)) × Point d :=
    fun p =>
      ((framePrefix (Nat.succ_le_iff.mpr k.isLt) p.1.1, p.2),
        (framePrefix hk p.1.1) (Fin.last (k.val + 1)))
  have hf : Measurable f :=
    ((((measurable_framePrefix (Nat.succ_le_iff.mpr k.isLt)).comp
      measurable_subtype_coe).comp measurable_fst).prodMk measurable_snd).prodMk
        ((((measurable_pi_apply (Fin.last (k.val + 1))).comp
          (measurable_framePrefix hk)).comp measurable_subtype_coe).comp measurable_fst)
  have hUS : Measurable (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => (z.1, S z.1 z.2)) :=
    measurable_fst.prodMk hS
  have hTriple : Measurable (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) =>
      ((z.1, S z.1 z.2), Z z.1 z.2)) := hUS.prodMk hZ
  have hTail : P.map (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => ((X z, D z), Z z.1 z.2)) =
      (P.map (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => (X z, D z))).prod ρ := by
    calc
      _ = (P.map (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) =>
          ((z.1, S z.1 z.2), Z z.1 z.2))).map (Prod.map f id) := by
        rw [Measure.map_map (hf.prodMap measurable_id) hTriple]
        rfl
      _ = ((P.map (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => (z.1, S z.1 z.2))).prod ρ).map
          (Prod.map f id) := by rw [hFull]
      _ = ((P.map (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => (z.1, S z.1 z.2))).map f).prod ρ := by
        simpa only [Measure.map_id] using
          (Measure.map_prod_map
            (P.map (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => (z.1, S z.1 z.2))) ρ hf measurable_id).symm
      _ = _ := by
        rw [Measure.map_map hf hUS]
        rfl
  exact hasCondDistrib_pair_fresh_tail P X D
    (fun z : {U : Fin T → Point d // Orthonormal ℝ U} × (Fin (N + m) → Point d) => Z z.1 z.2) hX hD hZ κ ρ hcond hTail

end

end HeavyTailedNoise
