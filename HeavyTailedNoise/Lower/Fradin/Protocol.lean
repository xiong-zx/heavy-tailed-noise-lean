import HeavyTailedNoise.Model.Basic

/-! First-order shared-seed batch protocol for Fradin et al., arXiv:2512.18713v2.
The observed value is the population value F(x), not a sampled loss or a seed.
`n` counts completed rounds; the next batch is decision round n+1, with no response.
-/

namespace HeavyTailedNoise.Fradin

open MeasureTheory
noncomputable section
set_option autoImplicit false
universe u v

abbrev Batch (d K : ℕ) := Fin K → Point d
abbrev BatchRecord (d K : ℕ) := Fin K → Point d × (ℝ × Point d)
abbrev Transcript (d K n : ℕ) := Fin n → BatchRecord d K

/-- Only observation structure is added to the existing gradient oracle. -/
structure FirstOrderOracle (d : ℕ) (Seed : Type*) [MeasurableSpace Seed] where
  gradient : GradientOracle d Seed
  value : Point d → ℝ
  measurable_value : Measurable value

def FirstOrderOracle.ofAdmissible {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L) : FirstOrderOracle d Seed where
  gradient := I.oracle
  value := I.objective.value
  measurable_value := (continuous_iff_continuousAt.mpr
    (fun x => (I.objective.hasGradientAt x).continuousAt)).measurable

/-- An arbitrary measurable private seed and every full-history batch rule. -/
structure Algorithm (d K : ℕ) (Private : Type*) [MeasurableSpace Private] where
  privateLaw : Measure Private
  private_probability : IsProbabilityMeasure privateLaw
  decide : (n : ℕ) → Private → Transcript d K n → Batch d K
  measurable_decide : ∀ n, Measurable
    (fun z : Private × Transcript d K n => decide n z.1 z.2)

/-- All K points are chosen before the same seed is evaluated at any point. -/
def runTranscript {d K : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private) (r : Private) :
    (n : ℕ) → (Fin n → Seed) → Transcript d K n
  | 0, _ => fun i => i.elim0
  | n+1, seeds =>
    let h := runTranscript O A r n (fun i => seeds i.castSucc)
    let x := A.decide n r h
    Fin.snoc h (fun k => (x k, O.value (x k),
      O.gradient.response (x k) (seeds (Fin.last n))))

def nextBatch {d K : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private)
    (n : ℕ) (r : Private) (seeds : Fin n → Seed) : Batch d K :=
  A.decide n r (runTranscript O A r n seeds)

theorem measurable_runTranscript {d K : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private) (n : ℕ) :
    Measurable (fun z : Private × (Fin n → Seed) => runTranscript O A z.1 n z.2) := by
  induction n with
  | zero =>
      refine measurable_pi_iff.mpr ?_
      intro i
      exact i.elim0
  | succ n ih =>
      have hp : Measurable (fun z : Private × (Fin (n+1) → Seed) =>
          (z.1, fun i : Fin n => z.2 i.castSucc)) :=
        measurable_fst.prodMk <| measurable_pi_iff.mpr fun i =>
          (measurable_pi_apply i.castSucc).comp measurable_snd
      have hh := ih.comp hp
      have hx := (A.measurable_decide n).comp (measurable_fst.prodMk hh)
      have hl : Measurable (fun z : Private × (Fin (n+1) → Seed) =>
          fun k : Fin K =>
            (A.decide n z.1 (runTranscript O A z.1 n (fun i => z.2 i.castSucc)) k,
             O.value (A.decide n z.1 (runTranscript O A z.1 n
               (fun i => z.2 i.castSucc)) k),
             O.gradient.response (A.decide n z.1 (runTranscript O A z.1 n
               (fun i => z.2 i.castSucc)) k) (z.2 (Fin.last n)))) := by
        refine measurable_pi_iff.mpr fun k => ?_
        have hk := (measurable_pi_apply k).comp hx
        exact hk.prodMk ((O.measurable_value.comp hk).prodMk
          (O.gradient.measurable_response.comp
            (hk.prodMk ((measurable_pi_apply (Fin.last n)).comp measurable_snd))))
      refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [runTranscript, Fin.snoc_last] using hl
      · simpa only [runTranscript, Fin.snoc_castSucc, Function.comp_def] using
          (measurable_pi_apply j).comp hh

theorem measurable_nextBatch {d K : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private) (n : ℕ) :
    Measurable (fun z : Private × (Fin n → Seed) => nextBatch O A n z.1 z.2) :=
  (A.measurable_decide n).comp
    (measurable_fst.prodMk (measurable_runTranscript O A n))

theorem runTranscript_last {d K : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private)
    (r : Private) (n : ℕ) (seeds : Fin (n+1) → Seed) (k : Fin K) :
    runTranscript O A r (n+1) seeds (Fin.last n) k =
      let x := nextBatch O A n r (fun i => seeds i.castSucc) k
      (x, O.value x, O.gradient.response x (seeds (Fin.last n))) := by
  simp [runTranscript, nextBatch]

theorem runTranscript_prefix {d K : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private)
    (r : Private) (n : ℕ) (seeds : Fin (n+1) → Seed) (i : Fin n) :
    runTranscript O A r (n+1) seeds i.castSucc =
      runTranscript O A r n (fun j => seeds j.castSucc) i := by
  simp [runTranscript]

/-- n completed batches return exactly n*K vectors, from n fresh seeds. -/
theorem response_positions_card (n K : ℕ) :
    Fintype.card (Fin n × Fin K) = n*K := by simp

/-- The evaluated next batch belongs to round n+1, after n responsive rounds. -/
theorem responsive_round_positions_card (n : ℕ) : Fintype.card (Fin n) = n := by simp

/-- Support condition on actual runs. It imposes nothing on unreachable histories.
This local condition is a proof interface, not the final universal algorithm class. -/
def ZeroRespectingOn {d K : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private) : Prop :=
  ∀ n, ∀ᵐ z ∂A.privateLaw.prod (freshSeedLaw O.gradient n),
    ∀ k : Fin K, ∀ i : Fin d,
      nextBatch O A n z.1 z.2 k i ≠ 0 →
        ∃ j : Fin n, ∃ l : Fin K, (runTranscript O A z.1 n z.2 j l).2.2 i ≠ 0

/-- Gradient norm at slot k of the response-free round n+1. -/
def slotRisk {d K : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (A : Algorithm d K Private) (n : ℕ) (k : Fin K) : ENNReal :=
  ∫⁻ z : Private × (Fin n → Seed),
    ENNReal.ofReal ‖I.objective.grad
      (nextBatch (FirstOrderOracle.ofAdmissible I) A n z.1 z.2 k)‖
    ∂A.privateLaw.prod (freshSeedLaw I.oracle n)

theorem measurable_slotRiskValue {d K : ℕ} {Seed Private : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (A : Algorithm d K Private) (n : ℕ) (k : Fin K) :
    Measurable (fun z : Private × (Fin n → Seed) =>
      ENNReal.ofReal ‖I.objective.grad
        (nextBatch (FirstOrderOracle.ofAdmissible I) A n z.1 z.2 k)‖) :=
  ENNReal.measurable_ofReal.comp
    ((I.objective.continuous_grad.measurable.comp
      ((measurable_pi_apply k).comp
        (measurable_nextBatch (FirstOrderOracle.ofAdmissible I) A n))).norm)

/-- The first-order oracle class of Fradin v2, Definition B.1, before imposing
moment, smoothness, or initial-gap restrictions. This predicate includes every
continuously differentiable population value with an integrable unbiased oracle. -/
def FirstOrderOracle.IsUnbiased {d : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    (O : FirstOrderOracle d Seed) : Prop :=
  ∃ grad : Point d → Point d,
    (∀ x, HasGradientAt O.value (grad x) x) ∧ Continuous grad ∧
    (∀ x, Integrable (O.gradient.response x) O.gradient.law) ∧
    (∀ x, (∫ ξ, O.gradient.response x ξ ∂O.gradient.law) = grad x)

theorem FirstOrderOracle.ofAdmissible_isUnbiased {d : ℕ} {Seed : Type u}
    [MeasurableSpace Seed] {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L) :
    (FirstOrderOracle.ofAdmissible I).IsUnbiased :=
  ⟨I.objective.grad, I.objective.hasGradientAt, I.objective.continuous_grad,
    I.integrable_response, I.unbiased⟩

/-- The global zero-respecting class of Fradin v2, Definition B.4.
`u` is the universe of all oracle seed spaces and `v` that of the private space.
The condition is almost sure on each actual run, for every C¹ value and every
integrable unbiased first-order oracle, not just for the chosen hard instance.
It does not constrain unreachable transcripts or restrict decisions to prefixes. -/
def ZeroRespecting {d K : ℕ} {Private : Type v} [MeasurableSpace Private]
    (A : Algorithm d K Private) : Prop :=
  ∀ (Seed : Type u) (m : MeasurableSpace Seed),
    letI := m
    ∀ O : FirstOrderOracle d Seed, O.IsUnbiased → ZeroRespectingOn O A

theorem ZeroRespecting.on {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {A : Algorithm d K Private} (hA : ZeroRespecting.{u, v} A)
    (O : FirstOrderOracle d Seed) (hO : O.IsUnbiased) : ZeroRespectingOn O A :=
  hA Seed inferInstance O hO

theorem ZeroRespecting.on_admissible {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L : ℝ} {A : Algorithm d K Private}
    (hA : ZeroRespecting.{u, v} A) (I : Admissible d Seed p q Δ σ L) :
    ZeroRespectingOn (FirstOrderOracle.ofAdmissible I) A :=
  hA.on _ (FirstOrderOracle.ofAdmissible_isUnbiased I)

/-- Independent private randomness and exactly n independent oracle seeds. -/
theorem runLaw_probability {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private) (n : ℕ) :
    IsProbabilityMeasure (A.privateLaw.prod (freshSeedLaw O.gradient n)) := by
  letI := O.gradient.law_probability
  letI := A.private_probability
  unfold freshSeedLaw
  infer_instance

end
end HeavyTailedNoise.Fradin
