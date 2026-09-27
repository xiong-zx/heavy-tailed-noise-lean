import Mathlib

/-!
The shared gradient-only finite-budget interface. This file states no lower-bound theorem.
`N` counts returned vectors; the arbitrary output is a further decision with no response.
-/

open MeasureTheory

noncomputable section

namespace HeavyTailedNoise

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Transcript (d n : ℕ) := Fin n → Point d × Point d

/-- `F(0) - inf F ≤ Δ` is encoded as the equivalent pointwise inequality. -/
structure Objective (d : ℕ) (Δ : ℝ) where
  dimension_pos : 0 < d
  value : Point d → ℝ
  grad : Point d → Point d
  hasGradientAt : ∀ x, HasGradientAt value (grad x) x
  continuous_grad : Continuous grad
  gap : ∀ x, value 0 - value x ≤ Δ

/-- The private seed is not an observation. A call returns one vector only. -/
structure GradientOracle (d : ℕ) (Seed : Type*) [MeasurableSpace Seed] where
  law : Measure Seed
  law_probability : IsProbabilityMeasure law
  response : Point d → Seed → Point d
  measurable_response : Measurable (fun z : Point d × Seed => response z.1 z.2)

/-- Finite `q` only. Moment bounds are written without taking the positive `p`/`q` root. -/
structure Admissible (d : ℕ) (Seed : Type*) [MeasurableSpace Seed]
    (p q Δ σ Lbar : ℝ) where
  objective : Objective d Δ
  oracle : GradientOracle d Seed
  p_range : 1 < p ∧ p ≤ 2
  q_range : 1 ≤ q
  delta_pos : 0 < Δ
  sigma_nonneg : 0 ≤ σ
  Lbar_pos : 0 < Lbar
  integrable_response : ∀ x, Integrable (oracle.response x) oracle.law
  unbiased : ∀ x, (∫ ξ, oracle.response x ξ ∂oracle.law) = objective.grad x
  centered_moment : ∀ x,
    (∫⁻ ξ, ENNReal.ofReal (‖oracle.response x ξ - objective.grad x‖ ^ p) ∂oracle.law)
      ≤ ENNReal.ofReal (σ ^ p)
  same_seed_increment : ∀ x y,
    (∫⁻ ξ, ENNReal.ofReal (‖oracle.response x ξ - oracle.response y ξ‖ ^ q)
      ∂oracle.law) ≤ ENNReal.ofReal ((Lbar * ‖x - y‖) ^ q)

/-- One measurable decision rule for every history length; only the first `N` are used. -/
structure RandomAlgorithm (d N : ℕ) (Private : Type*) [MeasurableSpace Private] where
  privateLaw : Measure Private
  private_probability : IsProbabilityMeasure privateLaw
  decide : (t : ℕ) → Private → Transcript d t → Point d
  measurable_decide : ∀ t, Measurable
    (fun z : Private × Transcript d t => decide t z.1 z.2)
  output : Private → Transcript d N → Point d
  measurable_output : Measurable
    (fun z : Private × Transcript d N => output z.1 z.2)

/-- The `n` seed coordinates are used once each, after their respective decisions. -/
def runTranscript {d N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private]
    (O : GradientOracle d Seed) (A : RandomAlgorithm d N Private) (r : Private) :
    (n : ℕ) → (Fin n → Seed) → Transcript d n
  | 0, _ => fun i => i.elim0
  | n + 1, seeds =>
    let history := runTranscript O A r n (fun i => seeds i.castSucc)
    let x := A.decide n r history
    Fin.snoc history (x, O.response x (seeds (Fin.last n)))

/-- Independent identical fresh seeds across the `N` responsive decisions. -/
def freshSeedLaw {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (N : ℕ) : Measure (Fin N → Seed) :=
  Measure.pi (fun _ => O.law)

/-- Expected gradient norm, extended to `∞` when it is not integrable. -/
def risk {d N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (A : RandomAlgorithm d N Private) : ENNReal :=
  ∫⁻ r, ∫⁻ seeds,
    ENNReal.ofReal ‖I.objective.grad
      (A.output r (runTranscript I.oracle A r N seeds))‖
    ∂freshSeedLaw I.oracle N ∂A.privateLaw

end HeavyTailedNoise
