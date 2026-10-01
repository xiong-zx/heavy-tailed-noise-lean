import HeavyTailedNoise.Upper.K1.Main
import HeavyTailedNoise.Model.Distributional
import HeavyTailedNoise.Lower.Gated.GatedHaarMinimaxComplexity

/-!
Lift the literal shared-batch EMA algorithm's finite private output index
across private universes. This is only a measurable reencoding of the same
private law and decision/output rules. The resulting guarantee has one
physical-parameter response cap for every dimension and admissible oracle.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

universe u

/-- The original algorithm with its finite private index reencoded in
`Type u`. Its seed is hidden, and its responsive protocol is unchanged. -/
def privateLiftAlgorithm {q : ℝ} (P : Schedule q) {d : ℕ} :
    RandomAlgorithm d (responseCount P) (ULift.{u} (Fin P.T)) where
  privateLaw := Measure.map ULift.up (algorithm (d := d) P).privateLaw
  private_probability := by
    letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
      (algorithm (d := d) P).private_probability
    infer_instance
  decide := fun t r H => (algorithm (d := d) P).decide t r.down H
  measurable_decide := by
    intro t
    have hpair : Measurable
        (fun z : ULift.{u} (Fin P.T) × Transcript d t =>
          (z.1.down, z.2)) :=
      (measurable_down.comp measurable_fst).prodMk measurable_snd
    exact ((algorithm (d := d) P).measurable_decide t).comp hpair
  output := fun r H => (algorithm (d := d) P).output r.down H
  measurable_output := by
    have hpair : Measurable
        (fun z : ULift.{u} (Fin P.T) ×
          Transcript d (responseCount P) => (z.1.down, z.2)) :=
      (measurable_down.comp measurable_fst).prodMk measurable_snd
    exact (algorithm (d := d) P).measurable_output.comp hpair

theorem privateLiftAlgorithm_runTranscript {q : ℝ} (P : Schedule q)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (r : ULift.{u} (Fin P.T)) :
    ∀ n (seeds : Fin n → Seed),
      runTranscript O (privateLiftAlgorithm.{u} (d := d) P) r n seeds =
        runTranscript O (algorithm (d := d) P) r.down n seeds := by
  intro n
  induction n with
  | zero =>
      intro seeds
      rfl
  | succ n ih =>
      intro seeds
      have hprefix := ih (fun i : Fin n => seeds i.castSucc)
      simp only [runTranscript]
      rw [hprefix]
      rfl

theorem privateLiftAlgorithm_output {q : ℝ} (P : Schedule q)
    {d : ℕ} (r : ULift.{u} (Fin P.T))
    (H : Transcript d (responseCount P)) :
    (privateLiftAlgorithm.{u} (d := d) P).output r H =
      (algorithm (d := d) P).output r.down H := rfl

/-- Relabeling the independent finite private index leaves the risk exactly
unchanged for every oracle and every response budget in the schedule. -/
theorem risk_privateLiftAlgorithm_eq {q : ℝ} (P : Schedule q)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar) :
    risk I (privateLiftAlgorithm.{u} P) =
      risk I (algorithm P) := by
  let A : RandomAlgorithm d (responseCount P) (Fin P.T) := algorithm P
  let A' : RandomAlgorithm d (responseCount P) (ULift.{u} (Fin P.T)) :=
    privateLiftAlgorithm.{u} P
  let F : ULift.{u} (Fin P.T) → ENNReal := fun r =>
    ∫⁻ seeds : Fin (responseCount P) → Seed,
      ENNReal.ofReal ‖I.objective.grad
        (A'.output r (runTranscript I.oracle A' r
          (responseCount P) seeds))‖
      ∂freshSeedLaw I.oracle (responseCount P)
  have hFdown : Measurable (fun r : Fin P.T => F (ULift.up r)) :=
    measurable_of_finite _
  have hF : Measurable F := by
    have heq : F =
        (fun r : Fin P.T => F (ULift.up r)) ∘ ULift.down := by
      funext r
      cases r
      rfl
    rw [heq]
    exact hFdown.comp measurable_down
  change (∫⁻ r : ULift.{u} (Fin P.T), F r
      ∂Measure.map ULift.up A.privateLaw) =
    ∫⁻ r : Fin P.T,
      ∫⁻ seeds : Fin (responseCount P) → Seed,
        ENNReal.ofReal ‖I.objective.grad
          (A.output r (runTranscript I.oracle A r
            (responseCount P) seeds))‖
        ∂freshSeedLaw I.oracle (responseCount P)
      ∂A.privateLaw
  rw [lintegral_map hF measurable_up]
  apply lintegral_congr
  intro r
  apply lintegral_congr
  intro seeds
  rw [privateLiftAlgorithm_runTranscript.{u} P I.oracle (ULift.up r)
    (responseCount P) seeds]
  rfl

/-- The same physical `N` works in every positive dimension for every
admissible gradient-only oracle, with arbitrary private universe `u`. -/
theorem strict_k1_shared_batch_ema_uniform_guarantee
    (p q Δ σ Lbar ε : ℝ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hLbar : 0 < Lbar)
    (hε : 0 < ε) :
    HasDimensionUniformGuarantee.{u, 0}
      (responseCount (upperSchedule p q Δ σ Lbar ε hε))
      p q Δ σ Lbar ε := by
  let P : Schedule q := upperSchedule p q Δ σ Lbar ε hε
  intro d hd
  refine ⟨ULift.{u} (Fin P.T), inferInstance,
    privateLiftAlgorithm.{u} (d := d) P, ?_⟩
  intro Seed seedSpace I
  letI : MeasurableSpace Seed := seedSpace
  have hmain := (Admissible.strict_k1_shared_batch_ema_upper I ε hε).1
  exact (risk_privateLiftAlgorithm_eq.{u} P I).trans_le hmain

/-- The exact shared minimax infimum is no larger than this one feasible
natural response cap. No smaller algorithm class is substituted. -/
theorem strict_k1_shared_batch_ema_minimax_le_responseCount
    (p q Δ σ Lbar ε : ℝ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hLbar : 0 < Lbar)
    (hε : 0 < ε) :
    dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ Lbar ε ≤
      (responseCount (upperSchedule p q Δ σ Lbar ε hε) : ℕ∞) := by
  let N := responseCount (upperSchedule p q Δ σ Lbar ε hε)
  have hfeasible : HasDimensionUniformGuarantee.{u, 0}
      N p q Δ σ Lbar ε :=
    strict_k1_shared_batch_ema_uniform_guarantee
      p q Δ σ Lbar ε hp hq hΔ hσ hLbar hε
  change (⨅ (M : ℕ)
    (_ : HasDimensionUniformGuarantee.{u, 0} M p q Δ σ Lbar ε),
      (M : ℕ∞)) ≤ (N : ℕ∞)
  exact (iInf_le _ N).trans (iInf_le _ hfeasible)

/-- The minimax upper response bound retains the public shape and its
dimension-free coefficient from `Main`, with the original response cap. -/
theorem strict_k1_shared_batch_ema_minimax_le_rate
    (p q Δ σ Lbar ε : ℝ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hLbar : 0 < Lbar)
    (hε : 0 < ε) :
    (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ Lbar ε : ENNReal) ≤
      ENNReal.ofReal
        (upperRateConstant p q *
          ((paperS σ ε) ^ (p / (p - 1)) +
            paperAplus Lbar Δ ε *
              max ((paperS σ ε) ^ 2)
                ((paperS σ ε) ^ ((p / (p - 1)) / q)))) := by
  let N := responseCount (upperSchedule p q Δ σ Lbar ε hε)
  have hmin : dimensionUniformMinimaxComplexity.{u, 0}
      p q Δ σ Lbar ε ≤ (N : ℕ∞) :=
    strict_k1_shared_batch_ema_minimax_le_responseCount
      p q Δ σ Lbar ε hp hq hΔ hσ hLbar hε
  have hcount : (N : ℝ) ≤
      upperRateConstant p q *
        ((paperS σ ε) ^ (p / (p - 1)) +
          paperAplus Lbar Δ ε *
            max ((paperS σ ε) ^ 2)
              ((paperS σ ε) ^ ((p / (p - 1)) / q))) := by
    unfold N upperSchedule upperRateConstant
    exact paperSchedule_responseCount_le_rate_max
      p q Δ σ Lbar ε (upperCtail p) (1 / 8) (upperKappa p q)
      (upperCb p q) upperCI hp.1 hp.2 hq hε
      (upperCtail_ge_twelve p hp.1 hp.2)
      (by norm_num) (upperCb_pos p q) upperCI_pos
  have hcast :
      (dimensionUniformMinimaxComplexity.{u, 0}
        p q Δ σ Lbar ε : ENNReal) ≤ (N : ENNReal) :=
    ENat.toENNReal_le.mpr hmin
  calc
    (dimensionUniformMinimaxComplexity.{u, 0}
      p q Δ σ Lbar ε : ENNReal) ≤ (N : ENNReal) := hcast
    _ = ENNReal.ofReal (N : ℝ) := by simp
    _ ≤ ENNReal.ofReal
        (upperRateConstant p q *
          ((paperS σ ε) ^ (p / (p - 1)) +
            paperAplus Lbar Δ ε *
              max ((paperS σ ε) ^ 2)
                ((paperS σ ε) ^ ((p / (p - 1)) / q)))) :=
      ENNReal.ofReal_le_ofReal hcount

end

end HeavyTailedNoise.UpperK1
