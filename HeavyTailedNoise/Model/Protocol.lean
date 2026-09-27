import HeavyTailedNoise.Model.Basic

open MeasureTheory

noncomputable section

namespace HeavyTailedNoise

theorem measurable_runTranscript {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private] {N : ℕ}
    (O : GradientOracle d Seed) (A : RandomAlgorithm d N Private) (n : ℕ) :
    Measurable (fun z : Private × (Fin n → Seed) =>
      runTranscript O A z.1 n z.2) := by
  induction n with
  | zero =>
      refine measurable_pi_iff.mpr ?_
      intro i
      exact i.elim0
  | succ n ih =>
      have hprefix : Measurable (fun z : Private × (Fin (n + 1) → Seed) =>
          (z.1, fun i : Fin n => z.2 i.castSucc)) :=
        measurable_fst.prodMk <| measurable_pi_iff.mpr fun i =>
          (measurable_pi_apply i.castSucc).comp measurable_snd
      have hhistory : Measurable (fun z : Private × (Fin (n + 1) → Seed) =>
          runTranscript O A z.1 n (fun i => z.2 i.castSucc)) :=
        ih.comp hprefix
      have hx : Measurable (fun z : Private × (Fin (n + 1) → Seed) =>
          A.decide n z.1 (runTranscript O A z.1 n (fun i => z.2 i.castSucc))) :=
        (A.measurable_decide n).comp (measurable_fst.prodMk hhistory)
      have hy : Measurable (fun z : Private × (Fin (n + 1) → Seed) =>
          O.response (A.decide n z.1
            (runTranscript O A z.1 n (fun i => z.2 i.castSucc)))
            (z.2 (Fin.last n))) :=
        O.measurable_response.comp <|
          hx.prodMk ((measurable_pi_apply (Fin.last n)).comp measurable_snd)
      refine measurable_pi_iff.mpr ?_
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [runTranscript, Fin.snoc_last] using hx.prodMk hy
      · simpa only [runTranscript, Fin.snoc_castSucc, Function.comp_def] using
          (measurable_pi_apply j).comp hhistory

theorem measurable_runOutput {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private] {N : ℕ}
    (O : GradientOracle d Seed) (A : RandomAlgorithm d N Private) :
    Measurable (fun z : Private × (Fin N → Seed) =>
      A.output z.1 (runTranscript O A z.1 N z.2)) :=
  A.measurable_output.comp (measurable_fst.prodMk (measurable_runTranscript O A N))

/-- The independent fresh-seed product law is a probability measure. -/
theorem freshSeedLaw_probability {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (N : ℕ) :
    IsProbabilityMeasure (freshSeedLaw O N) := by
  haveI : IsProbabilityMeasure O.law := O.law_probability
  unfold freshSeedLaw
  infer_instance

/-- The extended nonnegative risk integrand is measurable even when its
integral is infinite. -/
theorem measurable_riskValue {d N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (A : RandomAlgorithm d N Private) :
    Measurable (fun z : Private × (Fin N → Seed) =>
      ENNReal.ofReal ‖I.objective.grad
        (A.output z.1 (runTranscript I.oracle A z.1 N z.2))‖) :=
  ENNReal.measurable_ofReal.comp
    ((I.objective.continuous_grad.measurable.comp
      (measurable_runOutput I.oracle A)).norm)

/-- At round `n`, the decision precedes the fresh-seed response. -/
theorem runTranscript_last {d N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private]
    (O : GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (r : Private) (n : ℕ) (seeds : Fin (n + 1) → Seed) :
    runTranscript O A r (n + 1) seeds (Fin.last n) =
      let history := runTranscript O A r n (fun i => seeds i.castSucc)
      let x := A.decide n r history
      (x, O.response x (seeds (Fin.last n))) := by
  simp [runTranscript]

/-- Extending a run by one fresh response leaves its prior transcript intact. -/
theorem runTranscript_prefix {d N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private]
    (O : GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (r : Private) (n : ℕ) (seeds : Fin (n + 1) → Seed) (i : Fin n) :
    runTranscript O A r (n + 1) seeds i.castSucc =
      runTranscript O A r n (fun j => seeds j.castSucc) i := by
  simp [runTranscript]

/-- The complete decision path has exactly `N` responsive query positions and
one additional, response-free output position. -/
def decisionPath {d N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private]
    (O : GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (r : Private) (seeds : Fin N → Seed) : Fin (N + 1) → Point d :=
  Fin.snoc (fun i => (runTranscript O A r N seeds i).1)
    (A.output r (runTranscript O A r N seeds))

theorem decisionPath_query {d N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private]
    (O : GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (r : Private) (seeds : Fin N → Seed) (i : Fin N) :
    decisionPath O A r seeds i.castSucc = (runTranscript O A r N seeds i).1 := by
  simp [decisionPath]

theorem decisionPath_output {d N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private]
    (O : GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (r : Private) (seeds : Fin N → Seed) :
    decisionPath O A r seeds (Fin.last N) =
      A.output r (runTranscript O A r N seeds) := by
  simp [decisionPath]

theorem measurable_decisionPath {d N : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Private : Type*} [MeasurableSpace Private]
    (O : GradientOracle d Seed) (A : RandomAlgorithm d N Private) :
    Measurable (fun z : Private × (Fin N → Seed) => decisionPath O A z.1 z.2) := by
  refine measurable_pi_iff.mpr ?_
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [decisionPath_output] using measurable_runOutput O A
  · simpa only [decisionPath_query, Function.comp_def] using
      (measurable_fst.comp <| (measurable_pi_apply j).comp
        (measurable_runTranscript O A N))

end HeavyTailedNoise
