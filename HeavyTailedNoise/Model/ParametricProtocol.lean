import HeavyTailedNoise.Model.Basic

/-!
Joint measurability of the full-history strict-K=1 protocol when the oracle
depends on a hidden frame. The algorithm sees only gradient responses; the
frame and seed coordinates appear here solely as probability-space variables.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

theorem measurable_parametric_runTranscript
    {d N : ℕ} {Frame Seed Private : Type*}
    [MeasurableSpace Frame] [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : Frame → GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (hresponse : Measurable
      (fun z : Frame × (Point d × Seed) => (O z.1).response z.2.1 z.2.2))
    (n : ℕ) :
    Measurable (fun z : Frame × (Private × (Fin n → Seed)) =>
      runTranscript (O z.1) A z.2.1 n z.2.2) := by
  induction n with
  | zero =>
      refine measurable_pi_iff.mpr ?_
      intro i
      exact i.elim0
  | succ n ih =>
      have hprefix : Measurable
          (fun z : Frame × (Private × (Fin (n + 1) → Seed)) =>
            (z.1, (z.2.1, fun i : Fin n => z.2.2 i.castSucc))) :=
        measurable_fst.prodMk <|
          (measurable_fst.comp measurable_snd).prodMk <|
            measurable_pi_iff.mpr fun i =>
              (measurable_pi_apply i.castSucc).comp
                (measurable_snd.comp measurable_snd)
      have hhistory : Measurable
          (fun z : Frame × (Private × (Fin (n + 1) → Seed)) =>
            runTranscript (O z.1) A z.2.1 n
              (fun i => z.2.2 i.castSucc)) :=
        ih.comp hprefix
      have hx : Measurable
          (fun z : Frame × (Private × (Fin (n + 1) → Seed)) =>
            A.decide n z.2.1
              (runTranscript (O z.1) A z.2.1 n
                (fun i => z.2.2 i.castSucc))) :=
        (A.measurable_decide n).comp
          ((measurable_fst.comp measurable_snd).prodMk hhistory)
      have hseed : Measurable
          (fun z : Frame × (Private × (Fin (n + 1) → Seed)) =>
            z.2.2 (Fin.last n)) :=
        (measurable_pi_apply (Fin.last n)).comp
          (measurable_snd.comp measurable_snd)
      have hy : Measurable
          (fun z : Frame × (Private × (Fin (n + 1) → Seed)) =>
            (O z.1).response
              (A.decide n z.2.1
                (runTranscript (O z.1) A z.2.1 n
                  (fun i => z.2.2 i.castSucc)))
              (z.2.2 (Fin.last n))) :=
        hresponse.comp (measurable_fst.prodMk (hx.prodMk hseed))
      refine measurable_pi_iff.mpr ?_
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [runTranscript, Fin.snoc_last] using hx.prodMk hy
      · simpa only [runTranscript, Fin.snoc_castSucc, Function.comp_def] using
          (measurable_pi_apply j).comp hhistory

theorem measurable_parametric_runOutput
    {d N : ℕ} {Frame Seed Private : Type*}
    [MeasurableSpace Frame] [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : Frame → GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (hresponse : Measurable
      (fun z : Frame × (Point d × Seed) => (O z.1).response z.2.1 z.2.2)) :
    Measurable (fun z : Frame × (Private × (Fin N → Seed)) =>
      A.output z.2.1
        (runTranscript (O z.1) A z.2.1 N z.2.2)) :=
  A.measurable_output.comp <|
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_parametric_runTranscript O A hresponse N)

theorem measurable_parametric_riskValue
    {d N : ℕ} {Frame Seed Private : Type*}
    [MeasurableSpace Frame] [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ Lbar : ℝ}
    (I : Frame → Admissible d Seed p q Δ σ Lbar)
    (A : RandomAlgorithm d N Private)
    (hresponse : Measurable
      (fun z : Frame × (Point d × Seed) =>
        (I z.1).oracle.response z.2.1 z.2.2))
    (hgrad : Measurable
      (fun z : Frame × Point d => (I z.1).objective.grad z.2)) :
    Measurable (fun z : Frame × (Private × (Fin N → Seed)) =>
      ENNReal.ofReal ‖(I z.1).objective.grad
        (A.output z.2.1
          (runTranscript (I z.1).oracle A z.2.1 N z.2.2))‖) :=
  ENNReal.measurable_ofReal.comp <|
    (hgrad.comp <|
      measurable_fst.prodMk
        (measurable_parametric_runOutput
          (fun U => (I U).oracle) A hresponse)).norm

end

end HeavyTailedNoise
