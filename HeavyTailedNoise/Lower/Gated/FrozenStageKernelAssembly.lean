import HeavyTailedNoise.Lower.Gated.FrozenStageMeanBridge
import HeavyTailedNoise.Lower.Gated.FrozenStageGaussianKL

/-!
Fixed-horizon Gaussian information for two frozen prefix stages.  The history
space and its common update are arbitrary measurable objects; no stopping-time
identification is asserted here.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

namespace HeavyTailedNoise

/-- The actual truncated gradient evaluated at an arbitrary history-measurable
query. -/
def frozenStageHistoryMean {H : Type*} [MeasurableSpace H]
    {d T : ℕ} (U : Fin T → Point d) (j : Fin T)
    (q : ℕ → H → Point d) (t : ℕ) (h : H) : Point d :=
  gradient (prefixHardPotential U j) (q t h)

lemma measurable_frozenStageHistoryMean
    {H : Type*} [MeasurableSpace H] {d T : ℕ}
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (q : ℕ → H → Point d) (hq : ∀ t, Measurable (q t))
    (t : ℕ) : Measurable (frozenStageHistoryMean U j q t) := by
  exact measurable_frozenPrefixMean_comp hT j
    (fun _ : H => U) measurable_const (q t) (hq t)

/-- The existing additive Gaussian response law as a history kernel, with
the true frozen gradient as mean. -/
def frozenStageHistoryKernel
    {H : Type*} [MeasurableSpace H] {d T : ℕ}
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (q : ℕ → H → Point d) (hq : ∀ t, Measurable (q t))
    (a : ℝ) : ℕ → Kernel H (Point d) :=
  fun t => gaussianMeanKernel d
    (frozenStageHistoryMean U j q t)
    (measurable_frozenStageHistoryMean hT U j q hq t) a

lemma frozenStageHistoryKernel_markov
    {H : Type*} [MeasurableSpace H] {d T : ℕ}
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (q : ℕ → H → Point d) (hq : ∀ t, Measurable (q t))
    (a : ℝ) (t : ℕ) :
    IsMarkovKernel (frozenStageHistoryKernel hT U j q hq a t) := by
  exact gaussianMeanKernel_markov d
    (frozenStageHistoryMean U j q t)
    (measurable_frozenStageHistoryMean hT U j q hq t) a

lemma frozenStageHistoryKernel_apply
    {H : Type*} [MeasurableSpace H] {d T : ℕ}
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (q : ℕ → H → Point d) (hq : ∀ t, Measurable (q t))
    (a : ℝ) (t : ℕ) (h : H) :
    frozenStageHistoryKernel hT U j q hq a t h =
      gaussianResponseLaw d (frozenStageHistoryMean U j q t h) a := by
  exact gaussianMeanKernel_apply d
    (frozenStageHistoryMean U j q t)
    (measurable_frozenStageHistoryMean hT U j q hq t) a h

lemma frozenStageHistoryMean_diameter
    {H : Type*} [MeasurableSpace H] {d T : ℕ}
    {U V : Fin T → Point d} (hU : Orthonormal ℝ U)
    (hV : Orthonormal ℝ V) (j : Fin T)
    (hpre : ∀ i, i < j → U i = V i)
    (q : ℕ → H → Point d) (t : ℕ) (h : H) :
    ‖frozenStageHistoryMean U j q t h -
      frozenStageHistoryMean V j q t h‖ ≤ 300 :=
  norm_gradient_prefixHardPotential_sub_le_300 hU hV j hpre (q t h)

/-- Fixed-response-cap KL for two orthonormal frames agreeing before the
current frozen column.  Both laws use the same initial state and update. -/
theorem frozenStage_adaptiveGaussianLaw_klDiv_le
    {H : Type*} [MeasurableSpace H]
    {d T : ℕ} [MeasurableSpace.CountableOrCountablyGenerated H (Point d)]
    (hd : 0 < d) (hT : 0 < T)
    {U V : Fin T → Point d} (hU : Orthonormal ℝ U)
    (hV : Orthonormal ℝ V) (j : Fin T)
    (hpre : ∀ i, i < j → U i = V i)
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀)
    (q : ℕ → H → Point d) (hq : ∀ t, Measurable (q t))
    (P₀ : Measure H) [IsProbabilityMeasure P₀]
    (update : ℕ → H × Point d → H)
    (hUpdate : ∀ t, Measurable (update t)) (n : ℕ) :
    klDiv
      (adaptiveGaussianLaw d P₀
        (frozenStageHistoryKernel hT U j q hq (σ₀ / Real.sqrt d))
        update n)
      (adaptiveGaussianLaw d P₀
        (frozenStageHistoryKernel hT V j q hq (σ₀ / Real.sqrt d))
        update n) ≤
      (n : ENNReal) * ENNReal.ofReal
        ((d : ℝ) * (300 : ℝ) ^ 2 / (2 * σ₀ ^ 2)) := by
  exact adaptiveGaussianLaw_klDiv_le d hd σ₀ hσ₀ 300 P₀
    (frozenStageHistoryKernel hT U j q hq (σ₀ / Real.sqrt d))
    (frozenStageHistoryKernel hT V j q hq (σ₀ / Real.sqrt d))
    (fun t => frozenStageHistoryKernel_markov hT U j q hq
      (σ₀ / Real.sqrt d) t)
    (fun t => frozenStageHistoryKernel_markov hT V j q hq
      (σ₀ / Real.sqrt d) t)
    (frozenStageHistoryMean U j q)
    (frozenStageHistoryMean V j q)
    (fun t h => frozenStageHistoryKernel_apply hT U j q hq
      (σ₀ / Real.sqrt d) t h)
    (fun t h => frozenStageHistoryKernel_apply hT V j q hq
      (σ₀ / Real.sqrt d) t h)
    (fun t h => frozenStageHistoryMean_diameter hU hV j hpre q t h)
    update hUpdate n

end HeavyTailedNoise
