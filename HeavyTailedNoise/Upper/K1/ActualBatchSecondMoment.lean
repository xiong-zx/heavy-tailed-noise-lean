import HeavyTailedNoise.Upper.K1.ActualBatchStatistics

/-!
The whole shared-`Φ_k` runtime-batch error has a square-integrable norm on
the actual path. The bound retains all within-response correlation among
clipping scales and requires no raw-residual second moment.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem kernelBatchErrorAtHistory_memLp_two {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ) :
    MemLp (kernelBatchErrorAtHistory P O u k) 2
      ((batchPastHistoryLaw P O u).prod (freshSeedLaw O P.n)) := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (batchPastHistoryLaw P O u) := by
    unfold batchPastHistoryLaw
    infer_instance
  letI : IsProbabilityMeasure (freshSeedLaw O P.n) :=
    freshSeedLaw_probability O P.n
  let μ := (batchPastHistoryLaw P O u).prod (freshSeedLaw O P.n)
  let x : BatchHistory P d u → Point d := batchDecision P u
  let w : BatchHistory P d u → Point d := batchCenter P u
  let φ : Point d → Point d := kernelPhi P k
  let C : ℝ := kernelPhiBound P k
  have hcoord (i : Fin P.n) : MemLp
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        φ (O.response (x z.1) (z.2 i) - w z.1)) 2 μ := by
    have hm : Measurable (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        φ (O.response (x z.1) (z.2 i) - w z.1)) :=
      (measurable_kernelPhi P k).comp
        ((O.measurable_response.comp
          (((measurable_batchDecision P u).comp measurable_fst).prodMk
            ((measurable_pi_apply i).comp measurable_snd))).sub
              ((measurable_batchCenter P u).comp measurable_fst))
    exact MemLp.of_bound hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun z => kernelPhi_norm_le P k _))
  have hsum : MemLp
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        ∑ i : Fin P.n, φ (O.response (x z.1) (z.2 i) - w z.1)) 2 μ := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    exact hcoord i
  have hbatch : MemLp
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        upperResidualBatchMean O φ (x z.1) (w z.1) z.2) 2 μ := by
    have hrepr : (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        upperResidualBatchMean O φ (x z.1) (w z.1) z.2) =
        (P.n : ℝ)⁻¹ • (fun z =>
          ∑ i : Fin P.n, φ (O.response (x z.1) (z.2 i) - w z.1)) := by
      funext z
      rfl
    rw [hrepr]
    exact hsum.const_smul (P.n : ℝ)⁻¹
  have hsourceMeas : Measurable
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        upperResidualSourceMean O φ (x z.1) (w z.1)) :=
    (measurable_upperResidualSourceMean O φ (measurable_kernelPhi P k)
      x w (measurable_batchDecision P u) (measurable_batchCenter P u)).comp
        measurable_fst
  have hsourceBound (H : BatchHistory P d u) :
      ‖upperResidualSourceMean O φ (x H) (w H)‖ ≤ C := by
    unfold upperResidualSourceMean
    have hprob : O.law.real Set.univ = 1 := by simp
    simpa only [φ, C, hprob, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := O.law)
        (Filter.Eventually.of_forall (fun ξ =>
          kernelPhi_norm_le P k (O.response (x H) ξ - w H))))
  have hsource : MemLp
      (fun z : BatchHistory P d u × (Fin P.n → Seed) =>
        upperResidualSourceMean O φ (x z.1) (w z.1)) 2 μ :=
    MemLp.of_bound hsourceMeas.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun z => hsourceBound z.1))
  have herr := hbatch.sub hsource
  apply herr.congr_norm
    (measurable_kernelBatchErrorAtHistory P O u k).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    simp only [kernelBatchErrorAtHistory, x, w, φ, Pi.sub_apply])

theorem kernelBatchErrorAtHistory_sq_integrable {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T) (k : ℕ) :
    Integrable (fun z => ‖kernelBatchErrorAtHistory P O u k z‖ ^ 2)
      ((batchPastHistoryLaw P O u).prod (freshSeedLaw O P.n)) :=
  ((kernelBatchErrorAtHistory_memLp_two P O u k).norm).integrable_sq

end

end HeavyTailedNoise.UpperK1
