import HeavyTailedNoise.Upper.Foundations.ClippedBatch

/-!
The exact vector variance of one fresh finite batch. A single transformed
response may contain several correlated clipping bands: independence is used
only between distinct seed coordinates. The positive batch-size premise is
supplied when the optional initialization batch is actually drawn.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The centered vector batch mean has one-source centered second moment
divided by the batch size. The transform can combine every high band of one
response, so this does not split or discard same-seed cross terms. -/
theorem upperResidualBatchMean_secondMoment_eq_source
    {d m : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (φ : Point d → Point d)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ z, ‖φ z‖ ≤ C)
    (x w : Point d) (hm : 0 < m) :
    (∫ seeds : Fin m → Seed,
      ‖upperResidualBatchMean O φ x w seeds -
        upperResidualSourceMean O φ x w‖ ^ 2
      ∂freshSeedLaw O m) =
      (m : ℝ)⁻¹ * ∫ ξ : Seed,
        ‖φ (O.response x ξ - w) -
          upperResidualSourceMean O φ x w‖ ^ 2 ∂O.law := by
  letI : IsProbabilityMeasure O.law := O.law_probability
  let f : Seed → Point d := fun ξ => φ (O.response x ξ - w)
  let a : Point d := upperResidualSourceMean O φ x w
  have hfInt : Integrable f O.law :=
    upperResidualSource_integrable O φ hφ C hC x w
  have hfMeas : Measurable f := by
    have hresponse : Measurable (O.response x) :=
      O.measurable_response.comp (measurable_const.prodMk measurable_id)
    exact hφ.comp (hresponse.sub measurable_const)
  have hcoordMean (k : Fin d) :
      (∫ ξ, (f ξ) k ∂O.law) = a k := by
    let projk : Point d →L[ℝ] ℝ :=
      PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k
    have hproj := projk.integral_comp_comm hfInt
    simpa [projk, f, a, upperResidualSourceMean] using hproj
  have hcoordMem (k : Fin d) :
      MemLp (fun ξ => (f ξ) k) 2 O.law := by
    have hkMeas : Measurable (fun ξ => (f ξ) k) :=
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) k).measurable.comp
        hfMeas
    have hkBound (ξ : Seed) : ‖(f ξ) k‖ ≤ C :=
      (PiLp.norm_apply_le (f ξ) k).trans (hC _)
    exact MemLp.of_bound hkMeas.aestronglyMeasurable C
      (Filter.Eventually.of_forall hkBound)
  have hcoordSq (k : Fin d) : Integrable
      (fun ξ => ((f ξ - a) k) ^ 2) O.law := by
    have h := ((hcoordMem k).sub (memLp_const (a k))).integrable_sq
    simpa [PiLp.sub_apply] using h
  have hsource :
      (∑ k : Fin d,
        variance (fun ξ => (f ξ) k) O.law) =
      ∫ ξ : Seed, ‖f ξ - a‖ ^ 2 ∂O.law := by
    calc
      (∑ k : Fin d, variance (fun ξ => (f ξ) k) O.law) =
          ∑ k : Fin d, ∫ ξ : Seed, ((f ξ - a) k) ^ 2 ∂O.law := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [variance_eq_integral (hcoordMem k).aemeasurable]
            simp only [PiLp.sub_apply, hcoordMean k]
      _ = ∫ ξ : Seed, ∑ k : Fin d, ((f ξ - a) k) ^ 2 ∂O.law := by
            rw [integral_finsetSum]
            intro k hk
            exact hcoordSq k
      _ = ∫ ξ : Seed, ‖f ξ - a‖ ^ 2 ∂O.law := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun ξ =>
              (EuclideanSpace.real_norm_sq_eq (f ξ - a)).symm)
  rw [upperResidualBatchMean_secondMoment O φ hφ C hC x w hm]
  exact congrArg (fun v : ℝ => (m : ℝ)⁻¹ * v) hsource

end

end HeavyTailedNoise
