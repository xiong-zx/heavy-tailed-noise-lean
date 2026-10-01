import HeavyTailedNoise.Upper.K1.EMADriftActual
import HeavyTailedNoise.Upper.K1.ActualEstimatorKernelIdentity

/-!
The boundary source sequence used to account for the final drift agrees,
on every source index actually read by the finite EMA lag, with the source
means in the canonical estimator-error decomposition.  The final boundary
is an analysis extension only; the algorithm does not query there.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualBandSourceAtBoundary_eq_actualBandSourceMean
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed)
    (j : Fin P.J) (t : ℕ) (ht : t < P.T) :
    actualBandSourceAtBoundary P O j t
        ((⟨0, P.T_pos⟩ : Fin P.T), seeds) =
      actualBandSourceMean P O seeds j t := by
  let u : Fin P.T := ⟨t, ht⟩
  have hstart := actualBandSourceAtBoundary_eq_batchStart P O j u
    ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
  rw [actualBandSourceMean, dif_pos ht]
  exact hstart

/-- All actual runtime EMA lags use only source boundaries `0,…,T−1`;
therefore the bounded boundary extension agrees exactly with the existing
estimator decomposition at every `t<T`. -/
theorem actualMeanLag_eq_boundarySourceLag
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed)
    (t : ℕ) (ht : t < P.T) :
    actualMeanLag P O seeds t =
      aggregateMeanLag P
        (actualBandSourceSequence P O
          ((⟨0, P.T_pos⟩ : Fin P.T), seeds)) t := by
  let z : Fin P.T × (Fin (responseCount P) → Seed) :=
    ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
  let μold : Fin P.J → ℕ → Point d :=
    fun j v => actualBandSourceMean P O seeds j (v - 1)
  let μnew := actualBandSourceSequence P O z
  change aggregateMeanLag P μold t = aggregateMeanLag P μnew t
  rw [aggregateMeanLag_eq_source_moves P μold t,
    aggregateMeanLag_eq_source_moves P μnew t]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro j hj
  have hut : u < t := Finset.mem_range.mp hu
  have hu0 : u < P.T := by omega
  have hu1 : u + 1 < P.T := by omega
  have hfirst : μnew j (u + 1) =
      actualBandSourceMean P O seeds j u := by
    change actualBandSourceAtBoundary P O j u z = _
    exact actualBandSourceAtBoundary_eq_actualBandSourceMean
      P O seeds j u hu0
  have hsecond : μnew j (u + 2) =
      actualBandSourceMean P O seeds j (u + 1) := by
    change actualBandSourceAtBoundary P O j (u + 1) z = _
    exact actualBandSourceAtBoundary_eq_actualBandSourceMean
      P O seeds j (u + 1) hu1
  simp only [μold, Nat.add_sub_cancel, hfirst, hsecond]
  have hidx : u + 2 - 1 = u + 1 := by omega
  rw [hidx]

end

end HeavyTailedNoise.UpperK1
