import HeavyTailedNoise.Upper.K1.StationaritySourceMeanTelescope

/-!
The first exact error split on the actual complete seed path. The clipped
source estimate is an analysis quantity at the genuine pre-batch query and
center, evaluated with the original independent auxiliary-seed law. It is
never queried by the algorithm.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- The terminal-clipped auxiliary source mean at one actual pre-batch
decision. It names the bias term without defining another estimator update. -/
def actualClippedSourceEstimate {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) : Point d :=
  let H := batchHistoryOfRun P O u
    ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
  batchCenter P u H +
    upperResidualSourceMean O
      (upperClip (P.tau (Fin.last P.J)))
      (batchDecision P u H) (batchCenter P u H)

theorem actualRuntimePoint_eq_batchDecision {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) :
    actualRuntimePoint P O seeds u.val =
      batchDecision P u (batchHistoryOfRun P O u
        ((⟨0, P.T_pos⟩ : Fin P.T), seeds)) := by
  let z : Fin P.T × (Fin (responseCount P) → Seed) :=
    ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
  have hpre := boundaryTranscript_eq_batchHistory P O u z
  simp only [actualRuntimePoint, dif_pos (Nat.le_of_lt u.isLt)]
  rw [hpre]
  rfl

/-- The source term is also the low-band mean plus every high-band mean,
including the `J=0` case. -/
theorem actualClippedSourceEstimate_eq_bandMeans {d : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) :
    let H := batchHistoryOfRun P O u
      ((⟨0, P.T_pos⟩ : Fin P.T), seeds)
    actualClippedSourceEstimate P O seeds u =
      batchCenter P u H +
        (upperResidualSourceMean O (lowBand P)
          (batchDecision P u H) (batchCenter P u H) +
          ∑ j : Fin P.J,
            upperResidualSourceMean O (highBand P j)
              (batchDecision P u H) (batchCenter P u H)) := by
  dsimp only
  unfold actualClippedSourceEstimate
  rw [lowSourceMean_add_highSourceMeans_eq_terminalClip P O]

/-- Exact first split of the genuine completed-estimator error. The first
term still contains shared-batch sampling and high-band memory lag; the
second is precisely terminal clipping bias at the actual decision. -/
theorem actualRuntime_error_eq_centered_plus_terminalBias
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) :
    actualRuntimeEstimate P I.oracle seeds u.val -
        I.objective.grad (actualRuntimePoint P I.oracle seeds u.val) =
      (actualRuntimeEstimate P I.oracle seeds u.val -
        actualClippedSourceEstimate P I.oracle seeds u) +
      (actualClippedSourceEstimate P I.oracle seeds u -
        I.objective.grad (actualRuntimePoint P I.oracle seeds u.val)) := by
  abel

theorem actualRuntime_error_norm_le_centered_plus_terminalBias
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (seeds : Fin (responseCount P) → Seed) (u : Fin P.T) :
    ‖actualRuntimeEstimate P I.oracle seeds u.val -
        I.objective.grad (actualRuntimePoint P I.oracle seeds u.val)‖ ≤
      ‖actualRuntimeEstimate P I.oracle seeds u.val -
        actualClippedSourceEstimate P I.oracle seeds u‖ +
      ‖actualClippedSourceEstimate P I.oracle seeds u -
        I.objective.grad (actualRuntimePoint P I.oracle seeds u.val)‖ := by
  rw [actualRuntime_error_eq_centered_plus_terminalBias P I seeds u]
  exact norm_add_le _ _

end

end HeavyTailedNoise.UpperK1
