import HeavyTailedNoise.Upper.K1.Algorithm
import HeavyTailedNoise.Model.Protocol

/-!
The private `Fin T` index selects a previously queried runtime batch start.
It does not affect the transcript or cause another oracle response. All risk
identities use `ENNReal`, so a selected gradient may have infinite risk.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ}

/-- The sole private random index is not read by any query decision, so fixed
oracle seeds yield the same complete transcript for any two indices. -/
theorem runTranscript_private_independent {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (P : Schedule q) (O : GradientOracle d Seed)
    (r r' : Fin P.T) :
    ∀ n (seeds : Fin n → Seed),
      runTranscript O (algorithm (d := d) P) r n seeds =
        runTranscript O (algorithm (d := d) P) r' n seeds := by
  intro n
  induction n with
  | zero =>
      intro seeds
      rfl
  | succ n ih =>
      intro seeds
      simp [runTranscript, algorithm_decide, ih]

/-- The output is the decision at a runtime batch start, reconstructed from
the same seed path with a fixed private anchor. Thus output selection costs no
additional oracle response. -/
theorem algorithm_output_canonical_query {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (P : Schedule q) (O : GradientOracle d Seed)
    (r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
    (algorithm (d := d) P).output r
      (runTranscript O (algorithm (d := d) P) r (responseCount P) seeds) =
      query P (batchStart P r.val)
        (runTranscript O (algorithm (d := d) P)
          (⟨0, P.T_pos⟩ : Fin P.T) (batchStart P r.val)
          (fun j : Fin (batchStart P r.val) =>
            seeds ⟨j.val, lt_trans j.isLt (outputIndex P r).isLt⟩)) := by
  rw [algorithm_output_actual_query P O r seeds]
  congr 1
  exact runTranscript_private_independent P O r (⟨0, P.T_pos⟩ : Fin P.T)
    (batchStart P r.val)
    (fun j : Fin (batchStart P r.val) =>
      seeds ⟨j.val, lt_trans j.isLt (outputIndex P r).isLt⟩)

private theorem uniform_fin_singleton_weight (P : Schedule q) (r : Fin P.T) :
    uniformOn (Set.univ : Set (Fin P.T)) ({r} : Set (Fin P.T)) =
      (P.T : ENNReal)⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton]
  simp [Fintype.card_fin, one_div]

/-- Exact risk as the uniform average of extended-nonnegative gradient risks
at all runtime batch-start decisions. The seed law remains the original fresh
response law, and no gradient-integrability hypothesis is required. -/
theorem risk_eq_uniform_runtime_start_lintegrals
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (P : Schedule q) :
    risk I (algorithm (d := d) P) =
      ∑ r : Fin P.T,
        (∫⁻ seeds : Fin (responseCount P) → Seed,
          ENNReal.ofReal ‖I.objective.grad
            (query P (batchStart P r.val)
              (runTranscript I.oracle (algorithm (d := d) P)
                (⟨0, P.T_pos⟩ : Fin P.T) (batchStart P r.val)
                (fun j : Fin (batchStart P r.val) =>
                  seeds ⟨j.val, lt_trans j.isLt (outputIndex P r).isLt⟩)))‖
          ∂freshSeedLaw I.oracle (responseCount P)) *
            (P.T : ENNReal)⁻¹ := by
  let A : RandomAlgorithm d (responseCount P) (Fin P.T) := algorithm P
  change (∫⁻ r : Fin P.T,
    ∫⁻ seeds : Fin (responseCount P) → Seed,
      ENNReal.ofReal ‖I.objective.grad
        (A.output r (runTranscript I.oracle A r (responseCount P) seeds))‖
      ∂freshSeedLaw I.oracle (responseCount P)
    ∂A.privateLaw) = _
  have hpoint (r : Fin P.T) (seeds : Fin (responseCount P) → Seed) :
      A.output r (runTranscript I.oracle A r (responseCount P) seeds) =
        query P (batchStart P r.val)
          (runTranscript I.oracle A (⟨0, P.T_pos⟩ : Fin P.T)
            (batchStart P r.val)
            (fun j : Fin (batchStart P r.val) =>
              seeds ⟨j.val, lt_trans j.isLt (outputIndex P r).isLt⟩)) :=
    algorithm_output_canonical_query P I.oracle r seeds
  simp_rw [hpoint]
  change (∫⁻ r : Fin P.T,
    ∫⁻ seeds : Fin (responseCount P) → Seed,
      ENNReal.ofReal ‖I.objective.grad
        (query P (batchStart P r.val)
          (runTranscript I.oracle A (⟨0, P.T_pos⟩ : Fin P.T)
            (batchStart P r.val)
            (fun j : Fin (batchStart P r.val) =>
              seeds ⟨j.val, lt_trans j.isLt (outputIndex P r).isLt⟩)))‖
      ∂freshSeedLaw I.oracle (responseCount P)
    ∂uniformOn Set.univ) = _
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro r hr
  rw [uniform_fin_singleton_weight P r]

end

end HeavyTailedNoise.UpperK1
