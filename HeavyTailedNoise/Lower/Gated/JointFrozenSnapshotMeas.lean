import HeavyTailedNoise.Lower.Gated.NextDirectionFrozenKernel

/-!
Joint measurability of the existing frozen full-history Gaussian continuation
in the revealed prefix, stopped snapshot, candidate next direction, and
unobserved finite Gaussian tail.  Snapshots use the already established
`Bool × ℕ × Transcript d N × Point d` representation.  The continuation is
the same `actualFrozenGaussianSeedState`, including its response-cap update.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Canonical inverse of the existing stopped-record tuple representation. -/
def idealPreResponseHistoryOfTuple {d N : ℕ}
    (s : Bool × ℕ × Transcript d N × Point d) :
    IdealPreResponseHistory d N :=
  ⟨s.1, s.2.1, s.2.2.1, s.2.2.2⟩

@[simp] theorem idealPreResponseTuple_ofTuple {d N : ℕ}
    (s : Bool × ℕ × Transcript d N × Point d) :
    idealPreResponseTuple (idealPreResponseHistoryOfTuple s) = s := rfl

@[simp] theorem idealPreResponseHistoryOfTuple_tuple {d N : ℕ}
    (s : IdealPreResponseHistory d N) :
    idealPreResponseHistoryOfTuple (idealPreResponseTuple s) = s := by
  cases s
  rfl

/-- Parameter-dependent initial state, response mean, and update preserve
joint measurability of the single existing Gaussian state recursion. -/
theorem measurable_joint_gaussianSeedState_parametric_initial
    {Θ H : Type*} [MeasurableSpace Θ] [MeasurableSpace H]
    (d : ℕ) (h₀ : Θ → H) (hh₀ : Measurable h₀)
    (mean : Θ → ℕ → H → Point d)
    (hmean : ∀ t, Measurable (fun z : Θ × H => mean z.1 t z.2))
    (a : ℝ) (update : Θ → ℕ → H × Point d → H)
    (hUpdate : ∀ t, Measurable
      (fun z : Θ × (H × Point d) => update z.1 t z.2)) :
    ∀ n, Measurable (fun z : Θ × (Fin n → Point d) =>
      gaussianSeedState d (h₀ z.1) (mean z.1) a (update z.1) n z.2) := by
  intro n
  induction n with
  | zero =>
      exact hh₀.comp measurable_fst
  | succ n ih =>
      have hprefix : Measurable (fun z : Θ × (Fin (n + 1) → Point d) =>
          (z.1, fun i : Fin n => z.2 i.castSucc)) := by
        apply measurable_fst.prodMk
        apply measurable_pi_iff.mpr
        intro i
        exact (measurable_pi_apply i.castSucc).comp measurable_snd
      have hstate : Measurable (fun z : Θ × (Fin (n + 1) → Point d) =>
          gaussianSeedState d (h₀ z.1) (mean z.1) a (update z.1) n
            (fun i => z.2 i.castSucc)) := ih.comp hprefix
      have hm : Measurable (fun z : Θ × (Fin (n + 1) → Point d) =>
          mean z.1 n
            (gaussianSeedState d (h₀ z.1) (mean z.1) a (update z.1) n
              (fun i => z.2 i.castSucc))) :=
        (hmean n).comp (measurable_fst.prodMk hstate)
      have hnoise : Measurable (fun z : Θ × (Fin (n + 1) → Point d) =>
          a • z.2 (Fin.last n)) := by fun_prop
      have hresponse : Measurable (fun z : Θ × (Fin (n + 1) → Point d) =>
          mean z.1 n
            (gaussianSeedState d (h₀ z.1) (mean z.1) a (update z.1) n
              (fun i => z.2 i.castSucc)) + a • z.2 (Fin.last n)) :=
        hm.add hnoise
      have hpair := measurable_fst.prodMk (hstate.prodMk hresponse)
      simpa only [gaussianSeedState, Function.comp_def] using
        (hUpdate n).comp hpair

/-- The existing query is jointly measurable in the stopped tuple and the
complete current transcript, including the selected first query and output. -/
theorem measurable_joint_actualFrozenQuery_tuple
    {d N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm d N Private) (r : Private) (t : ℕ) :
    Measurable (fun z :
        (Bool × ℕ × Transcript d N × Point d) × Transcript d N =>
      actualFrozenQuery A r (idealPreResponseHistoryOfTuple z.1) t z.2) := by
  classical
  have hslices : Measurable (fun z : (Bool × ℕ) ×
      ((Transcript d N × Point d) × Transcript d N) =>
      actualFrozenQuery A r
        (idealPreResponseHistoryOfTuple
          (z.1.1, z.1.2, z.2.1.1, z.2.1.2)) t z.2.2) := by
    apply measurable_from_prod_countable_right
    rintro ⟨b, k⟩
    by_cases ha : b = true ∧ k + t < N
    · by_cases ht : t = 0
      · have hk : k < N := by simpa [ht] using ha.2
        simpa [actualFrozenQuery, actualFrozenActive,
          idealPreResponseHistoryOfTuple, ha.1, ht, hk, Function.comp_def] using
          (measurable_snd.comp measurable_fst : Measurable
            (fun z : (Transcript d N × Point d) × Transcript d N => z.1.2))
      · have hp : Measurable (fun z :
            (Transcript d N × Point d) × Transcript d N =>
          fun i : Fin (k + t) => z.2 ⟨i.val, lt_trans i.isLt ha.2⟩) := by
          apply measurable_pi_iff.mpr
          intro i
          exact (measurable_pi_apply
            (⟨i.val, lt_trans i.isLt ha.2⟩ : Fin N)).comp measurable_snd
        have hq : Measurable (fun z :
            (Transcript d N × Point d) × Transcript d N =>
          A.decide (k + t) r
            (actualFrozenPast
              (idealPreResponseHistoryOfTuple (b, k, z.1.1, z.1.2))
              t ha.2 z.2)) :=
          (A.measurable_decide (k + t)).comp
            ((measurable_const : Measurable (fun _ :
              (Transcript d N × Point d) × Transcript d N => r)).prodMk hp)
        simpa [actualFrozenQuery, actualFrozenActive,
          idealPreResponseHistoryOfTuple, ha, ht,
          Function.comp_def] using hq
    · have hq : Measurable (fun z :
          (Transcript d N × Point d) × Transcript d N => A.output r z.2) :=
        A.measurable_output.comp (measurable_const.prodMk measurable_snd)
      simpa [actualFrozenQuery, actualFrozenActive,
        idealPreResponseHistoryOfTuple, ha, Function.comp_def] using hq
  have hinput : Measurable (fun z :
      (Bool × ℕ × Transcript d N × Point d) × Transcript d N =>
      ((z.1.1, z.1.2.1), ((z.1.2.2.1, z.1.2.2.2), z.2))) := by fun_prop
  exact hslices.comp hinput

/-- The response-cap update is jointly measurable in the stopped tuple and
the current full transcript/response pair. -/
theorem measurable_joint_actualFrozenUpdate_tuple
    {d N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (A : RandomAlgorithm d N Private) (r : Private) (t : ℕ) :
    Measurable (fun z :
        (Bool × ℕ × Transcript d N × Point d) ×
          (Transcript d N × Point d) =>
      actualFrozenUpdate A r (idealPreResponseHistoryOfTuple z.1) t z.2) := by
  classical
  have hslices : Measurable (fun z : (Bool × ℕ) ×
      ((Transcript d N × Point d) × (Transcript d N × Point d)) =>
      actualFrozenUpdate A r
        (idealPreResponseHistoryOfTuple
          (z.1.1, z.1.2, z.2.1.1, z.2.1.2)) t z.2.2) := by
    apply measurable_from_prod_countable_right
    rintro ⟨b, k⟩
    by_cases ha : b = true ∧ k + t < N
    · have hinput : Measurable (fun z :
          (Transcript d N × Point d) × (Transcript d N × Point d) =>
          ((b, k, z.1.1, z.1.2), z.2.1)) := by fun_prop
      have hq := (measurable_joint_actualFrozenQuery_tuple A r t).comp hinput
      have hpair := (measurable_fst.comp measurable_snd).prodMk
        (hq.prodMk (measurable_snd.comp measurable_snd))
      have hu := (measurable_update' (a := (⟨k + t, ha.2⟩ : Fin N))).comp hpair
      simpa [actualFrozenUpdate, actualFrozenActive,
        idealPreResponseHistoryOfTuple, ha, Function.comp_def] using hu
    · simpa [actualFrozenUpdate, actualFrozenActive,
        idealPreResponseHistoryOfTuple, ha, Function.comp_def] using
        (measurable_fst.comp measurable_snd : Measurable
          (fun z : (Transcript d N × Point d) × (Transcript d N × Point d) => z.2.1))
  have hinput : Measurable (fun z :
      (Bool × ℕ × Transcript d N × Point d) × (Transcript d N × Point d) =>
      ((z.1.1, z.1.2.1), ((z.1.2.2.1, z.1.2.2.2), z.2))) := by fun_prop
  exact hslices.comp hinput

theorem measurable_joint_nextDirectionPrefixFrame
    {d T : ℕ} (j : Fin T) :
    Measurable (fun z : (Fin j.val → Point d) × Point d =>
      nextDirectionPrefixFrame j z.1 z.2) :=
  (measurable_idealPrefixExtension j).comp (measurable_frameSnoc d j.val)

/-- All four conditioning/continuation inputs vary jointly.  No restriction
is placed on the algorithm's private measurable space or arbitrary output. -/
theorem measurable_joint_nextDirectionFrozenState_snapshot_tuple
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Measurable (fun z :
        ((Fin j.val → Point d) ×
          (Bool × ℕ × Transcript d N × Point d)) ×
        (Point d × (Fin m → Point d)) =>
      actualFrozenGaussianSeedState hT
        (nextDirectionPrefixFrame j z.1.1 z.2.1) j A r
        (idealPreResponseHistoryOfTuple z.1.2) a m z.2.2) := by
  let Θ := ((Fin j.val → Point d) ×
    (Bool × ℕ × Transcript d N × Point d)) × Point d
  let initial : Θ → Transcript d N := fun p => p.1.2.2.2.1
  let mean : Θ → ℕ → Transcript d N → Point d := fun p t tr =>
    frozenStageHistoryMean (nextDirectionPrefixFrame j p.1.1 p.2) j
      (actualFrozenQuery A r (idealPreResponseHistoryOfTuple p.1.2)) t tr
  let update : Θ → ℕ → Transcript d N × Point d → Transcript d N :=
    fun p => actualFrozenUpdate A r (idealPreResponseHistoryOfTuple p.1.2)
  have hinitial : Measurable initial := by fun_prop
  have hm (t : ℕ) : Measurable (fun z : Θ × Transcript d N =>
      mean z.1 t z.2) := by
    have hframe : Measurable (fun z : Θ × Transcript d N =>
        nextDirectionPrefixFrame j z.1.1.1 z.1.2) :=
      (measurable_joint_nextDirectionPrefixFrame j).comp
        (by dsimp only [Θ]; fun_prop : Measurable (fun z : Θ × Transcript d N =>
          (z.1.1.1, z.1.2)))
    have hq : Measurable (fun z : Θ × Transcript d N =>
        actualFrozenQuery A r
          (idealPreResponseHistoryOfTuple z.1.1.2) t z.2) :=
      (measurable_joint_actualFrozenQuery_tuple A r t).comp
        (by dsimp only [Θ]; fun_prop : Measurable (fun z : Θ × Transcript d N =>
          (z.1.1.2, z.2)))
    exact measurable_frozenPrefixMean_comp hT j _ hframe _ hq
  have hu (t : ℕ) : Measurable (fun z :
      Θ × (Transcript d N × Point d) => update z.1 t z.2) :=
    (measurable_joint_actualFrozenUpdate_tuple A r t).comp
      (by dsimp only [Θ]; fun_prop : Measurable (fun z :
        Θ × (Transcript d N × Point d) => (z.1.1.2, z.2)))
  have hjoint := measurable_joint_gaussianSeedState_parametric_initial
    d initial hinitial mean hm a update hu m
  have hcanonical : Measurable (fun z : Θ × (Fin m → Point d) =>
      actualFrozenGaussianSeedState hT
        (nextDirectionPrefixFrame j z.1.1.1 z.1.2) j A r
        (idealPreResponseHistoryOfTuple z.1.1.2) a m z.2) := by
    change Measurable (fun z : Θ × (Fin m → Point d) =>
      gaussianSeedState d (initial z.1) (mean z.1) a (update z.1) m z.2)
    exact hjoint
  have hinput : Measurable (fun z :
      ((Fin j.val → Point d) ×
        (Bool × ℕ × Transcript d N × Point d)) ×
      (Point d × (Fin m → Point d)) => ((z.1, z.2.1), z.2.2)) := by fun_prop
  exact hcanonical.comp hinput

end

end HeavyTailedNoise
