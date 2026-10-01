import HeavyTailedNoise.Upper.K1.CoarseTrackerActualIncrement
import HeavyTailedNoise.Upper.K1.CoarseTrackerShiftedLyapunov

/-!
The tracker at each genuine runtime-batch boundary of the one canonical
gradient-only run.  The full transcript is merely restricted to a prefix;
this file defines no alternative algorithm or oracle process.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem batchStart_le_responseCount_of_le (t : ℕ) (ht : t ≤ P.T) :
    batchStart P t ≤ responseCount P := by
  have hmul := Nat.mul_le_mul_right P.n ht
  dsimp [batchStart, responseCount]
  omega

def boundaryTranscript {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (t : ℕ) (ht : t ≤ P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    Transcript d (batchStart P t) :=
  fun i => (runTranscript O (algorithm (d := d) P) z.1
    (responseCount P) z.2)
      (i.castLE (batchStart_le_responseCount_of_le P t ht))

/-- Outside the claimed runtime horizon the analysis variable is set to
zero; all stochastic claims below use only `t ≤ P.T`. -/
irreducible_def actualTrackerAtBoundary {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar) (t : ℕ)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) : ℝ :=
  if ht : t ≤ P.T then
    trackerError I
      (point P (stateAt P (batchStart P t)
        (boundaryTranscript P I.oracle t ht z)))
      (center P (stateAt P (batchStart P t)
        (boundaryTranscript P I.oracle t ht z)))
  else 0

theorem measurable_boundaryTranscript {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (t : ℕ) (ht : t ≤ P.T) :
    Measurable (boundaryTranscript (d := d) P O t ht) := by
  have hfull : Measurable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        runTranscript O (algorithm (d := d) P) z.1
          (responseCount P) z.2) :=
    measurable_runTranscript O (algorithm (d := d) P) (responseCount P)
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_pi_apply
    (i.castLE (batchStart_le_responseCount_of_le P t ht))).comp hfull

theorem measurable_actualTrackerAtBoundary {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar) (t : ℕ) :
    Measurable (actualTrackerAtBoundary P I t) := by
  by_cases ht : t ≤ P.T
  · have hstate : Measurable
        (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
          stateAt P (batchStart P t)
            (boundaryTranscript P I.oracle t ht z)) :=
      (measurable_stateAt P (batchStart P t)).comp
        (measurable_boundaryTranscript P I.oracle t ht)
    have hpair : Measurable
        (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
          (point P (stateAt P (batchStart P t)
            (boundaryTranscript P I.oracle t ht z)),
           center P (stateAt P (batchStart P t)
            (boundaryTranscript P I.oracle t ht z)))) :=
      (measurable_fst.comp hstate).prodMk
        (measurable_fst.comp (measurable_snd.comp hstate))
    change Measurable (fun z => actualTrackerAtBoundary P I t z)
    simpa only [actualTrackerAtBoundary, dif_pos ht, Function.comp_def] using
      (measurable_trackerError I).comp hpair
  · change Measurable (fun z => actualTrackerAtBoundary P I t z)
    simpa only [actualTrackerAtBoundary, dif_neg ht] using
      (measurable_const : Measurable
        (fun _ : Fin P.T × (Fin (responseCount P) → Seed) => (0 : ℝ)))

theorem actualTrackerAtBoundary_nonneg {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar) (t : ℕ)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    0 ≤ actualTrackerAtBoundary P I t z := by
  by_cases ht : t ≤ P.T
  · simp only [actualTrackerAtBoundary, dif_pos ht, trackerError]
    exact norm_nonneg _
  · simp only [actualTrackerAtBoundary, dif_neg ht]
    norm_num

/-- The full-log prefix at a real runtime boundary is exactly the
pre-batch transcript in the canonical history factor. -/
theorem boundaryTranscript_eq_batchHistory {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    boundaryTranscript P O u.val (Nat.le_of_lt u.isLt) z =
      (batchHistoryOfRun P O u z).2 := by
  funext i
  exact runTranscript_prefix_le O (algorithm (d := d) P)
    z.1 (batchStart P u.val) (responseCount P)
    (batchStart_le_responseCount_of_le P u.val
      (Nat.le_of_lt u.isLt)) z.2 i

/-- At a runtime-batch start, the global-boundary process is exactly the
tracker at the pre-batch history used in the fresh-batch product law. -/
theorem actualTrackerAtBoundary_eq_history {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    actualTrackerAtBoundary P I u.val z =
      trackerError I
        (batchDecision P u (batchHistoryOfRun P I.oracle u z))
        (batchCenter P u (batchHistoryOfRun P I.oracle u z)) := by
  have hu : u.val ≤ P.T := Nat.le_of_lt u.isLt
  have heq : boundaryTranscript P I.oracle u.val hu z =
      (batchHistoryOfRun P I.oracle u z).2 :=
    boundaryTranscript_eq_batchHistory P I.oracle u z
  simp only [actualTrackerAtBoundary, dif_pos hu]
  rw [heq]
  rfl

theorem batchStart_succ_eq_batchEndTime (u : Fin P.T) :
    batchStart P (u.val + 1) = batchEndTime P u := by
  dsimp [batchStart, batchEndTime]
  rw [Nat.succ_mul]
  omega

/-- The next boundary transcript is the completed transcript of the
current runtime batch, with only the provable natural-time equality cast. -/
theorem boundaryTranscript_succ_eq_batchEndTranscript {d : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    (fun i : Fin (batchEndTime P u) =>
      (boundaryTranscript P O (u.val + 1)
        (Nat.succ_le_iff.mpr u.isLt) z)
        (i.cast (batchStart_succ_eq_batchEndTime P u).symm)) =
      batchEndTranscript P O z.1 u z.2 := by
  funext i
  exact congrArg (runTranscript O (algorithm (d := d) P) z.1
    (responseCount P) z.2) (Fin.ext rfl)

/-- Changing only the proven natural length index of a transcript does not
change the state reconstructed from its returned vectors. -/
theorem stateAt_transcript_cast {d m n : ℕ} (h : m = n)
    (H : Transcript d m) :
    stateAt P n (fun i : Fin n => H (i.cast h.symm)) =
      stateAt P m H := by
  cases h
  rfl

/-- The next runtime boundary is exactly the state after all responses in
the current complete batch have been consumed. -/
theorem actualTrackerAtBoundary_succ_eq_batchEnd {d : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    actualTrackerAtBoundary P I (u.val + 1) z =
      trackerError I
        (point P (stateAt P (batchEndTime P u)
          (batchEndTranscript P I.oracle z.1 u z.2)))
        (center P (stateAt P (batchEndTime P u)
          (batchEndTranscript P I.oracle z.1 u z.2))) := by
  have hu : u.val + 1 ≤ P.T := Nat.succ_le_iff.mpr u.isLt
  have htime := batchStart_succ_eq_batchEndTime P u
  have htrans := boundaryTranscript_succ_eq_batchEndTranscript
    P I.oracle u z
  have hstate := stateAt_transcript_cast P htime
    (boundaryTranscript P I.oracle (u.val + 1) hu z)
  rw [htrans] at hstate
  simp only [actualTrackerAtBoundary, dif_pos hu]
  rw [← hstate]

/-- The literal adaptive boundary process has the same single-batch
increment previously bounded under the exact history × fresh-batch law. -/
theorem actualTrackerAtBoundary_increment_eq {d : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    actualTrackerAtBoundary P I (u.val + 1) z -
      actualTrackerAtBoundary P I u.val z =
    trackerIncrementOnHistory P I u
      (batchHistoryOfRun P I.oracle u z)
      (batchSeedBlock P u z.2) := by
  rw [actualTrackerAtBoundary_succ_eq_batchEnd P I u z,
    actualTrackerAtBoundary_eq_history P I u z]
  exact actualBatch_tracker_increment_eq P I z.1 u z.2

/-- The deterministic error increment cap holds along the *actual* adaptive
path, including reuse of the first current response. -/
theorem actualTrackerAtBoundary_increment_abs_le {d : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed))
    (hbeta : 0 ≤ P.beta) (hh : 0 ≤ P.h) :
    |actualTrackerAtBoundary P I (u.val + 1) z -
      actualTrackerAtBoundary P I u.val z| ≤
      P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h := by
  rw [actualTrackerAtBoundary_increment_eq P I u z]
  exact trackerIncrementOnHistory_abs_le P I u
    (batchHistoryOfRun P I.oracle u z) (batchSeedBlock P u z.2)
    hbeta hh

/-- Every finite-horizon shifted exponential weight of the actual tracker
is integrable although its first error may have no exponential moment. -/
theorem actualTrackerShiftedWeight_integrable {d : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    {p Δ σ Lbar : ℝ}
    (I : Admissible d Seed p q Δ σ Lbar)
    (b lam : ℝ) (hlam : 0 ≤ lam)
    (hbeta : 0 ≤ P.beta) (hh : 0 ≤ P.h)
    (t : ℕ) (ht : t ≤ P.T) :
    Integrable
      (shiftedTrackerWeight (actualTrackerAtBoundary P I) b
        (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h) lam t)
      ((algorithm (d := d) P).privateLaw.prod
        (freshSeedLaw I.oracle (responseCount P))) := by
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  letI : IsProbabilityMeasure ((algorithm (d := d) P).privateLaw) :=
    (algorithm (d := d) P).private_probability
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle (responseCount P)) :=
    freshSeedLaw_probability I.oracle (responseCount P)
  have hC : 0 ≤ P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h :=
    add_nonneg (mul_nonneg hbeta (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩).le)
      (mul_nonneg I.Lbar_pos.le hh)
  apply shiftedTrackerWeight_integrable_of_bounded_increments
    ((algorithm (d := d) P).privateLaw.prod
      (freshSeedLaw I.oracle (responseCount P)))
    (actualTrackerAtBoundary P I) b
    (P.beta * P.tau ⟨0, Nat.zero_lt_succ P.J⟩ + Lbar * P.h)
    lam hC hlam t
  · intro s hs
    exact measurable_actualTrackerAtBoundary P I s
  · intro s hs z
    let u : Fin P.T := ⟨s, lt_of_lt_of_le hs ht⟩
    simpa only [u] using
      actualTrackerAtBoundary_increment_abs_le P I u z hbeta hh

end

end HeavyTailedNoise.UpperK1
