import HeavyTailedNoise.Lower.Gated.StartedStageHistoryRecovery

/-!
Total measurable reconstruction of earlier observations on started paths.

Only stored query coordinates drive the existing cap replay.  Returned pairs
before the recovered clock are copied from the latest complete transcript;
no gradient or noise is replayed.  An invalid response-slot clock returns the
public never-started tuple.  The self observation passes through unchanged,
including a response-free output at time N.

The exact recovery theorem requires the actual latest record to be started.
Localized sigma-algebra trace and conditional-mean transfer remain separate.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

set_option autoImplicit false

theorem measurable_joint_capReplayUpdate {d T : ℕ} (hT : 0 < T) :
    Measurable (fun z : ℕ × ((Fin T → Point d) × Point d) =>
      idealStageAfter z.2.1 z.1 z.2.2) := by
  classical
  apply measurable_from_prod_countable_right
  intro s
  by_cases hs : s < T
  · let j : Fin T := ⟨s, hs⟩
    have hR : 0 < hardRadius T := by
      unfold hardRadius
      have ht : (0 : ℝ) < T := by exact_mod_cast hT
      positivity
    have hp : Measurable (fun z : (Fin T → Point d) × Point d =>
        (z.1, softProjection (hardRadius T) z.2)) :=
      measurable_fst.prodMk ((contDiff_softProjection_two hR).continuous.measurable.comp measurable_snd)
    have hc : Measurable (fun z : (Fin T → Point d) × Point d =>
        frameCoordinates z.1 (softProjection (hardRadius T) z.2) j) :=
      ((measurable_pi_apply j).comp contDiff_joint_frameCoordinates_two.continuous.measurable).comp hp
    have hr : Measurable (fun z : (Fin T → Point d) × Point d =>
        frameOrthogonalResidual z.1 (Finset.univ.filter (· ≤ j))
          (softProjection (hardRadius T) z.2)) :=
      (contDiff_joint_frameOrthogonalResidual_two (Finset.univ.filter (· ≤ j))).continuous.measurable.comp hp
    have hleft := measurableSet_le
      (measurable_const : Measurable (fun _ : (Fin T → Point d) × Point d => (1 / 2 : ℝ))) hc.abs
    have hright := measurableSet_le (hr.norm.pow_const 2)
      (measurable_const : Measurable (fun _ : (Fin T → Point d) × Point d =>
        (1000 + 1 / 16 + 1 : ℝ)))
    have hset : MeasurableSet {z : (Fin T → Point d) × Point d | idealCapHit z.1 s z.2} := by
      convert hleft.inter hright using 1
      ext z
      simp [idealCapHit, prefixCapSet, hs, j]
    change Measurable (fun z : (Fin T → Point d) × Point d =>
      if idealCapHit z.1 s z.2 then s + 1 else s)
    exact Measurable.ite hset
      (measurable_const : Measurable (fun _ : (Fin T → Point d) × Point d => s + 1))
      (measurable_const : Measurable (fun _ : (Fin T → Point d) × Point d => s))
  · simp [idealStageAfter, idealCapHit, hs]

theorem measurable_storedTranscriptQuery {d N : ℕ} (t : ℕ) :
    Measurable (fun tr : Transcript d N => storedTranscriptQuery tr t) := by
  by_cases ht : t < N
  · simpa [storedTranscriptQuery, ht, Function.comp_def] using
      (measurable_fst.comp (measurable_pi_apply (⟨t, ht⟩ : Fin N)))
  · simpa only [storedTranscriptQuery, dite_eq_right ht] using
      (measurable_const : Measurable (fun _ : Transcript d N => (0 : Point d)))

theorem measurable_storedQueryStageAt {d T N : ℕ} (hT : 0 < T) (t : ℕ) :
    Measurable (fun z : (Fin T → Point d) × Transcript d N => storedQueryStageAt z.1 z.2 t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (measurable_joint_capReplayUpdate hT).comp
        (ih.prodMk (measurable_fst.prodMk ((measurable_storedTranscriptQuery t).comp measurable_snd)))

theorem measurable_storedQueryAfterAt {d T N : ℕ} (hT : 0 < T) (t : ℕ) :
    Measurable (fun z : (Fin T → Point d) × Transcript d N => storedQueryAfterAt z.1 z.2 t) :=
  measurable_storedQueryStageAt hT (t + 1)

theorem measurable_storedQueryStageStart {d T N : ℕ} (hT : 0 < T) (k : ℕ) :
    Measurable (fun z : (Fin T → Point d) × Transcript d N => storedQueryStageStart z.1 z.2 k) := by
  classical
  let p : ((Fin T → Point d) × Transcript d N) → ℕ → Prop :=
    fun z t => (t ≤ N ∧ k ≤ storedQueryAfterAt z.1 z.2 t) ∨ t = N + 1
  have hex (z : (Fin T → Point d) × Transcript d N) : ∃ t, p z t := ⟨N + 1, Or.inr rfl⟩
  have hpm (t : ℕ) : MeasurableSet {z : (Fin T → Point d) × Transcript d N | p z t} := by
    have hh : MeasurableSet {z : (Fin T → Point d) × Transcript d N |
        k ≤ storedQueryAfterAt z.1 z.2 t} :=
      measurableSet_le measurable_const (measurable_storedQueryAfterAt hT t)
    by_cases ht : t ≤ N <;> by_cases hs : t = N + 1 <;> simp [p, ht, hs, hh]
  have heq (z : (Fin T → Point d) × Transcript d N) :
      storedQueryStageStart z.1 z.2 k = Nat.find (hex z) := by
    by_cases hh : ∃ t : ℕ, t ≤ N ∧ k ≤ storedQueryAfterAt z.1 z.2 t
    · have hb := (Nat.find_spec hh).1
      rw [storedQueryStageStart, dite_eq_left hh]
      apply ((Nat.find_eq_iff (hex z)).2 ?_).symm
      refine ⟨Or.inl (Nat.find_spec hh), ?_⟩
      intro t ht
      rintro (hhit | hsent)
      · exact Nat.find_min hh ht hhit
      · omega
    · rw [storedQueryStageStart, dite_eq_right hh]
      apply ((Nat.find_eq_iff (hex z)).2 ?_).symm
      refine ⟨Or.inr rfl, ?_⟩
      intro t ht
      rintro (hhit | hsent)
      · exact hh ⟨t, hhit⟩
      · omega
  simpa only [heq] using measurable_find hex hpm

def storedTranscriptBefore {d N : ℕ} (t : ℕ) (tr : Transcript d N) : Transcript d N :=
  fun k => if k.val < t then tr k else (0, 0)

theorem measurable_storedTranscriptBefore {d N : ℕ} (t : ℕ) :
    Measurable (storedTranscriptBefore (d := d) (N := N) t) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k.val < t
  · simpa [storedTranscriptBefore, hk] using (measurable_pi_apply k)
  · simp [storedTranscriptBefore, hk]

def recoveredStoppedTuple {d N : ℕ} (t : ℕ) (tr : Transcript d N) :
    Bool × ℕ × Transcript d N × Point d :=
  if t < N then (true, t, storedTranscriptBefore t tr, storedTranscriptQuery tr t)
  else (false, N + 1, fun _ => (0, 0), 0)

theorem measurable_recoveredStoppedTuple {d N : ℕ} :
    Measurable (fun z : ℕ × Transcript d N => recoveredStoppedTuple z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro t
  by_cases ht : t < N
  · simpa only [recoveredStoppedTuple, ite_eq_left ht] using
      (measurable_const.prodMk (measurable_const.prodMk
        ((measurable_storedTranscriptBefore t).prodMk (measurable_storedTranscriptQuery t))))
  · simpa only [recoveredStoppedTuple, ite_eq_right ht] using
      (measurable_const : Measurable (fun _ : Transcript d N =>
        ((false, N + 1, fun _ : Fin N => ((0 : Point d), (0 : Point d)), (0 : Point d)) :
          Bool × ℕ × Transcript d N × Point d)))

def reconstructEarlierObservation {d T N : ℕ} (i j : Fin T)
    (z : IdealStageAnalysisData d T N) : IdealStageAnalysisData d T N :=
  if i = j then z else
    (prefixFrame z.1 i, recoveredStoppedTuple
      (storedQueryStageStart z.1 z.2.2.2.1 (i.val + 1)) z.2.2.2.1)

theorem measurable_reconstructEarlierObservation {d T N : ℕ} (hT : 0 < T) (i j : Fin T) :
    Measurable (reconstructEarlierObservation (d := d) (N := N) i j) := by
  classical
  change Measurable (fun z : IdealStageAnalysisData d T N => if i = j then z else
    (prefixFrame z.1 i, recoveredStoppedTuple
      (storedQueryStageStart z.1 z.2.2.2.1 (i.val + 1)) z.2.2.2.1))
  by_cases hij : i = j
  · simp only [ite_eq_left hij]
    exact measurable_id
  · have hf : Measurable (fun z : IdealStageAnalysisData d T N => prefixFrame z.1 i) := by
      apply measurable_pi_iff.mpr
      intro k
      by_cases hk : k ≤ i
      · simpa [prefixFrame, hk, Function.comp_def] using ((measurable_pi_apply k).comp measurable_fst)
      · simp [prefixFrame, hk]
    have ht : Measurable (fun z : IdealStageAnalysisData d T N => z.2.2.2.1) := by fun_prop
    have hc := (measurable_storedQueryStageStart hT (i.val + 1)).comp (measurable_fst.prodMk ht)
    simpa only [ite_eq_right hij, Function.comp_def] using
      hf.prodMk (measurable_recoveredStoppedTuple.comp (hc.prodMk ht))

theorem storedTranscriptBefore_eq_older_stoppedTranscript
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (i j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (ξ : Fin N → Point d) (a : ℝ)
    (hi : idealStageStart hT U A r ξ a (i.val + 1) ≤ N)
    (hj : idealStageStart hT U A r ξ a (j.val + 1) ≤ N)
    (hij : idealStageStart hT U A r ξ a (i.val + 1) ≤ idealStageStart hT U A r ξ a (j.val + 1)) :
    storedTranscriptBefore (idealStageStart hT U A r ξ a (i.val + 1))
      (idealStoppedPreHistory hT U j A r ξ a).transcript =
      (idealStoppedPreHistory hT U i A r ξ a).transcript := by
  classical
  rw [idealStoppedPreHistory_eq_started_record hT U i A r ξ a hi,
    idealStoppedPreHistory_eq_started_record hT U j A r ξ a hj]
  funext k
  by_cases hk : k.val < idealStageStart hT U A r ξ a (i.val + 1)
  · have hk' : k.val < idealStageStart hT U A r ξ a (j.val + 1) := hk.trans_le hij
    simp only [storedTranscriptBefore, ite_eq_left hk, idealPadTranscript,
      dite_eq_left hk, dite_eq_left hk']
    exact (idealStateAt_transcript_pair_eq_earlier hT U A r ξ a _ hj k.val hk').trans
      (idealStateAt_transcript_pair_eq_earlier hT U A r ξ a _ hi k.val hk).symm
  · simp only [storedTranscriptBefore, ite_eq_right hk, idealPadTranscript, dite_eq_right hk]

/-- Every earlier observation is the total measurable reconstruction of the
latest actual observation on its started branch. -/
theorem reconstructEarlierObservation_eq_actual_of_started
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (i j : Fin T) (hij : i ≤ j)
    (A : RandomAlgorithm d N Private) (r : Private) (ξ : Fin N → Point d) (a : ℝ)
    (hs : (idealStoppedPreHistory hT U j A r ξ a).started = true) :
    reconstructEarlierObservation i j (idealStageObservation hT U A r ξ a j.val) =
      idealStageObservation hT U A r ξ a i.val := by
  classical
  by_cases heq : i = j
  · subst i
    simp [reconstructEarlierObservation]
  · have hlt : i < j := lt_of_le_of_ne hij heq
    have hj := idealStoppedPreHistory_started_implies_start_le hT U j A r ξ a hs
    have hpos : 0 < j.val := by change i.val < j.val at hlt; omega
    have hstrict := idealStageStart_lt_next_of_started hT U A r ξ a j.val hpos hj
    have hmono := idealStageStart_mono_target hT U A r ξ a
      (i.val + 1) j.val (by change i.val < j.val at hlt; omega)
    have hbefore : idealStageStart hT U A r ξ a (i.val + 1) <
        idealStageStart hT U A r ξ a (j.val + 1) := hmono.trans_lt hstrict
    have hi : idealStageStart hT U A r ξ a (i.val + 1) ≤ N := hbefore.le.trans hj
    have hiN : idealStageStart hT U A r ξ a (i.val + 1) < N := hbefore.trans_le hj
    have hidx (k : Fin T) : idealPrefixIndex hT k.val = k := by
      apply Fin.ext
      simp only [idealPrefixIndex]
      omega
    have hf : prefixFrame (prefixFrame U j) i = prefixFrame U i := by
      apply (prefixFrame_eq_of_agree i ?_).symm
      intro k hk
      simp only [prefixFrame, ite_eq_left (hk.trans hij)]
    have htr := storedTranscriptBefore_eq_older_stoppedTranscript hT U i j A r ξ a hi hj hbefore.le
    have hq := storedLatestQuery_eq_idealDecision_before_start hT U j A r ξ a hj _ hbefore
    have hclock := storedQueryStageStart_eq_earlier_idealStart hT U i j hlt A r ξ a hs
    have hrecord : recoveredStoppedTuple (idealStageStart hT U A r ξ a (i.val + 1))
        (idealStoppedPreHistory hT U j A r ξ a).transcript =
        idealPreResponseTuple (idealStoppedPreHistory hT U i A r ξ a) := by
      rw [recoveredStoppedTuple, ite_eq_left hiN, htr, hq,
        idealStoppedPreHistory_eq_started_record hT U i A r ξ a hi]
      rfl
    simp only [idealStageObservation, hidx, reconstructEarlierObservation, ite_eq_right heq,
      idealPreResponseTuple,
      hclock, hf, hrecord]

end

end HeavyTailedNoise
