import HeavyTailedNoise.Lower.Gated.IdealStageFiltration

/-!
Cap-only replay of a started latest record.

The record's complete padded transcript stores every earlier responsive
query in its first coordinate.  Replay applies the single existing
idealStageAfter rule to those stored points and the latest revealed prefix.
It never evaluates a gradient, observes a noise seed, or creates an algorithm.

This milestone recovers pre-response stage values and all strictly earlier
positive-stage clocks.  Full measurable snapshot reconstruction and the
localized sigma-algebra/conditional-half transfer remain subsequent steps.
No recovery from a never-started zero snapshot is asserted.
-/

namespace HeavyTailedNoise

noncomputable section

set_option autoImplicit false

def storedTranscriptQuery {d N : ℕ} (tr : Transcript d N) (t : ℕ) : Point d := by
  classical
  exact if ht : t < N then (tr ⟨t, ht⟩).1 else 0

def storedQueryStageAt {d T N : ℕ} (V : Fin T → Point d) (tr : Transcript d N) :
    ℕ → ℕ
  | 0 => 0
  | t + 1 => idealStageAfter V (storedQueryStageAt V tr t) (storedTranscriptQuery tr t)

def storedQueryAfterAt {d T N : ℕ} (V : Fin T → Point d) (tr : Transcript d N)
    (t : ℕ) : ℕ :=
  idealStageAfter V (storedQueryStageAt V tr t) (storedTranscriptQuery tr t)

/-- A bounded clock computed only from stored query coordinates.  The current
latest starting query is intentionally excluded from the padded transcript. -/
def storedQueryStageStart {d T N : ℕ} (V : Fin T → Point d) (tr : Transcript d N)
    (k : ℕ) : ℕ := by
  classical
  exact if h : ∃ t : ℕ, t ≤ N ∧ k ≤ storedQueryAfterAt V tr t then Nat.find h else N + 1

theorem idealStoppedPreHistory_started_implies_start_le
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hs : (idealStoppedPreHistory hT U j A r ξ a).started = true) :
    idealStageStart hT U A r ξ a (j.val + 1) ≤ N := by
  by_contra hn
  simp only [idealStoppedPreHistory, idealPreHistoryAtTime, dite_eq_right hn] at hs
  cases hs

/-- Later returned pairs preserve every earlier complete pair. -/
theorem idealStateAt_transcript_pair_eq_earlier
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (n : ℕ) (hn : n ≤ N) (t : ℕ) (ht : t < n) :
    (idealStateAt hT U A r ξ a n).transcript ⟨t, ht⟩ =
      (idealStateAt hT U A r ξ a (t + 1)).transcript (Fin.last t) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases heq : t = n
      · subst t
        rfl
      · have htn : t < n := by omega
        have hidx : (⟨t, ht⟩ : Fin (n + 1)) = (⟨t, htn⟩ : Fin n).castSucc := rfl
        rw [idealStateAt_transcript_succ_eq hT U A r ξ a (by omega), hidx,
          Fin.snoc_castSucc]
        exact ih (by omega) htn

theorem idealStateAt_transcript_query_eq_decision
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (n : ℕ) (hn : n ≤ N) (t : ℕ) (ht : t < n) :
    ((idealStateAt hT U A r ξ a n).transcript ⟨t, ht⟩).1 =
      idealDecisionAt hT U A r ξ a t := by
  rw [idealStateAt_transcript_pair_eq_earlier hT U A r ξ a n hn t ht,
    idealStateAt_transcript_succ_eq hT U A r ξ a (by omega), Fin.snoc_last]

theorem storedLatestQuery_eq_idealDecision_before_start
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hstart : idealStageStart hT U A r ξ a (j.val + 1) ≤ N)
    (t : ℕ) (ht : t < idealStageStart hT U A r ξ a (j.val + 1)) :
    storedTranscriptQuery (idealStoppedPreHistory hT U j A r ξ a).transcript t =
      idealDecisionAt hT U A r ξ a t := by
  have htN : t < N := lt_of_lt_of_le ht hstart
  rw [idealStoppedPreHistory_eq_started_record hT U j A r ξ a hstart]
  simp only [storedTranscriptQuery, dite_eq_left htN, idealPadTranscript, dite_eq_left ht]
  exact idealStateAt_transcript_query_eq_decision hT U A r ξ a _ hstart t ht

/-- Replay through the current start time uses only stored earlier queries.
The latest prefix agrees with every cap test that can occur on this interval. -/
theorem storedQueryStageAt_eq_ideal_before_latest_start
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hstart : idealStageStart hT U A r ξ a (j.val + 1) ≤ N)
    (t : ℕ) (ht : t ≤ idealStageStart hT U A r ξ a (j.val + 1)) :
    storedQueryStageAt (prefixFrame U j)
        (idealStoppedPreHistory hT U j A r ξ a).transcript t =
      (idealStateAt hT U A r ξ a t).stage := by
  have hagree : ∀ k, k ≤ j → U k = prefixFrame U j k := by
    intro k hk
    simp only [prefixFrame, ite_eq_left hk]
  induction t with
  | zero => rfl
  | succ t ih =>
      have htBefore : t < idealStageStart hT U A r ξ a (j.val + 1) := by omega
      have htN : t < N := lt_of_lt_of_le htBefore hstart
      have hq := storedLatestQuery_eq_idealDecision_before_start
        hT U j A r ξ a hstart t htBefore
      have hstage := idealStageBefore_le_of_beforeStart hT U j A r ξ a t
        htN.le (le_of_lt htBefore)
      have hcap := idealStageAfter_eq_of_agree j hagree
        (idealStateAt hT U A r ξ a t).stage hstage (idealDecisionAt hT U A r ξ a t)
      calc
        storedQueryStageAt (prefixFrame U j)
            (idealStoppedPreHistory hT U j A r ξ a).transcript (t + 1) =
          idealStageAfter (prefixFrame U j)
            (storedQueryStageAt (prefixFrame U j)
              (idealStoppedPreHistory hT U j A r ξ a).transcript t)
            (storedTranscriptQuery (idealStoppedPreHistory hT U j A r ξ a).transcript t) := rfl
        _ = idealAfterAt hT U A r ξ a t := by
          rw [ih (by omega), hq, ← hcap]
          rfl
        _ = (idealStateAt hT U A r ξ a (t + 1)).stage :=
          (idealStateAt_stage_succ_eq_after hT U A r ξ a htN).symm

theorem storedQueryAfterAt_eq_ideal_before_latest_start
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (j : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hstart : idealStageStart hT U A r ξ a (j.val + 1) ≤ N)
    (t : ℕ) (ht : t < idealStageStart hT U A r ξ a (j.val + 1)) :
    storedQueryAfterAt (prefixFrame U j)
        (idealStoppedPreHistory hT U j A r ξ a).transcript t =
      idealAfterAt hT U A r ξ a t := by
  change storedQueryStageAt (prefixFrame U j)
      (idealStoppedPreHistory hT U j A r ξ a).transcript (t + 1) = _
  rw [storedQueryStageAt_eq_ideal_before_latest_start hT U j A r ξ a hstart _ (by omega)]
  exact idealStateAt_stage_succ_eq_after hT U A r ξ a (by omega)

/-- Every strictly earlier positive-stage clock is computed from the latest
prefix and stored query slots.  The latest query itself need not be a slot. -/
theorem storedQueryStageStart_eq_earlier_idealStart
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (i j : Fin T) (hij : i < j)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hs : (idealStoppedPreHistory hT U j A r ξ a).started = true) :
    storedQueryStageStart (prefixFrame U j)
        (idealStoppedPreHistory hT U j A r ξ a).transcript (i.val + 1) =
      idealStageStart hT U A r ξ a (i.val + 1) := by
  classical
  have hstart := idealStoppedPreHistory_started_implies_start_le hT U j A r ξ a hs
  have hjpos : 0 < j.val := by have h := i.isLt; change i.val < j.val at hij; omega
  have hstrict := idealStageStart_lt_next_of_started hT U A r ξ a j.val hjpos hstart
  have hle := idealStageStart_mono_target hT U A r ξ a
    (i.val + 1) j.val (by change i.val < j.val at hij; omega)
  let τ := idealStageStart hT U A r ξ a (i.val + 1)
  have hτBefore : τ < idealStageStart hT U A r ξ a (j.val + 1) := hle.trans_lt hstrict
  have hτN : τ ≤ N := (le_of_lt hτBefore).trans hstart
  have hhit : i.val + 1 ≤ storedQueryAfterAt (prefixFrame U j)
      (idealStoppedPreHistory hT U j A r ξ a).transcript τ := by
    rw [storedQueryAfterAt_eq_ideal_before_latest_start hT U j A r ξ a hstart τ hτBefore]
    exact idealStageStart_hit hT U A r ξ a (i.val + 1) hτN
  have hex : ∃ t : ℕ, t ≤ N ∧ i.val + 1 ≤ storedQueryAfterAt (prefixFrame U j)
      (idealStoppedPreHistory hT U j A r ξ a).transcript t := ⟨τ, hτN, hhit⟩
  rw [storedQueryStageStart, dite_eq_left hex]
  apply (Nat.find_eq_iff hex).2
  refine ⟨⟨hτN, hhit⟩, ?_⟩
  intro t ht
  rintro ⟨htN, hge⟩
  have htBefore : t < idealStageStart hT U A r ξ a (j.val + 1) := ht.trans hτBefore
  rw [storedQueryAfterAt_eq_ideal_before_latest_start hT U j A r ξ a hstart t htBefore] at hge
  have hsmall := idealStageStart_before hT U A r ξ a (i.val + 1) t ht htN
  omega

end

end HeavyTailedNoise
