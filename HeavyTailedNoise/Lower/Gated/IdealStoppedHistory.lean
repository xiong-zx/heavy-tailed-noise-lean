import HeavyTailedNoise.Probability.HaarConditionalFrame
import HeavyTailedNoise.Lower.Gated.PrefixLocality

/-!
The manuscript's idealized strict-K=1 process.  Each responsive decision is
made from the algorithm's full query/response transcript; the hidden stage
is used only by the oracle-side construction.  The final algorithm output
is a response-free decision.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace HeavyTailedNoise

/-- A bounded stage index selects the exact truncated potential.  Stage T
uses the full potential, represented by the final prefix index. -/
def idealPrefixIndex {T : ℕ} (hT : 0 < T) (stage : ℕ) : Fin T :=
  ⟨min stage (T - 1), by omega⟩

/-- The manuscript's cap test at the current stage and query. -/
def idealCapHit {d T : ℕ} (U : Fin T → Point d)
    (stage : ℕ) (x : Point d) : Prop :=
  ∃ h : stage < T,
    softProjection (hardRadius T) x ∈
      prefixCapSet U ⟨stage, h⟩

/-- A query can reveal at most one new frame column. -/
def idealStageAfter {d T : ℕ} (U : Fin T → Point d)
    (stage : ℕ) (x : Point d) : ℕ := by
  classical
  exact if idealCapHit U stage x then stage + 1 else stage

/-- The exact truncated deterministic response mean, including the boundary
correction already contained in prefixHardPotential. -/
def idealResponseMean {d T : ℕ} (hT : 0 < T)
    (U : Fin T → Point d) (stageAfter : ℕ)
    (x : Point d) : Point d :=
  gradient (prefixHardPotential U (idealPrefixIndex hT stageAfter)) x

structure IdealState (d n : ℕ) where
  stage : ℕ
  transcript : Transcript d n

/-- One fixed tape contains exactly N noise vectors.  Values beyond the
responsive horizon are never used to issue a response. -/
def idealNoiseAt {d N : ℕ}
    (noise : Fin N → Point d) (t : ℕ) : Point d := by
  classical
  exact if h : t < N then noise ⟨t, h⟩ else 0

/-- The one response-bearing state transition.  The algorithm sees only the
new query/response pair; it is never given the hidden stage or noise seed. -/
def idealStepState {d T N n : ℕ} {Private : Type*}
    [MeasurableSpace Private] (hT : 0 < T)
    (U : Fin T → Point d) (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (st : IdealState d n) : IdealState d (n + 1) :=
  let x := A.decide n r st.transcript
  let next := idealStageAfter U st.stage x
  let response := idealResponseMean hT U next x +
    a • idealNoiseAt noise n
  ⟨next, Fin.snoc st.transcript (x, response)⟩

/-- State before query n after n returned vectors.  The recursion is
defined for all n for convenience; only n≤N is used. -/
def idealStateAt {d T N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (hT : 0 < T)
    (U : Fin T → Point d) (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ) :
    (n : ℕ) → IdealState d n
  | 0 => ⟨0, fun i => i.elim0⟩
  | n + 1 =>
      idealStepState hT U A r noise a
        (idealStateAt hT U A r noise a n)

/-- The next decision at time t.  At t=N it is the algorithm's arbitrary
response-free output, not a further oracle response. -/
def idealDecisionAt {d T N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (hT : 0 < T)
    (U : Fin T → Point d) (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (t : ℕ) : Point d := by
  classical
  exact if ht : t < N then
    A.decide t r (idealStateAt hT U A r noise a t).transcript
  else A.output r
    (idealStateAt hT U A r noise a N).transcript

/-- Stage after the cap test at decision t.  The decision at t=N is
response-free. -/
def idealAfterAt {d T N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (hT : 0 < T)
    (U : Fin T → Point d) (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (t : ℕ) : ℕ :=
  idealStageAfter U
    (idealStateAt hT U A r noise a t).stage
    (idealDecisionAt hT U A r noise a t)

lemma prefixCapSet_eq_of_agree {d T : ℕ}
    {U V : Fin T → Point d} (j : Fin T)
    (h : ∀ i, i ≤ j → U i = V i) :
    prefixCapSet U j = prefixCapSet V j := by
  ext y
  have hcoord :
      frameCoordinates U y j = frameCoordinates V y j := by
    simp [frameCoordinates, h j le_rfl]
  have hres :
      frameOrthogonalResidual U
          (Finset.univ.filter (· ≤ j)) y =
        frameOrthogonalResidual V
          (Finset.univ.filter (· ≤ j)) y := by
    unfold frameOrthogonalResidual
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≤ j := (Finset.mem_filter.mp hi).2
    simp [frameCoordinates, h i hij]
  simp [prefixCapSet, hcoord, hres]

lemma idealCapHit_iff_of_agree {d T : ℕ}
    {U V : Fin T → Point d} (j : Fin T)
    (h : ∀ i, i ≤ j → U i = V i)
    (stage : ℕ) (hs : stage ≤ j.val) (x : Point d) :
    idealCapHit U stage x ↔ idealCapHit V stage x := by
  unfold idealCapHit
  constructor
  · rintro ⟨ht, hmem⟩
    refine ⟨ht, ?_⟩
    have hk : (⟨stage, ht⟩ : Fin T) ≤ j := hs
    have hcap := prefixCapSet_eq_of_agree
      (U := U) (V := V) (⟨stage, ht⟩ : Fin T)
      (fun i hi => h i (le_trans hi hk))
    rw [hcap] at hmem
    exact hmem
  · rintro ⟨ht, hmem⟩
    refine ⟨ht, ?_⟩
    have hk : (⟨stage, ht⟩ : Fin T) ≤ j := hs
    have hcap := prefixCapSet_eq_of_agree
      (U := U) (V := V) (⟨stage, ht⟩ : Fin T)
      (fun i hi => h i (le_trans hi hk))
    rw [hcap]
    exact hmem

lemma idealStageAfter_eq_of_agree {d T : ℕ}
    {U V : Fin T → Point d} (j : Fin T)
    (h : ∀ i, i ≤ j → U i = V i)
    (stage : ℕ) (hs : stage ≤ j.val) (x : Point d) :
    idealStageAfter U stage x = idealStageAfter V stage x := by
  classical
  unfold idealStageAfter
  by_cases hc : idealCapHit U stage x
  · have hc' := (idealCapHit_iff_of_agree j h stage hs x).mp hc
    simp [hc, hc']
  · have hc' := mt (idealCapHit_iff_of_agree j h stage hs x).mpr hc
    simp [hc, hc']

lemma idealResponseMean_eq_of_agree {d T : ℕ}
    (hT : 0 < T) {U V : Fin T → Point d}
    (j : Fin T) (h : ∀ i, i ≤ j → U i = V i)
    (stageAfter : ℕ) (hs : stageAfter ≤ j.val)
    (x : Point d) :
    idealResponseMean hT U stageAfter x =
      idealResponseMean hT V stageAfter x := by
  unfold idealResponseMean
  apply congrArg (fun f : Point d → ℝ => gradient f x)
  apply prefixHardPotential_eq_of_agree
  intro i hi
  apply h i
  exact le_trans hi (by
    change (min stageAfter (T - 1)) ≤ j.val
    omega)

lemma idealStage_le_after {d T : ℕ}
    (U : Fin T → Point d) (stage : ℕ) (x : Point d) :
    stage ≤ idealStageAfter U stage x := by
  classical
  unfold idealStageAfter
  split_ifs <;> omega

lemma idealStageAfter_le_succ {d T : ℕ}
    (U : Fin T → Point d) (stage : ℕ) (x : Point d) :
    idealStageAfter U stage x ≤ stage + 1 := by
  classical
  unfold idealStageAfter
  split_ifs <;> omega

/-- The response-bearing transition has one source of truth for its cap,
truncation, and full transcript update. -/
lemma idealStepState_eq_of_agree {d T N n : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d}
    (j : Fin T) (h : ∀ i, i ≤ j → U i = V i)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (st : IdealState d n)
    (hstage : st.stage ≤ j.val)
    (hnext :
      (idealStepState hT U A r noise a st).stage ≤ j.val) :
    idealStepState hT U A r noise a st =
      idealStepState hT V A r noise a st := by
  let x := A.decide n r st.transcript
  have hafter :
      idealStageAfter U st.stage x =
        idealStageAfter V st.stage x :=
    idealStageAfter_eq_of_agree j h st.stage hstage x
  have hmean :
      idealResponseMean hT U
          (idealStageAfter U st.stage x) x =
        idealResponseMean hT V
          (idealStageAfter V st.stage x) x := by
    rw [← hafter]
    exact idealResponseMean_eq_of_agree hT j h
      (idealStageAfter U st.stage x)
      (by simpa [idealStepState, x] using hnext) x
  rw [hafter] at hmean
  cases st
  simp [idealStepState, x, hafter, hmean]

def idealResponsiveAfterAt {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (t : ℕ) : ℕ :=
  idealStageAfter U
    (idealStateAt hT U A r noise a t).stage
    (A.decide t r
      (idealStateAt hT U A r noise a t).transcript)

lemma idealAfterAt_eq_responsive_of_lt {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (t : ℕ) (ht : t < N) :
    idealAfterAt hT U A r noise a t =
      idealResponsiveAfterAt hT U A r noise a t := by
  simp [idealAfterAt, idealDecisionAt, idealResponsiveAfterAt, ht]

/-- Until a stage beyond j is reached, replacing unrevealed frame columns
does not change a single algorithm-visible query/response pair.  This is
pathwise and keeps the complete transcript. -/
theorem idealStateAt_eq_of_agree {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d}
    (j : Fin T) (h : ∀ i, i ≤ j → U i = V i)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (n : ℕ)
    (hbefore : ∀ t < n,
      idealResponsiveAfterAt hT U A r noise a t ≤ j.val) :
    idealStateAt hT U A r noise a n =
      idealStateAt hT V A r noise a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprev : ∀ t < n,
          idealResponsiveAfterAt hT U A r noise a t ≤ j.val :=
        fun t ht => hbefore t (by omega)
      have heq := ih hprev
      have hnext :
          (idealStepState hT U A r noise a
            (idealStateAt hT U A r noise a n)).stage ≤ j.val := by
        simpa [idealResponsiveAfterAt, idealStepState] using
          hbefore n (by omega)
      have hstage :
          (idealStateAt hT U A r noise a n).stage ≤ j.val := by
        apply le_trans
          (idealStage_le_after U
            (idealStateAt hT U A r noise a n).stage
            (A.decide n r
              (idealStateAt hT U A r noise a n).transcript))
        simpa [idealStepState, idealResponsiveAfterAt] using
          hbefore n (by omega)
      have hstep := idealStepState_eq_of_agree
        hT j h A r noise a
        (idealStateAt hT U A r noise a n)
        hstage hnext
      calc
        idealStateAt hT U A r noise a (n + 1) =
            idealStepState hT U A r noise a
              (idealStateAt hT U A r noise a n) := rfl
        _ = idealStepState hT V A r noise a
              (idealStateAt hT U A r noise a n) := hstep
        _ = idealStepState hT V A r noise a
              (idealStateAt hT V A r noise a n) := by rw [heq]
        _ = idealStateAt hT V A r noise a (n + 1) := rfl

/-- The first response-bearing or response-free decision whose post-cap
stage reaches j.  The default N+1 means that stage j never starts within
the hard N-response horizon plus final output decision. -/
def idealStageStart {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (j : ℕ) : ℕ := by
  classical
  exact if h : ∃ t : ℕ, t ≤ N ∧
      j ≤ idealAfterAt hT U A r noise a t then
    Nat.find h
  else N + 1

lemma idealStageStart_zero {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ) :
    idealStageStart hT U A r noise a 0 = 0 := by
  classical
  have hex : ∃ t : ℕ, t ≤ N ∧
      0 ≤ idealAfterAt hT U A r noise a t :=
    ⟨0, Nat.zero_le N, Nat.zero_le _⟩
  rw [idealStageStart, dif_pos hex]
  exact (Nat.find_eq_iff hex).2
    ⟨⟨Nat.zero_le N, Nat.zero_le _⟩, by intro t ht; omega⟩

lemma idealStageStart_le_succ {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (j : ℕ) :
    idealStageStart hT U A r noise a j ≤ N + 1 := by
  classical
  unfold idealStageStart
  split_ifs with h
  · have hs := Nat.find_spec h
    omega
  · exact le_rfl

lemma idealStageStart_hit {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (j : ℕ)
    (hstart : idealStageStart hT U A r noise a j ≤ N) :
    j ≤ idealAfterAt hT U A r noise a
      (idealStageStart hT U A r noise a j) := by
  classical
  unfold idealStageStart at hstart ⊢
  split_ifs at hstart ⊢ with h
  · exact (Nat.find_spec h).2
  · omega

lemma idealStageStart_before {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (j t : ℕ)
    (ht : t < idealStageStart hT U A r noise a j)
    (htN : t ≤ N) :
    idealAfterAt hT U A r noise a t < j := by
  classical
  unfold idealStageStart at ht
  split_ifs at ht with h
  · have hnot := Nat.find_min h ht
    exact Nat.lt_of_not_ge (fun hge => hnot ⟨htN, hge⟩)
  · exact Nat.lt_of_not_ge
      (fun hge => h ⟨t, htN, hge⟩)

/-- All responsive transcripts up to and including the decision that starts
stage k+1 depend only on the frame through column k.  The response at that
starting decision is intentionally excluded. -/
theorem idealStateAt_eq_before_stageStart {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d}
    (k : Fin T) (h : ∀ i, i ≤ k → U i = V i)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (t : ℕ) (htN : t ≤ N)
    (htStart :
      t ≤ idealStageStart hT U A r noise a (k.val + 1)) :
    idealStateAt hT U A r noise a t =
      idealStateAt hT V A r noise a t := by
  apply idealStateAt_eq_of_agree hT k h A r noise a t
  intro s hs
  have hsStart :
      s < idealStageStart hT U A r noise a (k.val + 1) :=
    lt_of_lt_of_le hs htStart
  have hsN : s < N := by omega
  have hBefore := idealStageStart_before hT U A r noise a
    (k.val + 1) s hsStart (by omega)
  rw [idealAfterAt_eq_responsive_of_lt hT U A r noise a s hsN] at hBefore
  omega

lemma idealDecisionAt_eq_of_state_eq {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d}
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (t : ℕ) (htN : t ≤ N)
    (hstate :
      idealStateAt hT U A r noise a t =
        idealStateAt hT V A r noise a t) :
    idealDecisionAt hT U A r noise a t =
      idealDecisionAt hT V A r noise a t := by
  classical
  by_cases ht : t < N
  · simp [idealDecisionAt, ht, hstate]
  · have heq : t = N := by omega
    subst t
    simp [idealDecisionAt, hstate]

lemma idealStageBefore_le_of_beforeStart {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (k : Fin T) (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (t : ℕ) (htN : t ≤ N)
    (htStart :
      t ≤ idealStageStart hT U A r noise a (k.val + 1)) :
    (idealStateAt hT U A r noise a t).stage ≤ k.val := by
  cases t with
  | zero =>
      simp [idealStateAt]
  | succ s =>
      have hsStart :
          s < idealStageStart hT U A r noise a (k.val + 1) := by
        omega
      have hsN : s < N := by omega
      have hBefore := idealStageStart_before hT U A r noise a
        (k.val + 1) s hsStart (by omega)
      rw [idealAfterAt_eq_responsive_of_lt hT U A r noise a s hsN] at hBefore
      change idealResponsiveAfterAt hT U A r noise a s ≤ k.val
      omega

lemma idealAfterAt_eq_of_agree_beforeStart {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d}
    (k : Fin T) (h : ∀ i, i ≤ k → U i = V i)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (t : ℕ) (htN : t ≤ N)
    (htStart :
      t ≤ idealStageStart hT U A r noise a (k.val + 1)) :
    idealAfterAt hT U A r noise a t =
      idealAfterAt hT V A r noise a t := by
  have hstate := idealStateAt_eq_before_stageStart
    hT k h A r noise a t htN htStart
  have hquery := idealDecisionAt_eq_of_state_eq
    hT A r noise a t htN hstate
  have hstage := idealStageBefore_le_of_beforeStart
    hT U k A r noise a t htN htStart
  unfold idealAfterAt
  rw [hstate, hquery]
  exact idealStageAfter_eq_of_agree k h
    (idealStateAt hT V A r noise a t).stage
    (by simpa [hstate] using hstage)
    (idealDecisionAt hT V A r noise a t)

/-- First hitting time is itself prefix-local, even when the stage never
starts and even when it starts at the final response-free output decision. -/
theorem idealStageStart_eq_of_agree {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d}
    (k : Fin T) (h : ∀ i, i ≤ k → U i = V i)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ) :
    idealStageStart hT U A r noise a (k.val + 1) =
      idealStageStart hT V A r noise a (k.val + 1) := by
  classical
  let τ := idealStageStart hT U A r noise a (k.val + 1)
  have hτ : τ ≤ N + 1 :=
    idealStageStart_le_succ hT U A r noise a (k.val + 1)
  by_cases hstarted : τ ≤ N
  · have hhitU :
        k.val + 1 ≤ idealAfterAt hT U A r noise a τ :=
      idealStageStart_hit hT U A r noise a
        (k.val + 1) hstarted
    have hhitV :
        k.val + 1 ≤ idealAfterAt hT V A r noise a τ := by
      rw [← idealAfterAt_eq_of_agree_beforeStart
        hT k h A r noise a τ hstarted (le_refl τ)]
      exact hhitU
    have hnotV (t : ℕ) (ht : t < τ) :
        ¬ (t ≤ N ∧
          k.val + 1 ≤ idealAfterAt hT V A r noise a t) := by
      rintro ⟨htN, hge⟩
      have hltU := idealStageStart_before hT U A r noise a
        (k.val + 1) t ht htN
      have heq := idealAfterAt_eq_of_agree_beforeStart
        hT k h A r noise a t htN (le_of_lt ht)
      omega
    have hVExists :
        ∃ t : ℕ, t ≤ N ∧
          k.val + 1 ≤ idealAfterAt hT V A r noise a t :=
      ⟨τ, hstarted, hhitV⟩
    change τ =
      idealStageStart hT V A r noise a (k.val + 1)
    rw [idealStageStart, dif_pos hVExists]
    exact ((Nat.find_eq_iff hVExists).2
      ⟨⟨hstarted, hhitV⟩, hnotV⟩).symm
  · have hτDefault : τ = N + 1 := by omega
    have hVNo :
        ¬ ∃ t : ℕ, t ≤ N ∧
          k.val + 1 ≤ idealAfterAt hT V A r noise a t := by
      rintro ⟨t, htN, hge⟩
      have htτ : t < τ := by omega
      have hltU := idealStageStart_before hT U A r noise a
        (k.val + 1) t htτ htN
      have heq := idealAfterAt_eq_of_agree_beforeStart
        hT k h A r noise a t htN (by omega)
      omega
    change τ =
      idealStageStart hT V A r noise a (k.val + 1)
    rw [hτDefault]
    rw [idealStageStart, dif_neg hVNo]

/-- A fixed-size representation of a variable-length, already returned
transcript.  The unused tail contains only a public default value. -/
def idealPadTranscript {d N t : ℕ}
    (tr : Transcript d t) : Transcript d N := by
  classical
  exact fun i => if h : i.val < t then tr ⟨i.val, h⟩ else (0, 0)

/-- A response-free record at a stage's first decision.  In the never-started
case every data field has a fixed default, and `time = N+1`.  At `time = N`,
the query is the algorithm's arbitrary final output and no response is
appended. -/
structure IdealPreResponseHistory (d N : ℕ) where
  started : Bool
  time : ℕ
  transcript : Transcript d N
  query : Point d

def idealPreHistoryAtTime {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ)
    (t : ℕ) : IdealPreResponseHistory d N := by
  classical
  exact if ht : t ≤ N then
    ⟨true, t,
      idealPadTranscript (idealStateAt hT U A r noise a t).transcript,
      idealDecisionAt hT U A r noise a t⟩
  else ⟨false, N + 1, fun _ => (0, 0), 0⟩

def idealStoppedPreHistory {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (k : Fin T) (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ) :
    IdealPreResponseHistory d N :=
  idealPreHistoryAtTime hT U A r noise a
    (idealStageStart hT U A r noise a (k.val + 1))

/-- The complete stopped, pre-response record is determined by the earlier
columns and the algorithm/noise tape.  This includes never-started paths. -/
theorem idealStoppedPreHistory_eq_of_agree {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d}
    (k : Fin T) (h : ∀ i, i ≤ k → U i = V i)
    (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ) :
    idealStoppedPreHistory hT U k A r noise a =
      idealStoppedPreHistory hT V k A r noise a := by
  classical
  have hτ := idealStageStart_eq_of_agree hT k h A r noise a
  unfold idealStoppedPreHistory
  rw [← hτ]
  let τ := idealStageStart hT U A r noise a (k.val + 1)
  change idealPreHistoryAtTime hT U A r noise a τ =
    idealPreHistoryAtTime hT V A r noise a τ
  by_cases hstarted : τ ≤ N
  · have hstate := idealStateAt_eq_before_stageStart
      hT k h A r noise a τ hstarted (le_refl τ)
    have hquery := idealDecisionAt_eq_of_state_eq
      hT A r noise a τ hstarted hstate
    simp [idealPreHistoryAtTime, hstarted, hstate, hquery]
  · simp [idealPreHistoryAtTime, hstarted]

/-- Embed an arbitrary revealed prefix back into the full frame coordinate
type by setting unrevealed columns to zero. -/
def idealPrefixExtension {d T : ℕ} (k : Fin T)
    (v : Fin (k.val + 1) → Point d) : Fin T → Point d := by
  classical
  exact fun i => if h : i.val < k.val + 1 then v ⟨i.val, h⟩ else 0

lemma measurable_idealPrefixExtension {d T : ℕ} (k : Fin T) :
    Measurable (idealPrefixExtension (d := d) k) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  by_cases h : i.val < k.val + 1
  · simpa [idealPrefixExtension, h] using
      (measurable_pi_apply (⟨i.val, h⟩ : Fin (k.val + 1)) :
        Measurable (fun v : Fin (k.val + 1) → Point d => v ⟨i.val, h⟩))
  · simp [idealPrefixExtension, h]

lemma idealPrefixExtension_agree {d T : ℕ}
    (U : Fin T → Point d) (k : Fin T) :
    ∀ i, i ≤ k →
      U i = idealPrefixExtension k
        (framePrefix (Nat.succ_le_iff.mpr k.isLt) U) i := by
  intro i hi
  have hlt : i.val < k.val + 1 := by omega
  simp [idealPrefixExtension, framePrefix, hlt]

/-- Explicit pathwise factorization through the revealed frame prefix and
the independent joint tape of algorithm private state and noise vectors. -/
theorem idealStoppedPreHistory_prefix_factorization {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (k : Fin T) (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ) :
    idealStoppedPreHistory hT U k A r noise a =
      idealStoppedPreHistory hT
        (idealPrefixExtension k
          (framePrefix (Nat.succ_le_iff.mpr k.isLt) U))
        k A r noise a :=
  idealStoppedPreHistory_eq_of_agree hT k
    (idealPrefixExtension_agree U k) A r noise a

/-- The product representation carries the standard measurable-space
structure needed by the conditional-distribution interface. -/
def idealPreResponseTuple {d N : ℕ}
    (h : IdealPreResponseHistory d N) :
    Bool × ℕ × Transcript d N × Point d :=
  (h.started, h.time, h.transcript, h.query)

/-- The canonical factor map from the revealed prefix and the joint private
tape.  Its measurability is the remaining analytic obligation. -/
def idealStoppedPreHistoryFromPrefix {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T) (A : RandomAlgorithm d N Private)
    (a : ℝ) :
    (Fin (k.val + 1) → Point d) ×
      (Private × (Fin N → Point d)) →
        Bool × ℕ × Transcript d N × Point d :=
  fun z => idealPreResponseTuple
    (idealStoppedPreHistory hT (idealPrefixExtension k z.1)
      k A z.2.1 z.2.2 a)

theorem idealStoppedPreHistoryFromPrefix_eq {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (k : Fin T) (A : RandomAlgorithm d N Private)
    (r : Private) (noise : Fin N → Point d) (a : ℝ) :
    idealPreResponseTuple (idealStoppedPreHistory hT U k A r noise a) =
      idealStoppedPreHistoryFromPrefix hT k A a
        (framePrefix (Nat.succ_le_iff.mpr k.isLt) U, (r, noise)) := by
  exact congrArg idealPreResponseTuple
    (idealStoppedPreHistory_prefix_factorization hT U k A r noise a)

lemma init_framePrefix_eq {d T : ℕ} (k : Fin T)
    (hk : k.val + 1 + 1 ≤ T) (U : Fin T → Point d) :
    Fin.init (framePrefix (d := d) hk U) =
      framePrefix (Nat.succ_le_iff.mpr k.isLt) U := by
  funext i
  rfl

/-- Conditional uniformity for the next frame column at the stopped
pre-response history of the actual full-history ideal process.  The sole
explicit premise not yet discharged is measurability of the concrete factor
map above; no independence of the history from raw Gaussian columns is
assumed. -/
theorem idealStoppedPreHistory_nextColumn_hasCondDistrib
    {d T N : ℕ} {Private Ω : Type*}
    [MeasurableSpace Private] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hT : 0 < T) (hTd : T ≤ d)
    (k : Fin T) (hk : k.val + 1 + 1 ≤ T)
    (A : RandomAlgorithm d N Private) (a : ℝ)
    (U : Ω → {v : Fin T → Point d // Orthonormal ℝ v})
    (Zvar : Ω → Private × (Fin N → Point d))
    (hU : Measurable U) (hZ : Measurable Zvar)
    (hInd : U ⟂ᵢ[P] Zvar)
    (hLaw : P.map U = preselectedOrthonormalFrameLaw d T hTd)
    (hFactorMeas :
      Measurable (idealStoppedPreHistoryFromPrefix hT k A a)) :
    HasCondDistrib
      (fun ω => (framePrefix hk (U ω).1) (Fin.last (k.val + 1)))
      (fun ω =>
        (Fin.init (framePrefix hk (U ω).1),
          idealPreResponseTuple
            (idealStoppedPreHistory hT (U ω).1 k A
              (Zvar ω).1 (Zvar ω).2 a)))
      ((frameNextKernel d (k.val + 1)).comap
        (Prod.fst :
          ((Fin (k.val + 1) → Point d) ×
            (Bool × ℕ × Transcript d N × Point d)) →
              (Fin (k.val + 1) → Point d))
        (measurable_fst : Measurable
          (Prod.fst :
            ((Fin (k.val + 1) → Point d) ×
              (Bool × ℕ × Transcript d N × Point d)) →
                (Fin (k.val + 1) → Point d))))
      P := by
  have hbase :=
    preselectedOrthonormalFrameLaw_column_independent_history
      P d (k.val + 1) T hTd hk U Zvar hU hZ hInd hLaw
      (idealStoppedPreHistoryFromPrefix hT k A a) hFactorMeas
  have hhist (ω : Ω) :
      idealStoppedPreHistoryFromPrefix hT k A a
        (Fin.init (framePrefix hk (U ω).1), Zvar ω) =
      idealPreResponseTuple
        (idealStoppedPreHistory hT (U ω).1 k A
          (Zvar ω).1 (Zvar ω).2 a) := by
    rw [init_framePrefix_eq k hk (U ω).1]
    exact (idealStoppedPreHistoryFromPrefix_eq hT (U ω).1
      k A (Zvar ω).1 (Zvar ω).2 a).symm
  simpa only [hhist] using hbase

end HeavyTailedNoise
