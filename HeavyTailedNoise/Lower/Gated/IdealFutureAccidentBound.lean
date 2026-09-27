import HeavyTailedNoise.Lower.Gated.RealIdealStoppedCoupling
import HeavyTailedNoise.Lower.Gated.IdealStageMonotonicity

/-!
The prefix-factorization input for frozen proof Section 4, Lemma 7(ii).

For one future column `i>0`, put `k=i-1`. Mask the actual ideal query to zero
once its pre-response stage exceeds `k`. This *global* masked query depends
only on columns through `k` and the fixed private/noise tapes. Its coordinate
event is exactly the event that column `i` is still future and has an accident.
Thus all current stages are absorbed into one event for each future column;
there is no extra union over stages and no additional factor of `T`.

The factorization covers every `t≤N`, including the arbitrary response-free
output at `t=N`, and imposes no query-location restriction. Conditioning on a
complete independent noise tape is an analysis operation; the algorithm still
receives only the shared full-history protocol's query/response transcript.

This file proves the deterministic event reduction and projected norm bound.
It does not yet prove factor-map measurability, its integration against the
checked next-column conditional law, or the full accident probability bound.
No suffix conditional law or probability estimate is assumed as an axiom.
-/

namespace HeavyTailedNoise

noncomputable section

/-- Every earlier responsive post-cap stage is bounded by the present
pre-response stage, including the pre-output state at time `N`. -/
theorem idealResponsiveAfterAt_le_current_stage
    {d T N s t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (hst : s < t) (htN : t ≤ N) :
    idealResponsiveAfterAt hT U A r ξ a s ≤
      (idealStateAt hT U A r ξ a t).stage := by
  cases t with
  | zero => omega
  | succ n =>
    have hn : n < N := by omega
    have hs : s < N := by omega
    have hmono := idealAfterAt_mono_of_le hT U A r ξ a
      s n (by omega) hn.le
    rw [idealAfterAt_eq_responsive_of_lt hT U A r ξ a s hs] at hmono
    rw [← idealStateAt_stage_succ_eq_after hT U A r ξ a hn] at hmono
    exact hmono

/-- A current stage at most `k` suffices for equality of the entire earlier
transcript under replacement of columns after `k`. No assumption on earlier
stages is left to the caller. -/
theorem idealStateAt_eq_of_prefix_agree_current_stage
    {d T N t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d} (k : Fin T)
    (h : ∀ i, i ≤ k → U i = V i)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (htN : t ≤ N)
    (hs : (idealStateAt hT U A r ξ a t).stage ≤ k.val) :
    idealStateAt hT U A r ξ a t = idealStateAt hT V A r ξ a t := by
  apply idealStateAt_eq_of_agree hT k h A r ξ a t
  intro s hst
  exact (idealResponsiveAfterAt_le_current_stage hT U A r ξ a hst htN).trans hs

/-- The gate for masking the query is itself invariant under replacement of
the unrevealed suffix, even on paths that have already passed that gate. -/
theorem idealCurrentStage_le_iff_of_prefix_agree
    {d T N t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d} (k : Fin T)
    (h : ∀ i, i ≤ k → U i = V i)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (htN : t ≤ N) :
    (idealStateAt hT U A r ξ a t).stage ≤ k.val ↔
      (idealStateAt hT V A r ξ a t).stage ≤ k.val := by
  constructor
  · intro hs
    have heq := idealStateAt_eq_of_prefix_agree_current_stage
      hT k h A r ξ a htN hs
    rwa [heq] at hs
  · intro hs
    have heq := idealStateAt_eq_of_prefix_agree_current_stage
      hT k (fun i hi => (h i hi).symm) A r ξ a htN hs
    rwa [heq] at hs

/-- Mask only in the probability analysis, leaving the actual algorithm and
ideal recursion unchanged. Zero contributes no positive-threshold accident. -/
def idealPrefixMaskedQueryAt
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (t : ℕ) : Point d :=
  if (idealStateAt hT U A r ξ a t).stage ≤ k.val then
    idealDecisionAt hT U A r ξ a t else 0

theorem idealPrefixMaskedQueryAt_eq_of_prefix_agree
    {d T N t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) {U V : Fin T → Point d} (k : Fin T)
    (h : ∀ i, i ≤ k → U i = V i)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (htN : t ≤ N) :
    idealPrefixMaskedQueryAt hT U k A r ξ a t =
      idealPrefixMaskedQueryAt hT V k A r ξ a t := by
  have hgate := idealCurrentStage_le_iff_of_prefix_agree hT k h A r ξ a htN
  by_cases hs : (idealStateAt hT U A r ξ a t).stage ≤ k.val
  · have hsV := hgate.mp hs
    have hstate := idealStateAt_eq_of_prefix_agree_current_stage
      hT k h A r ξ a htN hs
    have hquery := idealDecisionAt_eq_of_state_eq hT A r ξ a t htN hstate
    simp only [idealPrefixMaskedQueryAt, if_pos hs, if_pos hsV, hquery]
  · have hsV : ¬ (idealStateAt hT V A r ξ a t).stage ≤ k.val :=
      mt hgate.mpr hs
    simp only [idealPrefixMaskedQueryAt, if_neg hs, if_neg hsV]

/-- An explicit factor through the earlier frame prefix, using the existing
canonical zero extension rather than a new ideal-protocol implementation. -/
def idealPrefixMaskedQueryFromPrefix
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (t : ℕ)
    (v : Fin (k.val + 1) → Point d) : Point d :=
  idealPrefixMaskedQueryAt hT (idealPrefixExtension k v) k A r ξ a t

theorem idealPrefixMaskedQueryAt_prefix_factorization
    {d T N t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (htN : t ≤ N) :
    idealPrefixMaskedQueryAt hT U k A r ξ a t =
      idealPrefixMaskedQueryFromPrefix hT k A r ξ a t
        (framePrefix (Nat.succ_le_iff.mpr k.isLt) U) := by
  exact idealPrefixMaskedQueryAt_eq_of_prefix_agree hT k
    (idealPrefixExtension_agree U k) A r ξ a htN

/-- Every possible value of the factor has the original strict projected
radius bound, including its zero value on masked paths. -/
theorem norm_projected_idealPrefixMaskedQueryFromPrefix_lt_radius
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (t : ℕ)
    (v : Fin (k.val + 1) → Point d) :
    ‖softProjection (hardRadius T)
      (idealPrefixMaskedQueryFromPrefix hT k A r ξ a t v)‖ < hardRadius T := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < hardRadius T := by unfold hardRadius; positivity
  exact norm_softProjection_lt_radius hR _

/-- The column `i=k+1` coordinate event, restricted to stages where it is
unrevealed, is exactly a single coordinate event of the global prefix factor.
There is no union over the value of the current stage. -/
theorem idealFutureCoordinate_event_iff_prefix_masked
    {d T N t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k i : Fin T)
    (hi : i.val = k.val + 1)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (htN : t ≤ N) :
    ((idealStateAt hT U A r ξ a t).stage < i.val ∧
      (1 / 32 : ℝ) ≤ |frameCoordinates U
        (softProjection (hardRadius T) (idealDecisionAt hT U A r ξ a t)) i|) ↔
    (1 / 32 : ℝ) ≤ |inner ℝ
      (softProjection (hardRadius T)
        (idealPrefixMaskedQueryFromPrefix hT k A r ξ a t
          (framePrefix (Nat.succ_le_iff.mpr k.isLt) U))) (U i)| := by
  rw [← idealPrefixMaskedQueryAt_prefix_factorization hT U k A r ξ a htN]
  by_cases hs : (idealStateAt hT U A r ξ a t).stage ≤ k.val
  · have hfuture : (idealStateAt hT U A r ξ a t).stage < i.val := by omega
    rw [idealPrefixMaskedQueryAt, if_pos hs]
    constructor
    · intro h
      simpa only [frameCoordinates, real_inner_comm] using h.2
    · intro h
      exact ⟨hfuture, by simpa only [frameCoordinates, real_inner_comm] using h⟩
  · have hfuture : ¬ (idealStateAt hT U A r ξ a t).stage < i.val := by omega
    norm_num [idealPrefixMaskedQueryAt, hs, hfuture, softProjection]

/-- A positive future column has one uniquely determined predecessor, so
the later union is indexed by columns alone. -/
def idealFuturePredecessor {T : ℕ} (i : Fin T) (hi : 0 < i.val) : Fin T :=
  ⟨i.val - 1, by omega⟩

/-- Exact per-decision accident reduction to one prefix-masked coordinate
event for each future column. The witness `hi` is a proof, not another index.
-/
theorem idealPrefixAccidentAt_iff_futureMaskedCoordinates
    {d T N t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (htN : t ≤ N) :
    idealPrefixAccidentAt hT U A r ξ a t ↔
      ∃ (i : Fin T) (hi : 0 < i.val),
        (1 / 32 : ℝ) ≤ |inner ℝ
          (softProjection (hardRadius T)
            (idealPrefixMaskedQueryFromPrefix hT (idealFuturePredecessor i hi)
              A r ξ a t
              (framePrefix
                (Nat.succ_le_iff.mpr (idealFuturePredecessor i hi).isLt) U))) (U i)| := by
  constructor
  · intro hacc
    change ∃ i, idealPrefixIndex hT (idealStateAt hT U A r ξ a t).stage < i ∧
      (1 / 32 : ℝ) ≤ |frameCoordinates U
        (softProjection (hardRadius T) (idealDecisionAt hT U A r ξ a t)) i| at hacc
    obtain ⟨i, hfuture, hcoord⟩ := hacc
    have hiT := i.isLt
    change min (idealStateAt hT U A r ξ a t).stage (T - 1) < i.val at hfuture
    have hs : (idealStateAt hT U A r ξ a t).stage < i.val := by omega
    have hi : 0 < i.val := by omega
    have hik : i.val = (idealFuturePredecessor i hi).val + 1 := by
      dsimp [idealFuturePredecessor]
      omega
    exact ⟨i, hi, (idealFutureCoordinate_event_iff_prefix_masked hT U
      (idealFuturePredecessor i hi) i hik A r ξ a htN).mp ⟨hs, hcoord⟩⟩
  · rintro ⟨i, hi, hcoord⟩
    have hik : i.val = (idealFuturePredecessor i hi).val + 1 := by
      dsimp [idealFuturePredecessor]
      omega
    obtain ⟨hs, hcoordActual⟩ :=
      (idealFutureCoordinate_event_iff_prefix_masked hT U
        (idealFuturePredecessor i hi) i hik A r ξ a htN).mpr hcoord
    change ∃ i, idealPrefixIndex hT (idealStateAt hT U A r ξ a t).stage < i ∧
      (1 / 32 : ℝ) ≤ |frameCoordinates U
        (softProjection (hardRadius T) (idealDecisionAt hT U A r ξ a t)) i|
    refine ⟨i, ?_, hcoordActual⟩
    change min (idealStateAt hT U A r ξ a t).stage (T - 1) < i.val
    omega

end

end HeavyTailedNoise
