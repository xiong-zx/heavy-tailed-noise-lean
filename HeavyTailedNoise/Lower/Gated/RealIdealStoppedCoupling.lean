import HeavyTailedNoise.Lower.Gated.IdealFrozenTailPrefix
import HeavyTailedNoise.Lower.Gated.HardObjectiveSmoothness
import HeavyTailedNoise.Probability.GaussianOracle

/-!
Deterministic real/ideal coupling for the unscaled hard objective H_U.

The real experiment uses the existing Gaussian oracle and runTranscript
with the same full-history algorithm, private tape, and N noise vectors as
the ideal process.  Before a prefix accident, the actual gradient locality
certificate makes their complete transcripts identical.  Their next query
therefore agrees even at the first accidental decision.  At time N the
arbitrary output agrees and receives no further response.

This file does not assert the algorithm/response normalization bridge from
the final scaled F_U experiment to this unscaled H_U experiment.
-/

namespace HeavyTailedNoise

noncomputable section

/-- The actual full-H_U additive Gaussian oracle, instantiated through the
single existing Gaussian-oracle constructor. -/
def unscaledHardGaussianOracle
    {d T : ℕ} (hT : 0 < T) (U : Fin T → Point d)
    (hU : Orthonormal ℝ U) (a : ℝ) : GradientOracle d (Point d) :=
  gaussianOracle d (gradient (hardPotential U))
    (lipschitzWith_gradient_hardPotential hU hT).continuous a

/-- Read the first n responses of the actual experiment from its one N-vector
tape.  This is a view of runTranscript, not a second transcript recursion. -/
def realHardTranscriptAt
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (n : ℕ) (hn : n ≤ N) : Transcript d n :=
  runTranscript (unscaledHardGaussianOracle hT U hU a) A r n
    (idealTailPrefix hn ξ)

/-- The accident tested at an ideal decision, using its actual pre-response
stage.  At the terminal prefix the accident set has no unrevealed columns. -/
def idealPrefixAccidentAt
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (t : ℕ) : Prop :=
  softProjection (hardRadius T) (idealDecisionAt hT U A r ξ a t) ∈
    prefixAccidentSet U
      (idealPrefixIndex hT (idealStateAt hT U A r ξ a t).stage)

/-- The concrete one-query reveal rule has the full H_U response mean
outside its prefix accident set, for arbitrary ambient query locations. -/
theorem idealResponseMean_eq_full_of_no_prefix_accident
    {d T : ℕ} (hT : 0 < T) {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (stage : ℕ) (x : Point d)
    (hno : softProjection (hardRadius T) x ∉
      prefixAccidentSet U (idealPrefixIndex hT stage)) :
    idealResponseMean hT U (idealStageAfter U stage x) x =
      gradient (hardPotential U) x := by
  classical
  by_cases hnext : stage + 1 < T
  · let j : Fin T := ⟨stage, by omega⟩
    let k : Fin T := ⟨stage + 1, hnext⟩
    have hidx : idealPrefixIndex hT stage = j := by
      apply Fin.ext
      simp only [idealPrefixIndex, j]
      omega
    have hidxNext : idealPrefixIndex hT (stage + 1) = k := by
      apply Fin.ext
      simp only [idealPrefixIndex, k]
      omega
    have hno' : softProjection (hardRadius T) x ∉ prefixAccidentSet U j := by
      simpa only [hidx] using hno
    have hfull := gradient_hardPotential_eq_prefix_after_reveal
      hU j k (by rfl) x hno'
    by_cases hcap : softProjection (hardRadius T) x ∈ prefixCapSet U j
    · have hc : idealCapHit U stage x := ⟨j.isLt, hcap⟩
      simpa only [idealResponseMean, idealStageAfter, ite_eq_left hc,
        hidxNext, ite_eq_left hcap] using hfull.symm
    · have hc : ¬ idealCapHit U stage x := by
        rintro ⟨hj, hmem⟩
        exact hcap hmem
      simpa only [idealResponseMean, idealStageAfter, ite_eq_right hc,
        hidx, ite_eq_right hcap] using hfull.symm
  · have hs := idealStage_le_after U stage x
    have hlast : (idealPrefixIndex hT (idealStageAfter U stage x)).val + 1 = T := by
      simp only [idealPrefixIndex]
      omega
    unfold idealResponseMean
    rw [prefixHardPotential_eq_full_at_last U _ hlast]

/-- One response step preserves exact full-transcript equality if the next
common query has no prefix accident. -/
theorem realHardTranscriptAt_succ_eq_ideal_of_no_accident
    {d T N n : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (hn : n < N)
    (hprev : realHardTranscriptAt hT U hU A r ξ a n hn.le =
      (idealStateAt hT U A r ξ a n).transcript)
    (hno : ¬ idealPrefixAccidentAt hT U A r ξ a n) :
    realHardTranscriptAt hT U hU A r ξ a (n + 1) (by omega) =
      (idealStateAt hT U A r ξ a (n + 1)).transcript := by
  have hp : (fun i : Fin n =>
      idealTailPrefix (show n + 1 ≤ N by omega) ξ i.castSucc) =
      idealTailPrefix hn.le ξ := by
    funext i
    rfl
  have hlast : idealTailPrefix (show n + 1 ≤ N by omega) ξ (Fin.last n) =
      ξ ⟨n, hn⟩ := rfl
  have hprev' : runTranscript (unscaledHardGaussianOracle hT U hU a)
      A r n (idealTailPrefix hn.le ξ) =
      (idealStateAt hT U A r ξ a n).transcript := hprev
  have hdecision : A.decide n r (idealStateAt hT U A r ξ a n).transcript =
      idealDecisionAt hT U A r ξ a n := by
    simp only [idealDecisionAt, dite_eq_left hn]
  have hmean := idealResponseMean_eq_full_of_no_prefix_accident hT hU
    (idealStateAt hT U A r ξ a n).stage
    (idealDecisionAt hT U A r ξ a n) hno
  change idealResponseMean hT U (idealAfterAt hT U A r ξ a n)
      (idealDecisionAt hT U A r ξ a n) =
      gradient (hardPotential U) (idealDecisionAt hT U A r ξ a n) at hmean
  rw [realHardTranscriptAt, runTranscript, hp, hprev', hdecision,
    idealStateAt_transcript_succ_eq hT U A r ξ a hn]
  simp only [unscaledHardGaussianOracle, gaussianOracle, gaussianResponse,
    hlast, hmean, idealNoiseAt, dite_eq_left hn]

/-- Exact real/ideal transcript coupling up to any n ≤ N before the first
prefix accident.  No zero-respecting condition is placed on the algorithm. -/
theorem realHardTranscriptAt_eq_ideal_before_accident
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (n : ℕ) (hn : n ≤ N)
    (hno : ∀ t < n, ¬ idealPrefixAccidentAt hT U A r ξ a t) :
    realHardTranscriptAt hT U hU A r ξ a n hn =
      (idealStateAt hT U A r ξ a n).transcript := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < N := by omega
      have hnoPrev : ∀ t < n, ¬ idealPrefixAccidentAt hT U A r ξ a t :=
        fun t ht => hno t (by omega)
      exact realHardTranscriptAt_succ_eq_ideal_of_no_accident
        hT U hU A r ξ a hnlt (ih hnlt.le hnoPrev) (hno n (by omega))

/-- The next responsive query agrees from the earlier common transcript,
including the first query at which a prefix accident might occur. -/
theorem realHardQuery_eq_ideal_before_accident
    {d T N n : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (hn : n < N)
    (hno : ∀ t < n, ¬ idealPrefixAccidentAt hT U A r ξ a t) :
    A.decide n r (realHardTranscriptAt hT U hU A r ξ a n hn.le) =
      idealDecisionAt hT U A r ξ a n := by
  have htr := realHardTranscriptAt_eq_ideal_before_accident
    hT U hU A r ξ a n hn.le hno
  simpa only [idealDecisionAt, dite_eq_left hn] using
    congrArg (A.decide n r) htr

/-- Equality of the arbitrary response-free output.  Only the N responsive
queries need the no-accident premise; no N+1-st response is issued. -/
theorem realHardOutput_eq_ideal_of_no_responsive_accidents
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ)
    (hno : ∀ t < N, ¬ idealPrefixAccidentAt hT U A r ξ a t) :
    A.output r
      (runTranscript (unscaledHardGaussianOracle hT U hU a) A r N ξ) =
      idealDecisionAt hT U A r ξ a N := by
  have hp : idealTailPrefix (le_refl N) ξ = ξ := by
    funext i
    rfl
  have htr := realHardTranscriptAt_eq_ideal_before_accident
    hT U hU A r ξ a N le_rfl hno
  simp only [realHardTranscriptAt, hp] at htr
  simpa [idealDecisionAt] using congrArg (A.output r) htr

end

end HeavyTailedNoise
