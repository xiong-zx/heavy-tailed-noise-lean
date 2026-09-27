import HeavyTailedNoise.Lower.Gated.RealIdealStoppedCoupling
import HeavyTailedNoise.Lower.Gated.HardGaussianInstance
import HeavyTailedNoise.Lower.Gated.ScaledObjectiveStationarity

/-!
Public-scalar normalization of a full-history strict-K=1 algorithm.

The transformed algorithm depends only on A and public lam,c.  It reencodes
each already returned pair (y,g_H) as (lamy,cg_H), sends that complete history
to A, and divides A's next query or arbitrary output by lam.  It preserves
the private law and response cap N and never receives the noise seed or U.

The generic transcript identity is instantiated with the canonical legal
F_U Gaussian instance and the existing full-H_U Gaussian oracle.  The final
statement transfers the response-free F_U output to the ideal H_U output
outside the responsive prefix-accident event.
-/

namespace HeavyTailedNoise

open MeasureTheory

noncomputable section

set_option autoImplicit false

def encodeTranscript {d n : ℕ} (lam c : ℝ) (tr : Transcript d n) : Transcript d n :=
  fun i => (lam • (tr i).1, c • (tr i).2)

theorem measurable_encodeTranscript {d n : ℕ} (lam c : ℝ) :
    Measurable (encodeTranscript (d := d) (n := n) lam c) := by
  apply measurable_pi_iff.mpr
  intro i
  have hx : Measurable (fun tr : Transcript d n => (tr i).1) :=
    measurable_fst.comp (measurable_pi_apply i)
  have hg : Measurable (fun tr : Transcript d n => (tr i).2) :=
    measurable_snd.comp (measurable_pi_apply i)
  exact ((measurable_const : Measurable (fun _ : Transcript d n => lam)).smul hx).prodMk
    ((measurable_const : Measurable (fun _ : Transcript d n => c)).smul hg)

/-- A frame-independent algorithm transformation using only public scales. -/
def rescaledAlgorithm {d N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (lam c : ℝ) (A : RandomAlgorithm d N Private) : RandomAlgorithm d N Private where
  privateLaw := A.privateLaw
  private_probability := A.private_probability
  decide := fun n r tr => lam⁻¹ • A.decide n r (encodeTranscript lam c tr)
  measurable_decide := by
    intro n
    have hh : Measurable (fun z : Private × Transcript d n =>
        (z.1, encodeTranscript lam c z.2)) :=
      measurable_fst.prodMk ((measurable_encodeTranscript lam c).comp measurable_snd)
    have hx : Measurable (fun z : Private × Transcript d n =>
        A.decide n z.1 (encodeTranscript lam c z.2)) :=
      (A.measurable_decide n).comp hh
    exact (measurable_const :
      Measurable (fun _ : Private × Transcript d n => lam⁻¹)).smul hx
  output := fun r tr => lam⁻¹ • A.output r (encodeTranscript lam c tr)
  measurable_output := by
    have hh : Measurable (fun z : Private × Transcript d N =>
        (z.1, encodeTranscript lam c z.2)) :=
      measurable_fst.prodMk ((measurable_encodeTranscript lam c).comp measurable_snd)
    have hx : Measurable (fun z : Private × Transcript d N =>
        A.output z.1 (encodeTranscript lam c z.2)) :=
      A.measurable_output.comp hh
    exact (measurable_const :
      Measurable (fun _ : Private × Transcript d N => lam⁻¹)).smul hx

theorem rescaledAlgorithm_privateLaw {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (lam c : ℝ) (A : RandomAlgorithm d N Private) :
    (rescaledAlgorithm lam c A).privateLaw = A.privateLaw := rfl

theorem encodeTranscript_snoc {d n : ℕ} (lam c : ℝ)
    (tr : Transcript d n) (x g : Point d) :
    encodeTranscript lam c (Fin.snoc tr (x, g) : Transcript d (n + 1)) =
      (Fin.snoc (encodeTranscript lam c tr) (lam • x, c • g) : Transcript d (n + 1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [encodeTranscript, Fin.snoc_last, Fin.snoc_castSucc]

theorem rescaledAlgorithm_decide_mul {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] {lam : ℝ} (hlam : 0 < lam) (c : ℝ)
    (A : RandomAlgorithm d N Private) (n : ℕ) (r : Private) (tr : Transcript d n) :
    lam • (rescaledAlgorithm lam c A).decide n r tr =
      A.decide n r (encodeTranscript lam c tr) := by
  simp only [rescaledAlgorithm, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]

/-- Exact reencoding of every returned query and gradient vector.  The
fixed-cap application below takes n=N, with no further oracle response. -/
theorem encode_runTranscript_rescaledAlgorithm
    {d N : ℕ} {Private Seed : Type*}
    [MeasurableSpace Private] [MeasurableSpace Seed]
    {lam : ℝ} (hlam : 0 < lam) (c : ℝ)
    (OF OH : GradientOracle d Seed) (A : RandomAlgorithm d N Private) (r : Private)
    (hresponse : ∀ y ξ, OF.response (lam • y) ξ = c • OH.response y ξ)
    (n : ℕ) (ξ : Fin n → Seed) :
    encodeTranscript lam c (runTranscript OH (rescaledAlgorithm lam c A) r n ξ) =
      runTranscript OF A r n ξ := by
  induction n with
  | zero =>
      funext i
      exact i.elim0
  | succ n ih =>
      let ζ : Fin n → Seed := fun i => ξ i.castSucc
      let trH := runTranscript OH (rescaledAlgorithm lam c A) r n ζ
      let trF := runTranscript OF A r n ζ
      have hhistory : encodeTranscript lam c trH = trF := ih ζ
      have hquery : lam • (rescaledAlgorithm lam c A).decide n r trH =
          A.decide n r trF := by
        rw [rescaledAlgorithm_decide_mul hlam, hhistory]
      have hresp : c • OH.response ((rescaledAlgorithm lam c A).decide n r trH)
          (ξ (Fin.last n)) = OF.response (A.decide n r trF) (ξ (Fin.last n)) := by
        rw [← hquery]
        exact (hresponse _ _).symm
      calc
        encodeTranscript lam c
            (runTranscript OH (rescaledAlgorithm lam c A) r (n + 1) ξ) =
          (Fin.snoc (encodeTranscript lam c trH)
            (lam • (rescaledAlgorithm lam c A).decide n r trH,
              c • OH.response ((rescaledAlgorithm lam c A).decide n r trH)
                (ξ (Fin.last n))) : Transcript d (n + 1)) := by
            rw [runTranscript, encodeTranscript_snoc]
        _ = (Fin.snoc trF
            (A.decide n r trF, OF.response (A.decide n r trF) (ξ (Fin.last n))) :
              Transcript d (n + 1)) := by rw [hhistory, hquery, hresp]
        _ = runTranscript OF A r (n + 1) ξ := rfl

theorem rescaledAlgorithm_output_identity
    {d N : ℕ} {Private Seed : Type*}
    [MeasurableSpace Private] [MeasurableSpace Seed]
    {lam : ℝ} (hlam : 0 < lam) (c : ℝ)
    (OF OH : GradientOracle d Seed) (A : RandomAlgorithm d N Private) (r : Private)
    (hresponse : ∀ y ξ, OF.response (lam • y) ξ = c • OH.response y ξ)
    (ξ : Fin N → Seed) :
    (rescaledAlgorithm lam c A).output r
        (runTranscript OH (rescaledAlgorithm lam c A) r N ξ) =
      lam⁻¹ • A.output r (runTranscript OF A r N ξ) := by
  change lam⁻¹ • A.output r
      (encodeTranscript lam c (runTranscript OH (rescaledAlgorithm lam c A) r N ξ)) = _
  rw [encode_runTranscript_rescaledAlgorithm hlam c OF OH A r hresponse]

theorem scaledHardGaussianResponse_rescaling
    {d T : ℕ} (hd : 0 < d) (hT : 0 < T) (U : Fin T → Point d)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (σ : ℝ) (y ξ : Point d) :
    gaussianResponse d (gradient (scaledHardPotential L ε U)) (σ / Real.sqrt d)
        ((hardScaleLambda L ε) • y) ξ =
      (80 * ε) • gaussianResponse d (gradient (hardPotential U))
        (σ / ((80 * ε) * Real.sqrt d)) y ξ := by
  have hlam : 0 < hardScaleLambda L ε := by unfold hardScaleLambda; positivity
  have hc : (80 * ε : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
  have hnoise : (80 * ε) * (σ / ((80 * ε) * Real.sqrt d)) = σ / Real.sqrt d := by
    field_simp [hc, hsqrt]
  unfold gaussianResponse
  rw [gradient_scaledHardPotential_eq hT U hL hε]
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul, hnoise]

/-- Instantiation with the canonical legal F_U instance; B depends on the
public scales and A, never on U. -/
theorem hardGaussian_transcript_rescaling
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hd : 0 < d) (hT : 0 < T) (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    {p q L ε Δ σ : ℝ} (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (hbudget : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ)
    (A : RandomAlgorithm d N Private) (r : Private) (ξ : Fin N → Point d) :
    encodeTranscript (hardScaleLambda L ε) (80 * ε)
      (runTranscript
        (unscaledHardGaussianOracle hT U hU (σ / ((80 * ε) * Real.sqrt d)))
        (rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A) r N ξ) =
      runTranscript
        (hardGaussianAdmissible hd hT U hU hp hq hL hε hΔ hσ hbudget).oracle
        A r N ξ := by
  have hlam : 0 < hardScaleLambda L ε := by unfold hardScaleLambda; positivity
  apply encode_runTranscript_rescaledAlgorithm hlam
  intro y ζ
  exact scaledHardGaussianResponse_rescaling hd hT U hL hε σ y ζ

/-- The arbitrary original F_U output, divided by lam, equals the actual ideal
H_U output on the same N-vector tape outside responsive prefix accidents. -/
theorem hardGaussian_normalizedOutput_eq_ideal
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hd : 0 < d) (hT : 0 < T) (U : Fin T → Point d) (hU : Orthonormal ℝ U)
    {p q L ε Δ σ : ℝ} (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hε : 0 < ε) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (hbudget : 330240000 * ε ^ 2 * (T : ℝ) ≤ L * Δ)
    (A : RandomAlgorithm d N Private) (r : Private) (ξ : Fin N → Point d)
    (hno : ∀ t < N, ¬ idealPrefixAccidentAt hT U
      (rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A) r ξ
      (σ / ((80 * ε) * Real.sqrt d)) t) :
    (hardScaleLambda L ε)⁻¹ • A.output r
      (runTranscript
        (hardGaussianAdmissible hd hT U hU hp hq hL hε hΔ hσ hbudget).oracle
        A r N ξ) =
      idealDecisionAt hT U (rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A)
        r ξ (σ / ((80 * ε) * Real.sqrt d)) N := by
  have htr := hardGaussian_transcript_rescaling hd hT U hU hp hq hL hε hΔ hσ
    hbudget A r ξ
  have hout : (rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A).output r
      (runTranscript
        (unscaledHardGaussianOracle hT U hU (σ / ((80 * ε) * Real.sqrt d)))
        (rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A) r N ξ) =
      (hardScaleLambda L ε)⁻¹ • A.output r
        (runTranscript
          (hardGaussianAdmissible hd hT U hU hp hq hL hε hΔ hσ hbudget).oracle
          A r N ξ) := by
    change (hardScaleLambda L ε)⁻¹ • A.output r _ = _
    rw [htr]
  exact hout.symm.trans (realHardOutput_eq_ideal_of_no_responsive_accidents
    hT U hU (rescaledAlgorithm (hardScaleLambda L ε) (80 * ε) A)
    r ξ (σ / ((80 * ε) * Real.sqrt d)) hno)

end

end HeavyTailedNoise
