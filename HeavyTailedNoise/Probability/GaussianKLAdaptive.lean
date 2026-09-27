import HeavyTailedNoise.Probability.GaussianKL
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
One-response information estimates for arbitrary measurable full-history
decision rules. The Gaussian laws below are exactly the response laws of the
existing additive oracle; no alternative oracle is introduced.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

namespace HeavyTailedNoise

/-- A uniform bound on the distance between two history-dependent Gaussian
response means gives the corresponding uniform measure-level KL bound. The
history type may encode every previous query and returned vector. -/
theorem gaussianResponseLaw_klDiv_le_of_means
    {H : Type*} [MeasurableSpace H]
    (d : ℕ) (hd : 0 < d) (σ₀ : ℝ) (hσ₀ : 0 < σ₀)
    (C : ℝ) (m n : H → Point d)
    (hdiam : ∀ h, ‖m h - n h‖ ≤ C) (h : H) :
    klDiv (gaussianResponseLaw d (m h) (σ₀ / Real.sqrt d))
      (gaussianResponseLaw d (n h) (σ₀ / Real.sqrt d)) ≤
      ENNReal.ofReal ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2)) := by
  rw [gaussianResponseLaw_klDiv d hd (m h) (n h) σ₀ hσ₀]
  apply ENNReal.ofReal_le_ofReal
  have hC : 0 ≤ C := (norm_nonneg (m h - n h)).trans (hdiam h)
  have hsq : ‖m h - n h‖ ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hC).mpr (hdiam h)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg d)) (by positivity)

/-- Under pointwise absolute continuity, the KL of two kernels with the same
input law is the integral of their conditional KL. The integrand is measurable
here because the kernel Radon–Nikodym derivative supplies an integral formula. -/
private theorem klDiv_compProd_eq_lintegral_conditional
    {H Y : Type*} [MeasurableSpace H] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated H Y]
    (P : Measure H) [IsProbabilityMeasure P]
    (κ η : Kernel H Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hAC : ∀ h, κ h ≪ η h) :
    klDiv (P ⊗ₘ κ) (P ⊗ₘ η) = ∫⁻ h, klDiv (κ h) (η h) ∂P := by
  have hJointAC : P ⊗ₘ κ ≪ P ⊗ₘ η :=
    (Measure.absolutelyContinuous_compProd_right_iff).2 (ae_of_all _ hAC)
  have hf : Measurable (fun p : H × Y =>
      ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal)) := by
    fun_prop
  rw [klDiv_eq_lintegral_klFun_of_ac hJointAC]
  calc
    (∫⁻ p, ENNReal.ofReal
        (klFun (((P ⊗ₘ κ).rnDeriv (P ⊗ₘ η) p).toReal)) ∂(P ⊗ₘ η)) =
      ∫⁻ p, ENNReal.ofReal
        (klFun (κ.rnDeriv η p.1 p.2).toReal) ∂(P ⊗ₘ η) := by
          apply lintegral_congr_ae
          filter_upwards [rnDeriv_measure_compProd_right P κ η] with p hp
          rw [hp]
    _ = ∫⁻ h, ∫⁻ y, ENNReal.ofReal
          (klFun (κ.rnDeriv η h y).toReal) ∂(η h) ∂P := by
          rw [Measure.lintegral_compProd hf]
    _ = ∫⁻ h, klDiv (κ h) (η h) ∂P := by
          apply lintegral_congr
          intro h
          calc
            (∫⁻ y, ENNReal.ofReal
                (klFun (κ.rnDeriv η h y).toReal) ∂(η h)) =
              ∫⁻ y, ENNReal.ofReal
                (klFun (((κ h).rnDeriv (η h) y).toReal)) ∂(η h) := by
                  apply lintegral_congr_ae
                  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure
                    (κ := κ) (η := η) (a := h)] with y hy
                  rw [hy]
            _ = klDiv (κ h) (η h) :=
              (klDiv_eq_lintegral_klFun_of_ac (hAC h)).symm

/-- A single adaptive response, with an arbitrary measurable full-history
input law, adds at most the Gaussian diameter cost to KL. -/
theorem gaussian_compProd_klDiv_le
    {H : Type*} [MeasurableSpace H]
    (d : ℕ)
    [MeasurableSpace.CountableOrCountablyGenerated H (Point d)]
    (hd : 0 < d) (σ₀ : ℝ) (hσ₀ : 0 < σ₀)
    (C : ℝ) (P : Measure H) [IsProbabilityMeasure P]
    (κ η : Kernel H (Point d)) [IsMarkovKernel κ] [IsMarkovKernel η]
    (m n : H → Point d)
    (hκ : ∀ h, κ h = gaussianResponseLaw d (m h) (σ₀ / Real.sqrt d))
    (hη : ∀ h, η h = gaussianResponseLaw d (n h) (σ₀ / Real.sqrt d))
    (hdiam : ∀ h, ‖m h - n h‖ ≤ C) :
    klDiv (P ⊗ₘ κ) (P ⊗ₘ η) ≤
      ENNReal.ofReal ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2)) := by
  have hAC (h : H) : κ h ≪ η h := by
    rw [hκ h, hη h]
    have hfinite : klDiv
        (gaussianResponseLaw d (m h) (σ₀ / Real.sqrt d))
        (gaussianResponseLaw d (n h) (σ₀ / Real.sqrt d)) ≠ ∞ := by
      rw [gaussianResponseLaw_klDiv d hd (m h) (n h) σ₀ hσ₀]
      simp
    exact (klDiv_ne_top_iff.mp hfinite).1
  rw [klDiv_compProd_eq_lintegral_conditional P κ η hAC]
  calc
    (∫⁻ h, klDiv (κ h) (η h) ∂P) ≤
        ∫⁻ _ : H, ENNReal.ofReal ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2)) ∂P := by
          apply lintegral_mono
          intro h
          change klDiv (κ h) (η h) ≤
            ENNReal.ofReal ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2))
          rw [hκ h, hη h]
          exact gaussianResponseLaw_klDiv_le_of_means d hd σ₀ hσ₀ C m n hdiam h
    _ = _ := by simp

/-- A fixed-length adaptive response law on a measurable state that may retain
the complete query/response history. At each step the same state update is
applied after the hidden-direction-dependent Gaussian response kernel. -/
def adaptiveGaussianLaw {H : Type*} [MeasurableSpace H] (d : ℕ)
    (P₀ : Measure H) (κ : ℕ → Kernel H (Point d))
    (update : ℕ → H × Point d → H) : ℕ → Measure H
  | 0 => P₀
  | t + 1 => ((adaptiveGaussianLaw d P₀ κ update t) ⊗ₘ κ t).map (update t)

private lemma adaptiveGaussianLaw_probability
    {H : Type*} [MeasurableSpace H] (d : ℕ)
    (P₀ : Measure H) [IsProbabilityMeasure P₀]
    (κ : ℕ → Kernel H (Point d))
    (hκ : ∀ t, IsMarkovKernel (κ t))
    (update : ℕ → H × Point d → H) (t : ℕ) :
    IsProbabilityMeasure (adaptiveGaussianLaw d P₀ κ update t) := by
  induction t with
  | zero =>
      change IsProbabilityMeasure P₀
      infer_instance
  | succ t ih =>
      letI : IsProbabilityMeasure (adaptiveGaussianLaw d P₀ κ update t) := ih
      letI : IsMarkovKernel (κ t) := hκ t
      change IsProbabilityMeasure
        (((adaptiveGaussianLaw d P₀ κ update t) ⊗ₘ κ t).map (update t))
      infer_instance

/-- Fixed-horizon adaptive Gaussian KL bound. The measurable state may contain
all past responses and decisions; its update and the next-response means may
depend on that complete state at every step. The two hidden directions use the
same update and may have different history-dependent Gaussian means. -/
theorem adaptiveGaussianLaw_klDiv_le
    {H : Type*} [MeasurableSpace H]
    (d : ℕ) [MeasurableSpace.CountableOrCountablyGenerated H (Point d)]
    (hd : 0 < d) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (C : ℝ)
    (P₀ : Measure H) [IsProbabilityMeasure P₀]
    (κ η : ℕ → Kernel H (Point d))
    (hκMarkov : ∀ t, IsMarkovKernel (κ t))
    (hηMarkov : ∀ t, IsMarkovKernel (η t))
    (m n : ℕ → H → Point d)
    (hκLaw : ∀ t h, κ t h = gaussianResponseLaw d (m t h) (σ₀ / Real.sqrt d))
    (hηLaw : ∀ t h, η t h = gaussianResponseLaw d (n t h) (σ₀ / Real.sqrt d))
    (hdiam : ∀ t h, ‖m t h - n t h‖ ≤ C)
    (update : ℕ → H × Point d → H)
    (hUpdate : ∀ t, Measurable (update t)) (N : ℕ) :
    klDiv (adaptiveGaussianLaw d P₀ κ update N)
      (adaptiveGaussianLaw d P₀ η update N) ≤
      (N : ENNReal) * ENNReal.ofReal ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2)) := by
  induction N with
  | zero =>
      simp [adaptiveGaussianLaw]
  | succ t ih =>
      let Pκ : Measure H := adaptiveGaussianLaw d P₀ κ update t
      let Pη : Measure H := adaptiveGaussianLaw d P₀ η update t
      letI : IsProbabilityMeasure Pκ :=
        adaptiveGaussianLaw_probability d P₀ κ hκMarkov update t
      letI : IsProbabilityMeasure Pη :=
        adaptiveGaussianLaw_probability d P₀ η hηMarkov update t
      letI : IsMarkovKernel (κ t) := hκMarkov t
      letI : IsMarkovKernel (η t) := hηMarkov t
      have hstep : klDiv (Pκ ⊗ₘ κ t) (Pκ ⊗ₘ η t) ≤
          ENNReal.ofReal ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2)) :=
        gaussian_compProd_klDiv_le d hd σ₀ hσ₀ C Pκ (κ t) (η t)
          (m t) (n t) (hκLaw t) (hηLaw t) (hdiam t)
      calc
        klDiv (adaptiveGaussianLaw d P₀ κ update (t + 1))
          (adaptiveGaussianLaw d P₀ η update (t + 1)) =
            klDiv ((Pκ ⊗ₘ κ t).map (update t))
              ((Pη ⊗ₘ η t).map (update t)) := rfl
        _ ≤ klDiv (Pκ ⊗ₘ κ t) (Pη ⊗ₘ η t) :=
          klDiv_map_le _ _ (hUpdate t)
        _ = klDiv Pκ Pη + klDiv (Pκ ⊗ₘ κ t) (Pκ ⊗ₘ η t) :=
          klDiv_compProd_eq_add Pκ Pη (κ t) (η t)
        _ ≤ (t : ENNReal) * ENNReal.ofReal
              ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2)) +
              ENNReal.ofReal ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2)) := by
          exact add_le_add ih hstep
        _ = ((t + 1 : ℕ) : ENNReal) * ENNReal.ofReal
              ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2)) := by
          simp [Nat.cast_add, add_mul]

/-- Fill coordinate `t` of a fixed-length response transcript. The branch for
`t ≥ N` makes the update total but is never used during the first `N` steps. -/
def responseTranscriptUpdate (N d t : ℕ) :
    ((Fin N → Point d) × Point d) → (Fin N → Point d) :=
  fun p => if ht : t < N then Function.update p.1 ⟨t, ht⟩ p.2 else p.1

lemma measurable_responseTranscriptUpdate (N d t : ℕ) :
    Measurable (responseTranscriptUpdate N d t) := by
  classical
  unfold responseTranscriptUpdate
  by_cases ht : t < N
  · simp only [dif_pos ht]
    exact measurable_update'
  · simp only [dif_neg ht]
    exact measurable_fst

/-- The law of the ordered `N` returned vectors, built from the actual
history-indexed Gaussian response kernels. -/
def finiteGaussianResponseTranscriptLaw (N d : ℕ)
    (κ : ℕ → Kernel (Fin N → Point d) (Point d)) :
    Measure (Fin N → Point d) :=
  adaptiveGaussianLaw d (Measure.dirac 0) κ (responseTranscriptUpdate N d) N

/-- Exact fixed-budget transcript KL bound for two hidden directions. Every
next-response mean may depend on the complete preceding vector transcript;
the same adaptive decision/update map is used under both directions. -/
theorem finiteGaussianResponseTranscript_klDiv_le
    (N d : ℕ) (hd : 0 < d) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (C : ℝ)
    (κ η : ℕ → Kernel (Fin N → Point d) (Point d))
    (hκMarkov : ∀ t, IsMarkovKernel (κ t))
    (hηMarkov : ∀ t, IsMarkovKernel (η t))
    (m n : ℕ → (Fin N → Point d) → Point d)
    (hκLaw : ∀ t h, κ t h = gaussianResponseLaw d (m t h) (σ₀ / Real.sqrt d))
    (hηLaw : ∀ t h, η t h = gaussianResponseLaw d (n t h) (σ₀ / Real.sqrt d))
    (hdiam : ∀ t h, ‖m t h - n t h‖ ≤ C) :
    klDiv (finiteGaussianResponseTranscriptLaw N d κ)
      (finiteGaussianResponseTranscriptLaw N d η) ≤
      (N : ENNReal) * ENNReal.ofReal ((d : ℝ) * C ^ 2 / (2 * σ₀ ^ 2)) := by
  unfold finiteGaussianResponseTranscriptLaw
  exact adaptiveGaussianLaw_klDiv_le d hd σ₀ hσ₀ C (Measure.dirac 0)
    κ η hκMarkov hηMarkov m n hκLaw hηLaw hdiam
    (responseTranscriptUpdate N d)
    (measurable_responseTranscriptUpdate N d) N

end HeavyTailedNoise
