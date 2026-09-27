import HeavyTailedNoise.Probability.GaussianOracle
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
Measure-level information facts for the existing additive Gaussian oracle.
`gaussianResponseLaw` is exactly the pushforward of `standardGaussianLaw` by
`gaussianResponse`; it introduces no new noise or oracle model.
-/

open MeasureTheory ProbabilityTheory InformationTheory WithLp

noncomputable section

namespace HeavyTailedNoise

/-- The law of one response of the existing additive Gaussian oracle, when its
gradient mean is `μ`. -/
def gaussianResponseLaw (d : ℕ) (μ : Point d) (a : ℝ) : Measure (Point d) :=
  (standardGaussianLaw d).map (fun ξ => μ + a • ξ)

lemma gaussianResponseLaw_eq_oracle (d : ℕ) (grad : Point d → Point d)
    (hgrad : Continuous grad) (a : ℝ) (x : Point d) :
    gaussianResponseLaw d (grad x) a =
      ((gaussianOracle d grad hgrad a).law).map
        ((gaussianOracle d grad hgrad a).response x) := rfl

instance (d : ℕ) (μ : Point d) (a : ℝ) :
    IsProbabilityMeasure (gaussianResponseLaw d μ a) := by
  unfold gaussianResponseLaw
  infer_instance

lemma gaussianResponseLaw_integral (d : ℕ) (μ : Point d) (a : ℝ) :
    (∫ z : Point d, z ∂gaussianResponseLaw d μ a) = μ := by
  rw [gaussianResponseLaw, integral_map (by fun_prop) (by fun_prop)]
  simpa [gaussianResponse] using
    (integral_gaussianResponse (d := d) (fun _ => μ) a (0 : Point d))

/-- The actual measure-level KL vanishes when the two response means agree. -/
lemma gaussianResponseLaw_klDiv_self (d : ℕ) (μ : Point d) (a : ℝ) :
    klDiv (gaussianResponseLaw d μ a) (gaussianResponseLaw d μ a) = 0 := by
  simp

/-- KL is invariant under a common translation of finite-dimensional response
measures. This follows from data processing in both directions. -/
lemma klDiv_map_const_add (d : ℕ) (P Q : Measure (Point d))
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (c : Point d) :
    klDiv (P.map (fun z => c + z)) (Q.map (fun z => c + z)) = klDiv P Q := by
  apply le_antisymm
  · exact klDiv_map_le P Q (by fun_prop)
  · have hP : (P.map (fun z => c + z)).map (fun z => z - c) = P := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      simp [Function.comp_def]
    have hQ : (Q.map (fun z => c + z)).map (fun z => z - c) = Q := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      simp [Function.comp_def]
    have h := klDiv_map_le (P.map (fun z => c + z))
      (Q.map (fun z => c + z))
      (by fun_prop : Measurable (fun z : Point d => z - c))
    rwa [hP, hQ] at h

lemma gaussianResponseLaw_map_const_add (d : ℕ) (μ c : Point d) (a : ℝ) :
    (gaussianResponseLaw d μ a).map (fun z => c + z) =
      gaussianResponseLaw d (c + μ) a := by
  unfold gaussianResponseLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ξ
  simp [add_assoc]

/-- A common shift of the two actual Gaussian response laws preserves their
measure-level KL divergence. -/
lemma gaussianResponseLaw_klDiv_common_shift (d : ℕ) (μ ν c : Point d) (a : ℝ) :
    klDiv (gaussianResponseLaw d (c + μ) a)
      (gaussianResponseLaw d (c + ν) a) =
    klDiv (gaussianResponseLaw d μ a) (gaussianResponseLaw d ν a) := by
  rw [← gaussianResponseLaw_map_const_add,
    ← gaussianResponseLaw_map_const_add]
  exact klDiv_map_const_add d _ _ c

/-- The finite product of real Gaussian laws has the product of their real
densities with respect to the finite product of Lebesgue measures. -/
lemma pi_gaussianReal_eq_withDensity {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : NNReal) (hv : v ≠ 0) :
    Measure.pi (fun i : ι => gaussianReal (m i) v) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity
        (fun x : ι → ℝ =>
          ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (x i))) := by
  classical
  let V : Measure (ι → ℝ) := Measure.pi fun _ : ι => (volume : Measure ℝ)
  have hInt : Integrable
      (fun x : ι → ℝ => ∏ i, gaussianPDFReal (m i) v (x i)) V := by
    exact Integrable.fintype_prod (fun i => integrable_gaussianPDFReal (m i) v)
  have hNonneg (x : ι → ℝ) :
      0 ≤ ∏ i, gaussianPDFReal (m i) v (x i) := by
    exact Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg (m i) v (x i))
  change Measure.pi (fun i : ι => gaussianReal (m i) v) =
    V.withDensity (fun x : ι → ℝ =>
      ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (x i)))
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt.restrict
    (ae_of_all _ hNonneg)]
  have hRect :
      (∫ x in Set.univ.pi s,
        ∏ i, gaussianPDFReal (m i) v (x i) ∂V) =
      ∏ i, ∫ t in s i, gaussianPDFReal (m i) v t ∂volume := by
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod
      (fun i t => gaussianPDFReal (m i) v t)
  rw [hRect]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · simp_rw [← gaussianReal_apply_eq_integral (hv := hv)]
  · intro i hi
    exact integral_nonneg (gaussianPDFReal_nonneg (m i) v)

private lemma pi_gaussian_density_measurable {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : NNReal) :
    Measurable (fun x : ι → ℝ =>
      ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (x i))) := by
  fun_prop

private lemma pi_gaussian_density_pos {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : NNReal) (hv : v ≠ 0) (x : ι → ℝ) :
    0 < ∏ i, gaussianPDFReal (m i) v (x i) := by
  classical
  exact Finset.prod_pos (fun i _ => gaussianPDFReal_pos (m i) v (x i) hv)

lemma pi_gaussianReal_ac_pi_volume {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : NNReal) (hv : v ≠ 0) :
    Measure.pi (fun i : ι => gaussianReal (m i) v) ≪
      Measure.pi (fun _ : ι => (volume : Measure ℝ)) := by
  rw [pi_gaussianReal_eq_withDensity m v hv]
  exact withDensity_absolutelyContinuous _ _

lemma pi_volume_ac_pi_gaussianReal {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : NNReal) (hv : v ≠ 0) :
    Measure.pi (fun _ : ι => (volume : Measure ℝ)) ≪
      Measure.pi (fun i : ι => gaussianReal (m i) v) := by
  rw [pi_gaussianReal_eq_withDensity m v hv]
  exact withDensity_absolutelyContinuous'
    (pi_gaussian_density_measurable m v).aemeasurable
    (ae_of_all _ (fun x =>
      (ENNReal.ofReal_pos.mpr (pi_gaussian_density_pos m v hv x)).ne'))

/-- Positive-variance finite product Gaussians are mutually absolutely continuous. -/
lemma pi_gaussianReal_mutually_ac {ι : Type*} [Fintype ι]
    (m n : ι → ℝ) (v : NNReal) (hv : v ≠ 0) :
    Measure.pi (fun i : ι => gaussianReal (m i) v) ≪
      Measure.pi (fun i : ι => gaussianReal (n i) v) :=
  (pi_gaussianReal_ac_pi_volume m v hv).trans
    (pi_volume_ac_pi_gaussianReal n v hv)

private lemma pi_gaussianReal_rnDeriv_pi_volume {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : NNReal) (hv : v ≠ 0) :
    (Measure.pi (fun i : ι => gaussianReal (m i) v)).rnDeriv
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) =ᵐ[
      Measure.pi (fun _ : ι => (volume : Measure ℝ))]
      (fun x : ι → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (x i))) := by
  rw [pi_gaussianReal_eq_withDensity m v hv]
  exact Measure.rnDeriv_withDensity _ (pi_gaussian_density_measurable m v)

private lemma pi_gaussianReal_rnDeriv_ratio {ι : Type*} [Fintype ι]
    (m n : ι → ℝ) (v : NNReal) (hv : v ≠ 0) :
    (Measure.pi (fun i : ι => gaussianReal (m i) v)).rnDeriv
      (Measure.pi (fun i : ι => gaussianReal (n i) v)) =ᵐ[
      Measure.pi (fun i : ι => gaussianReal (n i) v)]
      (fun x : ι → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (x i)) /
          ENNReal.ofReal (∏ i, gaussianPDFReal (n i) v (x i))) := by
  let V : Measure (ι → ℝ) := Measure.pi fun _ : ι => (volume : Measure ℝ)
  let Pm : Measure (ι → ℝ) := Measure.pi fun i : ι => gaussianReal (m i) v
  let Pn : Measure (ι → ℝ) := Measure.pi fun i : ι => gaussianReal (n i) v
  change Pm.rnDeriv Pn =ᵐ[Pn] (fun x : ι → ℝ =>
    ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (x i)) /
      ENNReal.ofReal (∏ i, gaussianPDFReal (n i) v (x i)))
  have hmV := pi_gaussianReal_rnDeriv_pi_volume m v hv
  have hnV := pi_gaussianReal_rnDeriv_pi_volume n v hv
  have hPnV : Pn ≪ V := pi_gaussianReal_ac_pi_volume n v hv
  have hPmV : Pm ≪ V := pi_gaussianReal_ac_pi_volume m v hv
  have hmPn := hPnV hmV
  have hnPn := hPnV hnV
  have hRatio := Measure.rnDeriv_eq_div hPmV hPnV
  filter_upwards [hRatio, hmPn, hnPn] with x hr hm hn
  rw [hm, hn] at hr
  exact hr

/-- The log-likelihood ratio between two positive-variance product Gaussian
laws equals the logarithm of their strictly positive product-density ratio,
almost everywhere under the first law. -/
lemma pi_gaussianReal_llr_ae {ι : Type*} [Fintype ι]
    (m n : ι → ℝ) (v : NNReal) (hv : v ≠ 0) :
    llr (Measure.pi (fun i : ι => gaussianReal (m i) v))
      (Measure.pi (fun i : ι => gaussianReal (n i) v)) =ᵐ[
      Measure.pi (fun i : ι => gaussianReal (m i) v)]
      (fun x : ι → ℝ => Real.log
        ((∏ i, gaussianPDFReal (m i) v (x i)) /
          (∏ i, gaussianPDFReal (n i) v (x i)))) := by
  have hPmPn := pi_gaussianReal_mutually_ac m n v hv
  have hRatio := hPmPn (pi_gaussianReal_rnDeriv_ratio m n v hv)
  filter_upwards [hRatio] with x hx
  change Real.log
    ((Measure.pi (fun i : ι => gaussianReal (m i) v)).rnDeriv
      (Measure.pi (fun i : ι => gaussianReal (n i) v)) x).toReal = _
  rw [hx, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (pi_gaussian_density_pos m v hv x).le,
    ENNReal.toReal_ofReal (pi_gaussian_density_pos n v hv x).le]

private lemma log_gaussianPDFReal_sub (m n x : ℝ) (v : NNReal)
    (hv : v ≠ 0) :
    Real.log (gaussianPDFReal m v x) - Real.log (gaussianPDFReal n v x) =
      ((x - n) ^ 2 - (x - m) ^ 2) / (2 * (v : ℝ)) := by
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hc : (√(2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 := by positivity
  simp only [gaussianPDFReal, Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
  ring

private lemma log_pi_gaussian_density_div_affine {ι : Type*} [Fintype ι]
    (m n : ι → ℝ) (v : NNReal) (hv : v ≠ 0) (x : ι → ℝ) :
    Real.log
      ((∏ i, gaussianPDFReal (m i) v (x i)) /
        (∏ i, gaussianPDFReal (n i) v (x i))) =
      ∑ i : ι, (((m i - n i) / (v : ℝ)) * x i +
        ((n i) ^ 2 - (m i) ^ 2) / (2 * (v : ℝ))) := by
  classical
  have hm : (∏ i, gaussianPDFReal (m i) v (x i)) ≠ 0 :=
    (pi_gaussian_density_pos m v hv x).ne'
  have hn : (∏ i, gaussianPDFReal (n i) v (x i)) ≠ 0 :=
    (pi_gaussian_density_pos n v hv x).ne'
  rw [Real.log_div hm hn,
    Real.log_prod (fun i _ => (gaussianPDFReal_pos (m i) v (x i) hv).ne'),
    Real.log_prod (fun i _ => (gaussianPDFReal_pos (n i) v (x i) hv).ne'),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [log_gaussianPDFReal_sub (m i) (n i) (x i) v hv]
  have hvreal : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp [hvreal]
  ring

private lemma pi_gaussian_affine_integrable {ι : Type*} [Fintype ι]
    (m n : ι → ℝ) (v : NNReal) :
    Integrable
      (fun x : ι → ℝ => ∑ i : ι,
        (((m i - n i) / (v : ℝ)) * x i +
          ((n i) ^ 2 - (m i) ^ 2) / (2 * (v : ℝ))))
      (Measure.pi fun i : ι => gaussianReal (m i) v) := by
  classical
  have hcoord (i : ι) : Integrable
      (fun x : ι → ℝ => x i)
      (Measure.pi fun j : ι => gaussianReal (m j) v) := by
    have hi : Integrable (id : ℝ → ℝ) (gaussianReal (m i) v) :=
      ProbabilityTheory.IsGaussian.integrable_id
    exact integrable_eval hi
  have hterm (i : ι) : Integrable
      (fun x : ι → ℝ => ((m i - n i) / (v : ℝ)) * x i +
        ((n i) ^ 2 - (m i) ^ 2) / (2 * (v : ℝ)))
      (Measure.pi fun j : ι => gaussianReal (m j) v) :=
    ((hcoord i).const_mul _).add (integrable_const _)
  exact integrable_finsetSum _ (fun i _ => hterm i)

private lemma integral_pi_gaussian_affine {ι : Type*} [Fintype ι]
    (m n : ι → ℝ) (v : NNReal) (hv : v ≠ 0) :
    (∫ x : ι → ℝ, ∑ i : ι,
      (((m i - n i) / (v : ℝ)) * x i +
        ((n i) ^ 2 - (m i) ^ 2) / (2 * (v : ℝ)))
      ∂(Measure.pi fun j : ι => gaussianReal (m j) v)) =
      ∑ i : ι, (m i - n i) ^ 2 / (2 * (v : ℝ)) := by
  classical
  let Pm : Measure (ι → ℝ) := Measure.pi fun j : ι => gaussianReal (m j) v
  have hcoord (i : ι) : Integrable (fun x : ι → ℝ => x i) Pm := by
    have hi : Integrable (id : ℝ → ℝ) (gaussianReal (m i) v) :=
      ProbabilityTheory.IsGaussian.integrable_id
    exact integrable_eval hi
  have hterm (i : ι) : Integrable
      (fun x : ι → ℝ => ((m i - n i) / (v : ℝ)) * x i +
        ((n i) ^ 2 - (m i) ^ 2) / (2 * (v : ℝ))) Pm :=
    ((hcoord i).const_mul _).add (integrable_const _)
  change (∫ x : ι → ℝ, ∑ i : ι,
    (((m i - n i) / (v : ℝ)) * x i +
      ((n i) ^ 2 - (m i) ^ 2) / (2 * (v : ℝ))) ∂Pm) = _
  rw [integral_finsetSum _ (fun i _ => hterm i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_add ((hcoord i).const_mul _) (integrable_const _),
    integral_const_mul, integral_const]
  have hmean : (∫ x : ι → ℝ, x i ∂Pm) = m i := by
    rw [integral_eval, integral_id_gaussianReal]
  rw [hmean]
  have hmass : Pm.real Set.univ = 1 := by simp [Pm, measureReal_def]
  rw [hmass]
  simp only [one_smul]
  have hvreal : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp [hvreal]
  ring

/-- Exact measure-level KL for finite products of real Gaussians with the same
strictly positive coordinate variance. -/
theorem klDiv_pi_gaussianReal {ι : Type*} [Fintype ι]
    (m n : ι → ℝ) (v : NNReal) (hv : v ≠ 0) :
    klDiv (Measure.pi fun i : ι => gaussianReal (m i) v)
      (Measure.pi fun i : ι => gaussianReal (n i) v) =
      ENNReal.ofReal (∑ i : ι, (m i - n i) ^ 2 / (2 * (v : ℝ))) := by
  classical
  let Pm : Measure (ι → ℝ) := Measure.pi fun i : ι => gaussianReal (m i) v
  let Pn : Measure (ι → ℝ) := Measure.pi fun i : ι => gaussianReal (n i) v
  have hAffine : llr Pm Pn =ᵐ[Pm] (fun x : ι → ℝ => ∑ i : ι,
      (((m i - n i) / (v : ℝ)) * x i +
        ((n i) ^ 2 - (m i) ^ 2) / (2 * (v : ℝ)))) :=
    (pi_gaussianReal_llr_ae m n v hv).trans
      (ae_of_all _ (log_pi_gaussian_density_div_affine m n v hv))
  have hInt : Integrable (llr Pm Pn) Pm :=
    (integrable_congr hAffine).mpr (pi_gaussian_affine_integrable m n v)
  have hAC : Pm ≪ Pn := pi_gaussianReal_mutually_ac m n v hv
  change klDiv Pm Pn = _
  rw [klDiv_of_ac_of_integrable hAC hInt,
    integral_congr_ae hAffine, integral_pi_gaussian_affine m n v hv]
  simp [Pm, Pn, measureReal_def]

/-- The existing Euclidean response law is the coordinate-product Gaussian law
transported by `toLp 2`. -/
lemma gaussianResponseLaw_eq_map_pi_gaussianReal (d : ℕ)
    (μ : Point d) (a : ℝ) :
    gaussianResponseLaw d μ a =
      (Measure.pi fun i : Fin d =>
        gaussianReal (μ i) (NNReal.mk (a ^ 2) (sq_nonneg a))).map (toLp 2) := by
  let P0 : Measure (Fin d → ℝ) :=
    Measure.pi fun _ : Fin d => gaussianReal 0 1
  have hCoord :
      P0.map (fun x : Fin d → ℝ => fun i => μ i + a * x i) =
      Measure.pi (fun i : Fin d =>
        gaussianReal (μ i) (NNReal.mk (a ^ 2) (sq_nonneg a))) := by
    rw [Measure.pi_map_pi (fun i =>
      (show Measurable (fun z : ℝ => μ i + a * z) by fun_prop).aemeasurable)]
    congr 1
    funext i
    have hcomp : (fun z : ℝ => μ i + a * z) =
        (fun z : ℝ => μ i + z) ∘ (fun z : ℝ => a * z) := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      gaussianReal_map_const_mul, gaussianReal_map_const_add]
    simp
  calc
    gaussianResponseLaw d μ a =
        (P0.map (toLp 2)).map (fun ξ : Point d => μ + a • ξ) := by
          unfold gaussianResponseLaw standardGaussianLaw
          rw [← ProbabilityTheory.map_pi_eq_stdGaussian]
    _ = P0.map (fun x : Fin d → ℝ =>
          toLp 2 (fun i => μ i + a * x i)) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          congr 1
    _ = (P0.map (fun x : Fin d → ℝ => fun i => μ i + a * x i)).map
          (toLp 2) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = _ := by rw [hCoord]

private lemma klDiv_map_toLp (d : ℕ) (P Q : Measure (Fin d → ℝ))
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    klDiv (P.map (toLp 2)) (Q.map (toLp 2)) = klDiv P Q := by
  apply le_antisymm
  · exact klDiv_map_le P Q (by fun_prop)
  · let back : Point d → Fin d → ℝ := fun z i => z i
    have hP : (P.map (toLp 2)).map back = P := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have hcomp : back ∘ (toLp 2) = id := by
        funext x
        ext i
        rfl
      rw [hcomp, Measure.map_id]
    have hQ : (Q.map (toLp 2)).map back = Q := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have hcomp : back ∘ (toLp 2) = id := by
        funext x
        ext i
        rfl
      rw [hcomp, Measure.map_id]
    have h := klDiv_map_le (P.map (toLp 2)) (Q.map (toLp 2))
      (by fun_prop : Measurable back)
    rwa [hP, hQ] at h

/-- The one-response measure-level KL identity for the existing additive
Euclidean Gaussian oracle at the manuscript's scale `σ₀ / √d`. -/
theorem gaussianResponseLaw_klDiv (d : ℕ) (hd : 0 < d)
    (μ ν : Point d) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    klDiv (gaussianResponseLaw d μ (σ₀ / Real.sqrt d))
      (gaussianResponseLaw d ν (σ₀ / Real.sqrt d)) =
      ENNReal.ofReal ((d : ℝ) * ‖μ - ν‖ ^ 2 / (2 * σ₀ ^ 2)) := by
  let a : ℝ := σ₀ / Real.sqrt d
  let v : NNReal := NNReal.mk (a ^ 2) (sq_nonneg a)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < a := div_pos hσ₀ (Real.sqrt_pos.2 hdR)
  have hvR : (0 : ℝ) < (v : ℝ) := by
    change 0 < a ^ 2
    exact sq_pos_of_pos ha
  have hv : v ≠ 0 := ne_of_gt (NNReal.coe_pos.mp hvR)
  change klDiv (gaussianResponseLaw d μ a) (gaussianResponseLaw d ν a) = _
  rw [gaussianResponseLaw_eq_map_pi_gaussianReal,
    gaussianResponseLaw_eq_map_pi_gaussianReal,
    klDiv_map_toLp d,
    klDiv_pi_gaussianReal (fun i : Fin d => μ i) (fun i : Fin d => ν i) v hv]
  congr 1
  have hnorm : (∑ i : Fin d, (μ i - ν i) ^ 2) = ‖μ - ν‖ ^ 2 := by
    simpa using (EuclideanSpace.real_norm_sq_eq (μ - ν)).symm
  rw [← Finset.sum_div, hnorm]
  change ‖μ - ν‖ ^ 2 / (2 * a ^ 2) =
    (d : ℝ) * ‖μ - ν‖ ^ 2 / (2 * σ₀ ^ 2)
  have hdne : (d : ℝ) ≠ 0 := hdR.ne'
  have hσne : σ₀ ≠ 0 := hσ₀.ne'
  have ha2 : a ^ 2 = σ₀ ^ 2 / d := by
    dsimp [a]
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  rw [ha2]
  field_simp [hdne, hσne]

end HeavyTailedNoise
