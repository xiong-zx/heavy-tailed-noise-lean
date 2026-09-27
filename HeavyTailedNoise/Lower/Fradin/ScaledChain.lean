import HeavyTailedNoise.Lower.Fradin.BernoulliOracle

/-!
Actual rescaling of the Carmon objective and the smoothed Bernoulli oracle.
The final numerical choices are owned by Parameters. This module exposes
only scalar numerical bounds; it assumes no oracle law or analytic property.
-/

namespace HeavyTailedNoise.Fradin

open HeavyTailedNoise MeasureTheory
open scoped ENNReal
noncomputable section

def scaledChainValue {T : ℕ} (α β : ℝ) (x : Point T) : ℝ :=
  α * carmonChainValue (β • x)

def scaledChainGradient {T : ℕ} (α β : ℝ) (x : Point T) : Point T :=
  (α * β) • carmonChainGradient (β • x)

def scaledChainResponse {T : ℕ} (α β : ℝ) (θ : unitInterval)
    (x : Point T) (ξ : Bool) : Point T :=
  (α * β) • bernoulliResponse θ (β • x) ξ

theorem hasGradientAt_scaledChainValue {T : ℕ} (α β : ℝ) (x : Point T) :
    HasGradientAt (scaledChainValue α β) (scaledChainGradient α β x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hm : HasFDerivAt (fun y : Point T => β • y)
      (β • ContinuousLinearMap.id ℝ (Point T)) x :=
    (hasFDerivAt_id x).const_smul β
  have h := ((hasGradientAt_carmonChainValue (β • x)).hasFDerivAt.comp x hm).const_smul α
  convert h using 1
  · ext v
    rfl
  · ext v
    simp [scaledChainGradient, ContinuousLinearMap.comp_apply,
      InnerProductSpace.toDual_apply_apply, real_inner_smul_left, real_inner_smul_right,
      mul_assoc]

theorem continuous_scaledChainGradient {T : ℕ} (α β : ℝ) :
    Continuous (scaledChainGradient (T := T) α β) := by
  exact ((lipschitzWith_carmonChainGradient T).continuous.comp
    (by fun_prop : Continuous (fun x : Point T => β • x))).const_smul (α * β)

theorem scaledChainValue_gap_le {T : ℕ} {α β : ℝ} (hα : 0 ≤ α) (x : Point T) :
    scaledChainValue α β (0 : Point T) - scaledChainValue α β x ≤ α * (12 * T) := by
  have h := mul_le_mul_of_nonneg_left (carmonChainValue_gap_le_12T (β • x)) hα
  simpa only [scaledChainValue, smul_zero, mul_sub] using h

theorem measurable_scaledChainResponse {T : ℕ} (α β : ℝ) (θ : unitInterval) :
    Measurable (fun z : Point T × Bool => scaledChainResponse α β θ z.1 z.2) := by
  have hm : Measurable (fun z : Point T × Bool => (β • z.1, z.2)) :=
    ((continuous_fst.const_smul β).measurable :
      Measurable (fun z : Point T × Bool => β • z.1)).prodMk measurable_snd
  exact ((measurable_bernoulliResponse θ).comp hm).const_smul (α * β)

theorem integral_scaledChainResponse {T : ℕ} (α β : ℝ) (θ : unitInterval)
    (hθ : 0 < (θ : ℝ)) (x : Point T) :
    (∫ ξ, scaledChainResponse α β θ x ξ ∂bernoulliLaw θ) = scaledChainGradient α β x := by
  change (∫ ξ, (α * β) • bernoulliResponse θ (β • x) ξ ∂bernoulliLaw θ) =
    (α * β) • carmonChainGradient (β • x)
  rw [integral_smul, integral_bernoulliResponse θ hθ]

theorem integral_scaledChain_centered_rpow_le {T : ℕ} {α β : ℝ}
    (ha : 0 ≤ α * β) (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (x : Point T) {p : ℝ} (hp : 1 ≤ p) :
    (∫ ξ, ‖scaledChainResponse α β θ x ξ - scaledChainGradient α β x‖ ^ p
      ∂bernoulliLaw θ) ≤
      (α * β) ^ p * (2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) := by
  have hfun : (fun ξ => ‖scaledChainResponse α β θ x ξ - scaledChainGradient α β x‖ ^ p) =
      (fun ξ => (α * β) ^ p * ‖bernoulliResponse θ (β • x) ξ -
        carmonChainGradient (β • x)‖ ^ p) := by
    funext ξ
    rw [scaledChainResponse, scaledChainGradient, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha, Real.mul_rpow ha (norm_nonneg _)]
  rw [hfun, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_centered_rpow_le θ hθ (β • x) hp)
    (Real.rpow_nonneg ha _)

theorem integral_scaledChain_increment_rpow_le {T : ℕ} (hT : 0 < T) {α β : ℝ}
    (ha : 0 ≤ α * β) (hβ : 0 ≤ β) (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (x y : Point T) {q : ℝ} (hq : 1 ≤ q) :
    (∫ ξ, ‖scaledChainResponse α β θ x ξ - scaledChainResponse α β θ y ξ‖ ^ q
      ∂bernoulliLaw θ) ≤
      ((α * β) ^ q * (6087 : ℝ) ^ q * β ^ q / (θ : ℝ) ^ (q - 1)) * ‖x - y‖ ^ q := by
  have hfun : (fun ξ => ‖scaledChainResponse α β θ x ξ - scaledChainResponse α β θ y ξ‖ ^ q) =
      (fun ξ => (α * β) ^ q * ‖bernoulliResponse θ (β • x) ξ -
        bernoulliResponse θ (β • y) ξ‖ ^ q) := by
    funext ξ
    rw [scaledChainResponse, scaledChainResponse, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha, Real.mul_rpow ha (norm_nonneg _)]
  have hdist : ‖β • x - β • y‖ ^ q = β ^ q * ‖x - y‖ ^ q := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ,
      Real.mul_rpow hβ (norm_nonneg _)]
  rw [hfun, integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (integral_increment_rpow_le hT θ hθ (β • x) (β • y) hq)
      (Real.rpow_nonneg ha q)
  rw [hdist] at h
  convert h using 1 <;> ring

/-- An actual legal instance from positivity and three scalar numerical checks. -/
def scaledChainAdmissible (T : ℕ) (hT : 0 < T) (p q Δ σ L α β : ℝ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hL : 0 < L)
    (hα : 0 < α) (hβ : 0 < β) (θ : unitInterval) (hθ : 0 < (θ : ℝ))
    (hgap : α * (12 * T) ≤ Δ)
    (hmoment : (α * β) ^ p *
      (2 * (23 : ℝ) ^ p * (1 - (θ : ℝ)) / (θ : ℝ) ^ (p - 1)) ≤ σ ^ p)
    (hincrement : (α * β) ^ q * (6087 : ℝ) ^ q * β ^ q /
      (θ : ℝ) ^ (q - 1) ≤ L ^ q) : Admissible T Bool p q Δ σ L where
  objective := {
    dimension_pos := hT
    value := scaledChainValue α β
    grad := scaledChainGradient α β
    hasGradientAt := hasGradientAt_scaledChainValue α β
    continuous_grad := continuous_scaledChainGradient α β
    gap := fun x => (scaledChainValue_gap_le hα.le x).trans hgap }
  oracle := {
    law := bernoulliLaw θ
    law_probability := inferInstance
    response := scaledChainResponse α β θ
    measurable_response := measurable_scaledChainResponse α β θ }
  p_range := hp
  q_range := hq
  delta_pos := hΔ
  sigma_nonneg := hσ
  Lbar_pos := hL
  integrable_response := fun _ => integrable_bernoulliLaw θ _
  unbiased := integral_scaledChainResponse α β θ hθ
  centered_moment := by
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_bernoulliLaw θ _)
      (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) p))]
    exact ENNReal.ofReal_le_ofReal
      ((integral_scaledChain_centered_rpow_le (mul_pos hα hβ).le θ hθ x hp.1.le).trans hmoment)
  same_seed_increment := by
    intro x y
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_bernoulliLaw θ _)
      (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) q))]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ((α * β) ^ q * (6087 : ℝ) ^ q * β ^ q /
          (θ : ℝ) ^ (q - 1)) * ‖x - y‖ ^ q :=
        integral_scaledChain_increment_rpow_le hT (mul_pos hα hβ).le hβ.le θ hθ x y hq
      _ ≤ L ^ q * ‖x - y‖ ^ q := mul_le_mul_of_nonneg_right hincrement
        (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (L * ‖x - y‖) ^ q := (Real.mul_rpow hL.le (norm_nonneg (x-y))).symm

theorem scaledChainResponse_false_tail_zero {T n : ℕ} (α β : ℝ) (θ : unitInterval)
    (x : Point T) (hx : ∀ i : Fin T, n ≤ i.val → x i = 0)
    (i : Fin T) (hi : n ≤ i.val) : scaledChainResponse α β θ x false i = 0 := by
  have hraw : ∀ j : Fin T, n ≤ j.val → |(β • x) j| ≤ 1 / 4 := by
    intro j hj
    simp [PiLp.smul_apply, hx j hj]
  rw [scaledChainResponse, PiLp.smul_apply,
    bernoulliResponse_false_frontier_zero θ (β • x) hraw i hi, smul_zero]

theorem scaledChainResponse_tail_zero {T n : ℕ} (α β : ℝ) (θ : unitInterval)
    (x : Point T) (hx : ∀ i : Fin T, n ≤ i.val → x i = 0)
    (i : Fin T) (hi : n + 1 ≤ i.val) (ξ : Bool) : scaledChainResponse α β θ x ξ i = 0 := by
  have hraw : ∀ j : Fin T, n ≤ j.val → |(β • x) j| ≤ 1 / 2 := by
    intro j hj
    simp [PiLp.smul_apply, hx j hj]
  rw [scaledChainResponse, PiLp.smul_apply,
    bernoulliResponse_tail_zero θ (β • x) hraw i hi ξ, smul_zero]

theorem scaledChainGradient_barrier {T : ℕ} {α β : ℝ} (ha : 0 < α * β)
    (x : Point T) (hx : ∃ i : Fin T, |(β • x) i| < 1) :
    α * β < ‖scaledChainGradient α β x‖ := by
  have h := mul_lt_mul_of_pos_left
    (one_lt_norm_carmonChainGradient_of_small_coordinate (β • x) hx) ha
  simpa only [scaledChainGradient, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
    mul_one] using h

theorem scaledChainGradient_barrier_of_tail_zero {T n : ℕ} {α β : ℝ}
    (ha : 0 < α * β) (hn : n < T) (x : Point T)
    (hx : ∀ i : Fin T, n ≤ i.val → x i = 0) : α * β < ‖scaledChainGradient α β x‖ := by
  apply scaledChainGradient_barrier ha x
  refine ⟨⟨n, hn⟩, ?_⟩
  simp [PiLp.smul_apply, hx ⟨n, hn⟩ le_rfl]

end
end HeavyTailedNoise.Fradin
