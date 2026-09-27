import HeavyTailedNoise.Lower.Fradin.PhysicalChain
import HeavyTailedNoise.Lower.Fradin.Progress
import HeavyTailedNoise.Lower.Fradin.Complexity

/-!
Actual all-slot risk and source-round lower bounds for the physical chain
and the one-dimensional rare-noise family. Oracle laws, response tails and
population barriers are discharged for the genuine admissible instances.
-/

namespace HeavyTailedNoise.Fradin

open HeavyTailedNoise MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false
universe v

theorem count_budget_of_round_budget {T n : ℕ} (θ : unitInterval)
    (hθ : 0 < (θ : ℝ))
    (hbudget : ((n + 1 : ℕ) : ℝ) ≤ (T : ℝ) / (4 * (θ : ℝ))) :
    4 * (n : ℝ) * (θ : ℝ) ≤ (T : ℝ) := by
  have hr := (le_div_iff₀ (by positivity : 0 < 4 * (θ : ℝ))).mp hbudget
  have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  calc
    4 * (n : ℝ) * (θ : ℝ) = (n : ℝ) * (4 * (θ : ℝ)) := by ring
    _ ≤ ((n + 1 : ℕ) : ℝ) * (4 * (θ : ℝ)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ ≤ (T : ℝ) := hr

/-- The global source algorithm predicate is instantiated on the actual
physical chain; no local-support, moment or probability premise is added. -/
theorem physicalChain_slotRisk_gt {K : ℕ} {Private : Type v}
    [MeasurableSpace Private] {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hT : 0 < chainLength L Δ ε
      (revealParameter 92 (σ / ε) (tailExponent p)
        (by norm_num) (tailExponent_pos hp.1)) q) :
    let θ := revealParameter 92 (σ / ε) (tailExponent p)
      (by norm_num) (tailExponent_pos hp.1)
    let T := chainLength L Δ ε θ q
    let I := physicalChainAdmissible hp hq hL hΔ hε hσ hT
    ∀ (A : Algorithm T K Private), ZeroRespecting.{0, v} A →
      ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≤ (T : ℝ) / (4 * (θ : ℝ)) →
        ∀ k : Fin K, ENNReal.ofReal ε < slotRisk I A n k := by
  let θ := revealParameter 92 (σ / ε) (tailExponent p)
    (by norm_num) (tailExponent_pos hp.1)
  let T := chainLength L Δ ε θ q
  let α := chainScaleAlpha L ε θ q
  let β := chainScaleBeta L ε θ q
  let I := physicalChainAdmissible hp hq hL hΔ hε hσ hT
  have hθ : 0 < (θ : ℝ) := revealRate_pos (by norm_num : (0 : ℝ) < 92)
  have hα : 0 < α := chainScaleAlpha_pos hL hε hθ
  have hβ : 0 < β := chainScaleBeta_pos hL hε hθ
  have hamplitude : α * β = 2 * ε := chainScaleAlpha_mul_beta hL hε hθ
  change ∀ (A : Algorithm T K Private), ZeroRespecting.{0, v} A →
    ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≤ (T : ℝ) / (4 * (θ : ℝ)) →
      ∀ k : Fin K, ENNReal.ofReal ε < slotRisk I A n k
  intro A hA n hn k
  apply slotRisk_gt_of_Bernoulli_tail_barrier I A θ
    (by rfl) (hA.on_admissible I) ?_ ?_ ?_ hε hT le_rfl n
    (count_budget_of_round_budget θ hθ hn) k
  · intro x m hx i hi
    exact scaledChainResponse_false_tail_zero α β θ x hx i hi
  · intro x m hx i hi
    exact scaledChainResponse_tail_zero α β θ x hx i hi true
  · intro x m hm hx
    have h := scaledChainGradient_barrier_of_tail_zero (mul_pos hα hβ) hm x hx
    rw [hamplitude] at h
    exact h

/-- The outer objective and oracle suprema precede the entire source algorithm infimum. -/
theorem physicalChain_sourceRoundComplexity_lower_bound {K : ℕ} (hK : 0 < K)
    {p q L Δ σ ε : ℝ} (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hT : 0 < chainLength L Δ ε
      (revealParameter 92 (σ / ε) (tailExponent p)
        (by norm_num) (tailExponent_pos hp.1)) q) :
    let θ := revealParameter 92 (σ / ε) (tailExponent p)
      (by norm_num) (tailExponent_pos hp.1)
    ENNReal.ofReal ((chainLength L Δ ε θ q : ℝ) / (4 * (θ : ℝ))) ≤
      sourceRoundComplexity.{0, v} K hK p q Δ σ L ε := by
  let I := physicalChainAdmissible hp hq hL hΔ hε hσ hT
  apply sourceRoundComplexity_ge_of_all_slot_risk_lower hK I
  intro Private m
  letI := m
  exact physicalChain_slotRisk_gt hp hq hL hΔ hε hσ hT

theorem noiseResponse_false_tailZero (L ε : ℝ) (ρ : unitInterval)
    (x : Point 1) (m : ℕ) (hx : tailZero x m) :
    tailZero (noiseResponse L ε ρ x false) m := by
  intro i hi
  rw [noiseResponse_false, PiLp.smul_apply, hx i hi, smul_zero]

theorem noiseResponse_true_tailZero (L ε : ℝ) (ρ : unitInterval)
    (x : Point 1) (m : ℕ) (_hx : tailZero x m) :
    tailZero (noiseResponse L ε ρ x true) (m + 1) := by
  intro i hi
  have hlt := i.isLt
  omega

theorem noiseGradient_tail_barrier {L ε : ℝ} (hε : 0 < ε)
    (x : Point 1) (m : ℕ) (hm : m < 1) (hx : tailZero x m) :
    2 * ε < ‖noiseGradient L ε x‖ := by
  have hm0 : m = 0 := by omega
  subst m
  have hx0 : x = 0 := by
    ext i
    exact hx i (Nat.zero_le _)
  rw [hx0, norm_noiseGradient_zero hε.le]
  linarith

theorem noiseFamily_slotRisk_gt {K : ℕ} {Private : Type v}
    [MeasurableSpace Private] {p q L Δ σ ε : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q) (hL : 0 < L) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hσ : 0 ≤ σ) (hgap : 8 * ε ^ 2 ≤ L * Δ) :
    let ρ := revealParameter 8 (σ / ε) (tailExponent p)
      (by norm_num) (tailExponent_pos hp.1)
    let I := noiseInstance_revealParameter (c := 8) (by norm_num)
      hp hq hL hΔ hε hσ hgap
    ∀ (A : Algorithm 1 K Private), ZeroRespecting.{0, v} A →
      ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≤ 1 / (4 * (ρ : ℝ)) →
        ∀ k : Fin K, ENNReal.ofReal ε < slotRisk I A n k := by
  let ρ := revealParameter 8 (σ / ε) (tailExponent p)
    (by norm_num) (tailExponent_pos hp.1)
  let I := noiseInstance_revealParameter (c := 8) (by norm_num)
    hp hq hL hΔ hε hσ hgap
  have hρ : 0 < (ρ : ℝ) := revealRate_pos (by norm_num : (0 : ℝ) < 8)
  change ∀ (A : Algorithm 1 K Private), ZeroRespecting.{0, v} A →
    ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≤ 1 / (4 * (ρ : ℝ)) →
      ∀ k : Fin K, ENNReal.ofReal ε < slotRisk I A n k
  intro A hA n hn k
  exact slotRisk_gt_of_Bernoulli_tail_barrier I A ρ
    (by rfl) (hA.on_admissible I)
    (noiseResponse_false_tailZero L ε ρ) (noiseResponse_true_tailZero L ε ρ)
    (noiseGradient_tail_barrier hε) hε (by norm_num) le_rfl n
    (count_budget_of_round_budget (T := 1) ρ hρ (by simpa only [Nat.cast_one] using hn)) k

theorem noiseFamily_sourceRoundComplexity_lower_bound {K : ℕ} (hK : 0 < K)
    {p q L Δ σ ε : ℝ} (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hgap : 8 * ε ^ 2 ≤ L * Δ) :
    let ρ := revealParameter 8 (σ / ε) (tailExponent p)
      (by norm_num) (tailExponent_pos hp.1)
    ENNReal.ofReal (1 / (4 * (ρ : ℝ))) ≤
      sourceRoundComplexity.{0, v} K hK p q Δ σ L ε := by
  let I := noiseInstance_revealParameter (c := 8) (by norm_num)
    hp hq hL hΔ hε hσ hgap
  apply sourceRoundComplexity_ge_of_all_slot_risk_lower hK I
  intro Private m
  letI := m
  exact noiseFamily_slotRisk_gt hp hq hL hΔ hε hσ hgap

end
end HeavyTailedNoise.Fradin
