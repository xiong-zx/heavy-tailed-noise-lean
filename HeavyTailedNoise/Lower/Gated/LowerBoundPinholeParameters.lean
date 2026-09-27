import HeavyTailedNoise.Lower.Gated.LowerBoundStageLength
import HeavyTailedNoise.Lower.Gated.NextDirectionStagePinhole

/-!
The manuscript's fixed stage floor and dimension condition discharge the
numeric premises of the fixed-prefix pinhole theorem.  The cap list keeps the
existing `m+1` pre-response queries and its conservative `n₀+2` union bound.
No identification of the actual stopped conditional law is assumed here.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

/-- The large-noise condition and `d≥2T` make the actual stage floor at least
two, before any loss used for the final response-rate constant. -/
theorem gatedStageLength_ge_two {d T : ℕ} {S : ℝ}
    (hd : 0 < d) (hdim : 2 * T ≤ d)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2))) :
    2 ≤ gatedStageLength d T S := by
  have hTd : T ≤ d := by omega
  have hdimR : (2 : ℝ) * T ≤ d := by exact_mod_cast hdim
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hD : (d : ℝ) / 2 ≤ (d - T : ℕ) := by
    rw [Nat.cast_sub hTd]
    linarith
  let V : ℝ := (1 / 4005.25) * (S / 80) ^ 2 / 300 ^ 2
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlargeV : 2 ≤ V / 16 := by
    dsimp [V]
    convert hlarge using 1
    ring
  apply Nat.le_floor
  change (2 : ℝ) ≤ (d - T : ℕ) * V / (8 * d)
  apply hlargeV.trans
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * d)).2
  have hmul := mul_le_mul_of_nonneg_right hD hV
  nlinarith

/-- Flooring the fixed stage cap gives the exact KL allowance, also for any
shorter frozen response transcript. -/
theorem gatedStageLength_klBudget {d T m : ℕ} {S : ℝ}
    (hd : 0 < d) (hS : 0 < S) (hm : m ≤ gatedStageLength d T S) :
    (m : ENNReal) * ENNReal.ofReal
        ((d : ℝ) * (300 : ℝ) ^ 2 / (2 * (S / 80) ^ 2)) ≤
      ENNReal.ofReal (((d - T : ℕ) : ℝ) * haarCapAngleSq / 16) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have harg : 0 ≤ (((d - T : ℕ) : ℝ) *
      ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / 300 ^ 2) / (8 * d)) := by
    positivity
  have hfloor := Nat.floor_le harg
  have hmR : (m : ℝ) ≤ gatedStageLength d T S := by exact_mod_cast hm
  change (gatedStageLength d T S : ℝ) ≤ _ at hfloor
  have hbound := hmR.trans hfloor
  have hfactor : 0 ≤ (d : ℝ) * 300 ^ 2 / (2 * (S / 80) ^ 2) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hbound hfactor
  have heq :
      (((d - T : ℕ) : ℝ) *
        ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 / 300 ^ 2) / (8 * d)) *
        ((d : ℝ) * 300 ^ 2 / (2 * (S / 80) ^ 2)) =
      ((d - T : ℕ) : ℝ) * haarCapAngleSq / 16 := by
    rw [haarCapAngleSq_eq]
    field_simp [hdR.ne', hS.ne']
    ring
  have hreal : (m : ℝ) *
      ((d : ℝ) * 300 ^ 2 / (2 * (S / 80) ^ 2)) ≤
      ((d - T : ℕ) : ℝ) * haarCapAngleSq / 16 := by
    simpa only [heq] using hmul
  have hof := ENNReal.ofReal_le_ofReal hreal
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast] using hof

/-- The public cap allowance uses the least residual dimension `d-T` and
includes the two conservative extra slots in the checked query-list bound. -/
def gatedPinholeCap (d T n₀ : ℕ) : ℝ :=
  2 * (n₀ + 2 : ℕ) *
    Real.exp (-((d - T : ℕ) : ℝ) * haarCapAngleSq / 2)

/-- The frozen `21400` dimension condition has enough slack for `n₀+2`,
without changing the manuscript's condition involving `log(2n₀)`. -/
theorem gatedPinhole_logBudget {d T n₀ : ℕ}
    (hn₀ : 2 ≤ n₀)
    (hdim : 21400 * (1 + Real.log (2 * (n₀ : ℝ))) ≤ (d - T : ℕ)) :
    ((d - T : ℕ) : ℝ) * haarCapAngleSq / 16 + Real.log 2 ≤
      (1 / 2 : ℝ) * Real.log (gatedPinholeCap d T n₀)⁻¹ := by
  have hτ := haarCapAngleSq_pos
  have hnR : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hnpos : (0 : ℝ) < n₀ := by linarith
  have hn2pos : (0 : ℝ) < (n₀ + 2 : ℕ) := by positivity
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogn : 2 * Real.log (2 : ℝ) ≤ Real.log (2 * (n₀ : ℝ)) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ 2 * n₀)
    have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    simpa only [hfour] using h
  have hlogn0 : 0 ≤ Real.log (2 * (n₀ : ℝ)) :=
    (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))).trans hlogn
  have hlist : Real.log (2 * (n₀ + 2 : ℕ)) ≤
      Real.log (2 * (n₀ : ℝ)) + Real.log 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (n₀ + 2 : ℕ))
      (by push_cast; nlinarith : (2 : ℝ) * (n₀ + 2 : ℕ) ≤ (2 * n₀) * 2)
    simpa only [Real.log_mul (by positivity : (2 * (n₀ : ℝ)) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hslack : Real.log 2 + (1 / 2 : ℝ) * Real.log (2 * (n₀ + 2 : ℕ)) ≤
      1 + Real.log (2 * (n₀ : ℝ)) := by linarith
  have hconst : 1 ≤ (3 / 16 : ℝ) * 21400 * haarCapAngleSq := by
    norm_num [haarCapAngleSq]
  have hpos : 0 ≤ 1 + Real.log (2 * (n₀ : ℝ)) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdim
    (by positivity : (0 : ℝ) ≤ (3 / 16 : ℝ) * haarCapAngleSq)
  have hmul2 := mul_le_mul_of_nonneg_right hconst hpos
  have hD : 1 + Real.log (2 * (n₀ : ℝ)) ≤
      (3 / 16 : ℝ) * (d - T : ℕ) * haarCapAngleSq := by nlinarith
  have hcaplog : Real.log (gatedPinholeCap d T n₀)⁻¹ =
      ((d - T : ℕ) : ℝ) * haarCapAngleSq / 2 -
        Real.log (2 * (n₀ + 2 : ℕ)) := by
    unfold gatedPinholeCap
    rw [Real.log_inv, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
    ring
  rw [hcaplog]
  nlinarith

/-- The conservative cap allowance is positive. -/
theorem gatedPinholeCap_pos (d T n₀ : ℕ) :
    0 < gatedPinholeCap d T n₀ := by
  unfold gatedPinholeCap
  positivity

/-- The same public dimension condition makes the reference allowance a
genuine probability cap below one. -/
theorem gatedPinholeCap_lt_one {d T n₀ : ℕ}
    (hn₀ : 2 ≤ n₀)
    (hdim : 21400 * (1 + Real.log (2 * (n₀ : ℝ))) ≤ (d - T : ℕ)) :
    gatedPinholeCap d T n₀ < 1 := by
  have hτ := haarCapAngleSq_pos
  have h := gatedPinhole_logBudget hn₀ hdim
  have hI : 0 ≤ ((d - T : ℕ) : ℝ) * haarCapAngleSq / 16 := by
    positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [Real.log_inv] at h
  apply (Real.log_neg_iff (gatedPinholeCap_pos d T n₀)).mp
  linarith

/-- The manuscript's actual fixed floor and dimension choices close every
numeric and query-list premise of the checked one-stage pinhole theorem.
Its conclusion concerns the constructed fixed-prefix joint kernel. -/
theorem nextDirection_frozenCap_probability_half_actual_parameters
    {d T N m : ℕ} {S : ℝ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (hdim : 2 * T ≤ d) (hS : 0 < S)
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * (S / 80) ^ 2 /
      (16 * 300 ^ 2)))
    (hdimlog : 21400 *
      (1 + Real.log (2 * (gatedStageLength d T S : ℝ))) ≤ (d - T : ℕ))
    (hm : m ≤ gatedStageLength d T S)
    (j : Fin T) (v : Fin j.val → Point d) (hv : Orthonormal ℝ v)
    (θ₀ : Point d) (hθ₀ : Orthonormal ℝ (Fin.snoc v θ₀))
    (A : RandomAlgorithm d N Private) (r : Private)
    (s : IdealPreResponseHistory d N) :
    let K := repairedNextDirectionFrozenKernel
      (m := m) hT j v A r s ((S / 80) / Real.sqrt d) θ₀
    let E := nextDirectionFinalCapEvent (m := m) hT v A r s
    (((frameNextKernel d j.val v) ⊗ₘ K) E).toReal ≤ 1 / 2 := by
  have hτ := haarCapAngleSq_pos
  have hd : 0 < d := by omega
  have hTd : T ≤ d := by omega
  have hjd : j.val < d := j.isLt.trans_le hTd
  have hn₀ : 2 ≤ gatedStageLength d T S :=
    gatedStageLength_ge_two hd hdim hlarge
  have hnR : (2 : ℝ) ≤ gatedStageLength d T S := by exact_mod_cast hn₀
  have hlogn : 0 ≤ Real.log (2 * (gatedStageLength d T S : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hD : 21400 ≤ d - T := by
    have hDreal : (21400 : ℝ) ≤ (d - T : ℕ) := by linarith
    exact_mod_cast hDreal
  have hDim : 16022 ≤ d - j.val := by omega
  have hlen : m + 1 ≤ gatedStageLength d T S + 2 := by omega
  have hcap : 2 * (gatedStageLength d T S + 2 : ℕ) *
      Real.exp (-((d - j.val : ℕ) : ℝ) * haarCapAngleSq / 2) ≤
      gatedPinholeCap d T (gatedStageLength d T S) := by
    have hDle : ((d - T : ℕ) : ℝ) ≤ (d - j.val : ℕ) := by
      exact_mod_cast (show d - T ≤ d - j.val by omega)
    unfold gatedPinholeCap
    apply mul_le_mul_of_nonneg_left
    · apply Real.exp_le_exp.mpr
      have hτ := haarCapAngleSq_pos
      nlinarith
    · positivity
  exact nextDirection_frozenCap_probability_half
    (budget := gatedStageLength d T S) hd hT hTd j v hv hjd hDim θ₀ hθ₀
    (S / 80) (by positivity) A r s hlen
    (((d - T : ℕ) : ℝ) * haarCapAngleSq / 16)
    (gatedPinholeCap d T (gatedStageLength d T S))
    (by positivity) (gatedStageLength_klBudget hd hS hm)
    (gatedPinholeCap_pos _ _ _) (gatedPinholeCap_lt_one hn₀ hdimlog)
    hcap (gatedPinhole_logBudget hn₀ hdimlog)

end

end HeavyTailedNoise
