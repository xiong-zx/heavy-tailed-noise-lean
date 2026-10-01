import HeavyTailedNoise.Upper.K1.PhysicalParameters

/-!
Ceiling bookkeeping for the literal response cap of the frozen manuscript
algorithm. These bounds do not replace the parameter choices or alter the
strict one-response protocol. The subsequent exponent conversion is separate.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

private theorem ceil_real_le_add_one (x : ℝ) (hx : 0 ≤ x) :
    (Nat.ceil x : ℝ) ≤ x + 1 :=
  (Nat.ceil_lt_add_one hx).le

/-- The iteration count, including its integer rounding. -/
theorem paperT_real_le (Lbar Δ ε ch : ℝ) (hch : 0 < ch) :
    (paperT Lbar Δ ε ch : ℝ) ≤
      4 * paperAplus Lbar Δ ε / ch + 1 := by
  unfold paperT
  apply ceil_real_le_add_one
  have hA : 0 ≤ paperAplus Lbar Δ ε :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 _)
  exact div_nonneg (by positivity) hch.le

/-- The runtime batch size, including its integer rounding. -/
theorem paperBatchSize_real_le (p q σ ε Ctail Cb : ℝ) (hε : 0 < ε)
    (hCb : 0 ≤ Cb) :
    (paperBatchSize p q σ ε Ctail Cb : ℝ) ≤
      Cb * (paperS σ ε) ^ 2 *
        (paperU p σ ε Ctail) ^ (paperEplus p q) + 1 := by
  unfold paperBatchSize
  apply ceil_real_le_add_one
  have hU := paperU_pos (p := p) (σ := σ) (Ctail := Ctail) hε
  have hS := paperS_pos σ ε
  positivity

/-- The optional initialization batch size, including its integer rounding. -/
theorem paperInitialBatchSize_real_le (p σ ε Ctail CI : ℝ) (hε : 0 < ε)
    (hCI : 0 ≤ CI) :
    (paperInitialBatchSize p σ ε Ctail CI : ℝ) ≤
      CI * (paperS σ ε) ^ 2 *
        (paperU p σ ε Ctail) ^ (paperA p) + 1 := by
  unfold paperInitialBatchSize
  apply ceil_real_le_add_one
  have hU := paperU_pos (p := p) (σ := σ) (Ctail := Ctail) hε
  have hS := paperS_pos σ ε
  positivity

/-- The exact response count is at most the real envelope of its three
rounded terms. It covers `q=1` and `J=0` without assuming initialization. -/
theorem paperSchedule_responseCount_real_le
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI) :
    (responseCount (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI) : ℝ) ≤
      1 + (CI * (paperS σ ε) ^ 2 *
        (paperU p σ ε Ctail) ^ (paperA p) + 1) +
      (4 * paperAplus Lbar Δ ε / ch + 1) *
        (Cb * (paperS σ ε) ^ 2 *
          (paperU p σ ε Ctail) ^ (paperEplus p q) + 1) := by
  let T := paperT Lbar Δ ε ch
  let n := paperBatchSize p q σ ε Ctail Cb
  let nI := paperInitialBatchSize p σ ε Ctail CI
  have hT := paperT_real_le Lbar Δ ε ch hch
  have hn := paperBatchSize_real_le p q σ ε Ctail Cb hε hCb.le
  have hnI := paperInitialBatchSize_real_le p σ ε Ctail CI hε hCI.le
  have hTnonneg : 0 ≤ 4 * paperAplus Lbar Δ ε / ch + 1 := by
    have hA : 0 ≤ paperAplus Lbar Δ ε :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 _)
    positivity
  have hprod : (T : ℝ) * (n : ℝ) ≤
      (4 * paperAplus Lbar Δ ε / ch + 1) *
        (Cb * (paperS σ ε) ^ 2 *
          (paperU p σ ε Ctail) ^ (paperEplus p q) + 1) := by
    exact mul_le_mul hT hn (Nat.cast_nonneg _) hTnonneg
  have hinitnonneg : 0 ≤ CI * (paperS σ ε) ^ 2 *
      (paperU p σ ε Ctail) ^ (paperA p) + 1 := by
    have hU := paperU_pos (p := p) (σ := σ) (Ctail := Ctail) hε
    positivity
  rw [paperSchedule_responseCount]
  split_ifs <;> push_cast <;> dsimp [T, n, nI] at * <;> nlinarith

end

end HeavyTailedNoise.UpperK1
