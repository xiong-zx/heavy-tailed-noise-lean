import HeavyTailedNoise.Upper.K1.Parameters

/-!
Scalar formulas from the frozen `alg:k1` manuscript. This module fixes the
actual dyadic cutoff and counts; the eventual upper theorem must construct a
`Schedule` from these formulas and prove the required quantitative estimates.
No oracle or algorithm restriction is introduced here.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

def paperNu (σ ε : ℝ) : ℝ := max σ ε
def paperS (σ ε : ℝ) : ℝ := max 1 (σ / ε)
def paperAplus (Lbar Δ ε : ℝ) : ℝ := max 1 (Lbar * Δ / ε ^ 2)
def paperA (p : ℝ) : ℝ := 2 - p
def paperSexp (p q : ℝ) : ℝ := p * (1 - 1 / q)
def paperEplus (p q : ℝ) : ℝ := max (paperA p - paperSexp p q) 0

theorem paperNu_pos {σ ε : ℝ} (hε : 0 < ε) : 0 < paperNu σ ε :=
  lt_of_lt_of_le hε (le_max_right σ ε)

theorem one_le_paperS (σ ε : ℝ) : 1 ≤ paperS σ ε :=
  le_max_left 1 (σ / ε)

theorem paperS_pos (σ ε : ℝ) : 0 < paperS σ ε :=
  lt_of_lt_of_le zero_lt_one (one_le_paperS σ ε)

theorem paperEplus_nonneg (p q : ℝ) : 0 ≤ paperEplus p q :=
  le_max_right _ _

/-- The target level in the manuscript's least-dyadic-index definition. -/
def paperTailTarget (p σ ε Ctail : ℝ) : ℝ :=
  Ctail * (paperS σ ε) ^ (1 / (p - 1))

private theorem paper_cutoff_exists (p σ ε Ctail : ℝ) :
    ∃ j : ℕ, paperTailTarget p σ ε Ctail ≤ 12 * (2 : ℝ) ^ j := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
    (paperTailTarget p σ ε Ctail / 12) (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, ?_⟩
  have h := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 12)).mp hj
  dsimp [paperTailTarget] at h ⊢
  nlinarith

/-- The least `J ≥ 0` with `12*2^J ≥ Ctail*S^(1/(p−1))`. -/
def paperJ (p σ ε Ctail : ℝ) : ℕ :=
  Nat.find (paper_cutoff_exists p σ ε Ctail)

theorem paperJ_reaches_target (p σ ε Ctail : ℝ) :
    paperTailTarget p σ ε Ctail ≤ 12 * (2 : ℝ) ^ paperJ p σ ε Ctail :=
  Nat.find_spec (paper_cutoff_exists p σ ε Ctail)

theorem paperJ_is_least (p σ ε Ctail : ℝ) {j : ℕ}
    (hj : j < paperJ p σ ε Ctail) :
    ¬ paperTailTarget p σ ε Ctail ≤ 12 * (2 : ℝ) ^ j :=
  Nat.find_min (paper_cutoff_exists p σ ε Ctail) hj

def paperTau (σ ε : ℝ) (j : ℕ) : ℝ :=
  12 * paperNu σ ε * (2 : ℝ) ^ j

theorem paperTau_pos {σ ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    0 < paperTau σ ε j := by
  have hν := paperNu_pos (σ := σ) hε
  unfold paperTau
  positivity

def paperU (p σ ε Ctail : ℝ) : ℝ :=
  paperTau σ ε (paperJ p σ ε Ctail) / paperNu σ ε

theorem paperU_pos {p σ ε Ctail : ℝ} (hε : 0 < ε) :
    0 < paperU p σ ε Ctail :=
  div_pos (paperTau_pos hε _) (paperNu_pos hε)

def paperT (Lbar Δ ε ch : ℝ) : ℕ :=
  Nat.ceil (4 * paperAplus Lbar Δ ε / ch)

def paperBatchSize (p q σ ε Ctail Cb : ℝ) : ℕ :=
  Nat.ceil (Cb * (paperS σ ε) ^ 2 * (paperU p σ ε Ctail) ^ (paperEplus p q))

def paperInitialBatchSize (p σ ε Ctail CI : ℝ) : ℕ :=
  Nat.ceil (CI * (paperS σ ε) ^ 2 * (paperU p σ ε Ctail) ^ (paperA p))

def paperBeta (σ ε : ℝ) : ℝ :=
  (4 * (Nat.ceil (paperS σ ε) : ℝ))⁻¹

def paperStep (ch ε Lbar : ℝ) : ℝ := ch * ε / Lbar

/-- `j : Fin J` represents manuscript band `j+1`, with `t_{j+1}=12*2^j`. -/
def paperAlpha (p q κ : ℝ) (j : ℕ) : ℝ :=
  min 1 ((κ * (12 * (2 : ℝ) ^ j) ^ paperSexp p q)⁻¹)

/-- The `q=1` branch retains every high band, with no memory lag. -/
theorem paperAlpha_q_one (p κ : ℝ) (hκ : 0 < κ) (hκle : κ ≤ 1)
    (j : ℕ) : paperAlpha p 1 κ j = 1 := by
  have hinv : 1 ≤ κ⁻¹ := (one_le_inv₀ hκ).2 hκle
  simp [paperAlpha, paperSexp, min_eq_left hinv]

/-- Exact scalar schedule from the manuscript. Quantitative constraints on the
large/small numerical constants are proved separately before the final upper
theorem; positivity suffices to make this finite algorithm well-defined. -/
def paperSchedule (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI) : Schedule q where
  J := paperJ p σ ε Ctail
  T := paperT Lbar Δ ε ch
  n := paperBatchSize p q σ ε Ctail Cb
  nI := paperInitialBatchSize p σ ε Ctail CI
  T_pos := by
    have hA : 0 < paperAplus Lbar Δ ε :=
      lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
    unfold paperT
    apply Nat.ceil_pos.mpr
    exact div_pos (by positivity) hch
  n_pos := by
    have hS := paperS_pos σ ε
    have hU := paperU_pos (p := p) (σ := σ) (Ctail := Ctail) hε
    unfold paperBatchSize
    apply Nat.ceil_pos.mpr
    positivity
  nI_pos := by
    have hS := paperS_pos σ ε
    have hU := paperU_pos (p := p) (σ := σ) (Ctail := Ctail) hε
    unfold paperInitialBatchSize
    apply Nat.ceil_pos.mpr
    positivity
  tau := fun j => paperTau σ ε j.val
  tau_pos := fun j => paperTau_pos hε j.val
  alpha := fun j => paperAlpha p q κ j.val
  beta := paperBeta σ ε
  h := paperStep ch ε Lbar

/-- Literal fixed response cap after substituting the manuscript formulas. -/
theorem paperSchedule_responseCount
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI) :
    responseCount (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI) =
      1 + (if 1 < q ∧ 0 < paperJ p σ ε Ctail then
        paperInitialBatchSize p σ ε Ctail CI else 0) +
        paperT Lbar Δ ε ch * paperBatchSize p q σ ε Ctail Cb := by
  classical
  by_cases hinit : 1 < q ∧ 0 < paperJ p σ ε Ctail
  · simp [responseCount, initialResponses, useInitialBatch, paperSchedule, hinit]
  · simp [responseCount, initialResponses, useInitialBatch, paperSchedule, hinit]

end

end HeavyTailedNoise.UpperK1
