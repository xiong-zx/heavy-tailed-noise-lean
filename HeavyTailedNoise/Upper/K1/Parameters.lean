import HeavyTailedNoise.Model.Basic

/-!
Public finite schedule for the `alg:k1` shared-batch exponential-memory method.
The final theorem must instantiate these fields with the exact formulas in the
current manuscript; this structure does not assert an oracle property.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

/-- Finite public sizes and scalar coefficients used by the literal method.
High-band index `j : Fin J` represents manuscript band `j+1`. -/
structure Schedule (q : ℝ) where
  J : ℕ
  T : ℕ
  n : ℕ
  nI : ℕ
  T_pos : 0 < T
  n_pos : 0 < n
  nI_pos : 0 < nI
  tau : Fin (J + 1) → ℝ
  tau_pos : ∀ j, 0 < tau j
  alpha : Fin J → ℝ
  beta : ℝ
  h : ℝ

/-- The initial high-band batch is used precisely in the manuscript's branch. -/
def useInitialBatch {q : ℝ} (P : Schedule q) : Prop := 1 < q ∧ 0 < P.J

/-- No initial-band responses are drawn at `q=1` or when there are no bands. -/
def initialResponses {q : ℝ} (P : Schedule q) : ℕ := by
  classical
  exact if useInitialBatch P then P.nI else 0

/-- Exact number of returned gradient vectors; the final output has no response. -/
def responseCount {q : ℝ} (P : Schedule q) : ℕ :=
  1 + initialResponses P + P.T * P.n

/-- The start of runtime batch `t` after the initial response and optional
independent initialization batch. -/
def batchStart {q : ℝ} (P : Schedule q) (t : ℕ) : ℕ :=
  1 + initialResponses P + t * P.n

theorem responseCount_eq_batchStart {q : ℝ} (P : Schedule q) :
    responseCount P = batchStart P P.T := rfl

theorem responseCount_pos {q : ℝ} (P : Schedule q) :
    0 < responseCount P := by
  simp [responseCount]

theorem initialResponses_of_q_le_one {q : ℝ} (P : Schedule q)
    (hq : q ≤ 1) : initialResponses P = 0 := by
  simp [initialResponses, useInitialBatch, not_lt.mpr hq]

theorem initialResponses_of_no_bands {q : ℝ} (P : Schedule q)
    (hJ : P.J = 0) : initialResponses P = 0 := by
  simp [initialResponses, useInitialBatch, hJ]

theorem initialResponses_of_high_bands {q : ℝ} (P : Schedule q)
    (hq : 1 < q) (hJ : 0 < P.J) : initialResponses P = P.nI := by
  simp [initialResponses, useInitialBatch, hq, hJ]

theorem responseCount_q_one (P : Schedule (1 : ℝ)) :
    responseCount P = 1 + P.T * P.n := by
  simp [responseCount, initialResponses_of_q_le_one P (le_refl 1)]

theorem responseCount_no_bands {q : ℝ} (P : Schedule q)
    (hJ : P.J = 0) : responseCount P = 1 + P.T * P.n := by
  simp [responseCount, initialResponses_of_no_bands P hJ]

end

end HeavyTailedNoise.UpperK1
