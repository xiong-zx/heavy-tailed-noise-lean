import HeavyTailedNoise.Lower.Gated.GatedHaarFiniteLowerBound

/-!
The manuscript's dimension-uniform minimax response complexity.

The infimum ranges over natural, deterministic padded response budgets in the
existing shared guarantee. It is taken in `ℕ∞`, so an empty feasible-budget
set has value `∞`. When feasible budgets exist, it is their least natural
budget. Its coercion to `ENNReal` is the same infimum in the extended
nonnegative reals, matching the manuscript's `inf ∅ = +∞` convention.

No expected stopping-time budget or narrower algorithm class is introduced.
-/

namespace HeavyTailedNoise

noncomputable section

set_option autoImplicit false

universe u v

/-- The single minimax complexity definition: the least feasible deterministic
natural response budget, or `∞` if no dimension-uniform budget is feasible. -/
def dimensionUniformMinimaxComplexity (p q Δ σ Lbar ε : ℝ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : HasDimensionUniformGuarantee.{u, v} N p q Δ σ Lbar ε), (N : ℕ∞)

/-- The empty-set convention is explicit, including oracle/private universes. -/
theorem dimensionUniformMinimaxComplexity_eq_top_iff
    (p q Δ σ Lbar ε : ℝ) :
    dimensionUniformMinimaxComplexity.{u, v} p q Δ σ Lbar ε = ⊤ ↔
      ∀ N : ℕ, ¬ HasDimensionUniformGuarantee.{u, v} N p q Δ σ Lbar ε := by
  simp [dimensionUniformMinimaxComplexity]

/-- If feasible budgets exist, the extended infimum is their ordinary natural
infimum. In particular no limiting sequence of fractional budgets is added. -/
theorem dimensionUniformMinimaxComplexity_eq_nat_sInf
    {p q Δ σ Lbar ε : ℝ}
    (hfeasible : ∃ N : ℕ, HasDimensionUniformGuarantee.{u, v} N p q Δ σ Lbar ε) :
    dimensionUniformMinimaxComplexity.{u, v} p q Δ σ Lbar ε =
      ((sInf {N : ℕ | HasDimensionUniformGuarantee.{u, v} N p q Δ σ Lbar ε} : ℕ) : ℕ∞) := by
  exact (ENat.natCast_sInf hfeasible).symm

/-- This is exactly the manuscript infimum viewed in extended nonnegative
reals, with the same natural feasible budgets and empty-set convention. -/
theorem dimensionUniformMinimaxComplexity_toENNReal
    (p q Δ σ Lbar ε : ℝ) :
    (dimensionUniformMinimaxComplexity.{u, v} p q Δ σ Lbar ε : ENNReal) =
      ⨅ (N : ℕ) (_ : HasDimensionUniformGuarantee.{u, v} N p q Δ σ Lbar ε),
        (N : ENNReal) := by
  simp [dimensionUniformMinimaxComplexity, ENat.toENNReal_iInf]

/-- Excluding every natural budget up to `N` forces the complexity to be at
least `N+1`. This direct prefix argument does not require a separate padding
or monotonicity theorem for algorithms. -/
theorem dimensionUniformMinimaxComplexity_succ_le_of_excluded_prefix
    {p q Δ σ Lbar ε : ℝ} (N : ℕ)
    (hfail : ∀ M : ℕ, M ≤ N →
      ¬ HasDimensionUniformGuarantee.{u, v} M p q Δ σ Lbar ε) :
    ((N + 1 : ℕ) : ℕ∞) ≤ dimensionUniformMinimaxComplexity.{u, v} p q Δ σ Lbar ε := by
  unfold dimensionUniformMinimaxComplexity
  refine le_iInf fun M => le_iInf fun hM => ?_
  have hNM : N < M := lt_of_not_ge (fun hMN => hfail M hMN hM)
  exact_mod_cast Nat.succ_le_of_lt hNM

/-- Natural-budget exclusion gives the strict fixed-budget conclusion. -/
theorem dimensionUniformMinimaxComplexity_gt_of_excluded_prefix
    {p q Δ σ Lbar ε : ℝ} (N : ℕ)
    (hfail : ∀ M : ℕ, M ≤ N →
      ¬ HasDimensionUniformGuarantee.{u, v} M p q Δ σ Lbar ε) :
    (N : ℕ∞) < dimensionUniformMinimaxComplexity.{u, v} p q Δ σ Lbar ε := by
  have hsucc := dimensionUniformMinimaxComplexity_succ_le_of_excluded_prefix N hfail
  have hstep : (N : ℕ∞) < ((N + 1 : ℕ) : ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self N
  exact hstep.trans_le hsucc

/-- Excluding every natural budget at most a nonnegative real threshold
gives a strict complexity bound: the complexity is at least its floor plus
one, which is strictly greater than that real threshold. -/
theorem dimensionUniformMinimaxComplexity_gt_of_excluded_real_budget
    {p q Δ σ Lbar ε C : ℝ} (hC : 0 ≤ C)
    (hfail : ∀ M : ℕ, (M : ℝ) ≤ C →
      ¬ HasDimensionUniformGuarantee.{u, v} M p q Δ σ Lbar ε) :
    ENNReal.ofReal C <
      (dimensionUniformMinimaxComplexity.{u, v} p q Δ σ Lbar ε : ENNReal) := by
  have hfail_floor (M : ℕ) (hM : M ≤ ⌊C⌋₊) :
      ¬ HasDimensionUniformGuarantee.{u, v} M p q Δ σ Lbar ε := by
    have hMreal : (M : ℝ) ≤ (⌊C⌋₊ : ℝ) := by exact_mod_cast hM
    exact hfail M (hMreal.trans (Nat.floor_le hC))
  have hsucc := dimensionUniformMinimaxComplexity_succ_le_of_excluded_prefix
    (p := p) (q := q) (Δ := Δ) (σ := σ) (Lbar := Lbar) (ε := ε)
    ⌊C⌋₊ hfail_floor
  have hstrict : ENNReal.ofReal C < ((⌊C⌋₊ + 1 : ℕ) : ENNReal) := by
    rw [← ENNReal.ofReal_natCast]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hC).2
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one C
  have hcast : (((⌊C⌋₊ + 1 : ℕ) : ℕ∞) : ENNReal) ≤
      (dimensionUniformMinimaxComplexity.{u, v} p q Δ σ Lbar ε : ENNReal) :=
    ENat.toENNReal_le.2 hsucc
  exact hstrict.trans_le (by simpa only [ENat.toENNReal_coe] using hcast)

/-- The public fixed-cap theorem excludes every smaller natural response
budget. Its hard dimension is chosen separately for each such public budget;
dimension-uniform guarantees must cover each of those dimensions. -/
theorem gatedHaar_minimax_complexity_gt_response_budget
    {p q L Δ ε σ : ℝ} (N : ℕ)
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσε : ε ≤ σ)
    (hT64 : 64 ≤ gatedChainLength (L * Δ / ε ^ 2))
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * ((σ / ε) / 80) ^ 2 / (16 * 300 ^ 2)))
    (hN : (N : ℝ) ≤ gatedPublicRateConstant * (L * Δ / ε ^ 2) * (σ / ε) ^ 2) :
    (N : ℕ∞) < dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε := by
  apply dimensionUniformMinimaxComplexity_gt_of_excluded_prefix N
  intro M hM
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast hM
  exact gatedHaar_refutes_dimension_uniform_guarantee.{u}
    M hp hq hL hΔ hε hσε hT64 hlarge (hMN.trans hN)

/-- The manuscript's finite-q strict-K=1 minimax lower rate, in its stated
large-chain/large-noise regime. The explicit coefficient is the public
`10⁻²⁵`, which already accounts for the response-free output decision.
The seed universe is `0` and private randomness remains arbitrary in `u`.
There are no stochastic or algorithm-specific premises. -/
theorem gatedHaar_minimax_complexity_lower_bound
    {p q L Δ ε σ : ℝ}
    (hp : 1 < p ∧ p ≤ 2) (hq : 1 ≤ q)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hσε : ε ≤ σ)
    (hT64 : 64 ≤ gatedChainLength (L * Δ / ε ^ 2))
    (hlarge : 2 ≤ ((1 / 4005.25 : ℝ) * ((σ / ε) / 80) ^ 2 / (16 * 300 ^ 2))) :
    ENNReal.ofReal (gatedPublicRateConstant * (L * Δ / ε ^ 2) * (σ / ε) ^ 2) <
      (dimensionUniformMinimaxComplexity.{u, 0} p q Δ σ L ε : ENNReal) := by
  apply dimensionUniformMinimaxComplexity_gt_of_excluded_real_budget
  · unfold gatedPublicRateConstant
    positivity
  · intro M hM
    exact gatedHaar_refutes_dimension_uniform_guarantee.{u}
      M hp hq hL hΔ hε hσε hT64 hlarge hM

end

end HeavyTailedNoise
