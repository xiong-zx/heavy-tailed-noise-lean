import HeavyTailedNoise.Lower.Fradin.Protocol

/-!
The natural-round distributional complexity in Fradin et al.,
arXiv:2512.18713v2, Section B.1.4. The source's batched `∇F(𝒙)` notation
has no specified batch norm. Here the designated first query is used for the
stationarity test. All-slot lower bounds cover this normalization.

A round numbered n+1 is tested before its responses, after n completed rounds.
The order is sup dimension, sup population objective, sup legal oracle,
inf global zero-respecting algorithm (including its arbitrary measurable
private probability space), inf successful natural round. Empty infima are ∞.
No expected stopping time or fixed response budget is substituted.

`u` is the oracle-seed universe and `v` is the private-space universe. All
measurable spaces and probability laws on types in those universes are included.
-/

namespace HeavyTailedNoise.Fradin

open MeasureTheory
noncomputable section
set_option autoImplicit false
universe u v

/-- Literal infimum of successful queried rounds, with the source's t≥1 indexing. -/
def roundInfimum {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (A : Algorithm d K Private) (ε : ℝ) (k : Fin K) : ENNReal :=
  sInf {r : ENNReal | ∃ n : ℕ,
    r = ((n + 1 : ℕ) : ENNReal) ∧ slotRisk I A n k ≤ ENNReal.ofReal ε}

/-- The source's infimum over the entire global algorithm class. -/
def instanceRoundComplexity {d K : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (ε : ℝ) (k : Fin K) : ENNReal :=
  ⨅ (Private : Type v) (m : MeasurableSpace Private),
    letI := m
    ⨅ (A : Algorithm d K Private) (_ : ZeroRespecting.{u, v} A),
      roundInfimum I A ε k

/-- Legal oracles with exactly the given population objective, including its
value and gradient. Equality is equality of the existing `Objective` record. -/
def objectiveRoundComplexity {d K : ℕ} {p q Δ σ L : ℝ}
    (F : Objective d Δ) (ε : ℝ) (k : Fin K) : ENNReal :=
  ⨆ (Seed : Type u) (m : MeasurableSpace Seed),
    letI := m
    ⨆ (I : Admissible d Seed p q Δ σ L) (_ : I.objective = F),
      instanceRoundComplexity.{u, v} I ε k

/-- The oracle-fiber equality fixes exactly the population value and gradient;
the remaining objective fields are proofs and are identified by proof irrelevance. -/
theorem objective_eq_iff_value_grad_eq {d : ℕ} {Δ : ℝ} (F G : Objective d Δ) :
    F = G ↔ F.value = G.value ∧ F.grad = G.grad := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hv, hg⟩
    cases F
    cases G
    cases hv
    cases hg
    rfl

/-- Fradin v2 B.1.4's distributional complexity, with a first-slot normalization.
The dimension and population objective are selected before the algorithm. -/
def sourceRoundComplexity (K : ℕ) (hK : 0 < K) (p q Δ σ L ε : ℝ) : ENNReal :=
  ⨆ d : ℕ, ⨆ F : Objective d Δ,
    objectiveRoundComplexity.{u, v} (p := p) (q := q) (σ := σ) (L := L)
      F ε ⟨0, hK⟩

theorem roundInfimum_le_of_success {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L ε : ℝ} (I : Admissible d Seed p q Δ σ L)
    (A : Algorithm d K Private) (k : Fin K) (n : ℕ)
    (h : slotRisk I A n k ≤ ENNReal.ofReal ε) :
    roundInfimum I A ε k ≤ ((n + 1 : ℕ) : ENNReal) :=
  sInf_le ⟨n, rfl, h⟩

/-- In particular, no success at any round gives the literal empty-infimum ∞. -/
theorem roundInfimum_eq_top_of_no_success {d K : ℕ}
    {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L ε : ℝ} (I : Admissible d Seed p q Δ σ L)
    (A : Algorithm d K Private) (k : Fin K)
    (h : ∀ n, ENNReal.ofReal ε < slotRisk I A n k) :
    roundInfimum I A ε k = ⊤ := by
  have hempty : {r : ENNReal | ∃ n : ℕ,
      r = ((n + 1 : ℕ) : ENNReal) ∧ slotRisk I A n k ≤ ENNReal.ofReal ε} = ∅ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨n, _, hs⟩
    exact (not_le_of_gt (h n)) hs
  rw [roundInfimum, hempty]
  exact sInf_empty

theorem one_le_roundInfimum {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L ε : ℝ} (I : Admissible d Seed p q Δ σ L)
    (A : Algorithm d K Private) (k : Fin K) : 1 ≤ roundInfimum I A ε k := by
  refine le_sInf ?_
  rintro r ⟨n, rfl, _⟩
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- Risk lower bounds through every natural queried round at most C imply the
same real threshold for the round infimum, without monotonicity assumptions. -/
theorem roundInfimum_ge_of_risk_lower {d K : ℕ}
    {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L ε C : ℝ} (I : Admissible d Seed p q Δ σ L)
    (A : Algorithm d K Private) (k : Fin K)
    (h : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≤ C →
      ENNReal.ofReal ε < slotRisk I A n k) :
    ENNReal.ofReal C ≤ roundInfimum I A ε k := by
  refine le_sInf ?_
  rintro r ⟨n, rfl, hs⟩
  by_cases hn : ((n + 1 : ℕ) : ℝ) ≤ C
  · exact ((not_le_of_gt (h n hn)) hs).elim
  · have hc : C ≤ ((n + 1 : ℕ) : ℝ) := le_of_lt (lt_of_not_ge hn)
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hc

/-- The risk-to-complexity bridge keeps every private space and every globally
zero-respecting full-history algorithm inside the source's infimum. -/
theorem instanceRoundComplexity_ge_of_risk_lower {d K : ℕ}
    {Seed : Type u} [MeasurableSpace Seed]
    {p q Δ σ L ε C : ℝ} (I : Admissible d Seed p q Δ σ L) (k : Fin K)
    (h : ∀ (Private : Type v) (m : MeasurableSpace Private),
      letI := m
      ∀ (A : Algorithm d K Private), ZeroRespecting.{u, v} A →
        ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≤ C →
          ENNReal.ofReal ε < slotRisk I A n k) :
    ENNReal.ofReal C ≤ instanceRoundComplexity.{u, v} I ε k := by
  unfold instanceRoundComplexity
  refine le_iInf fun Private => le_iInf fun m => ?_
  letI := m
  refine le_iInf fun A => le_iInf fun hA => ?_
  exact roundInfimum_ge_of_risk_lower I A k (h Private m A hA)

/-- A fixed instance is below the outer suprema in exactly the source order. -/
theorem instanceRoundComplexity_le_source {d K : ℕ}
    {Seed : Type u} [MeasurableSpace Seed]
    {p q Δ σ L ε : ℝ} (hK : 0 < K) (I : Admissible d Seed p q Δ σ L) :
    instanceRoundComplexity.{u, v} I ε ⟨0, hK⟩ ≤
      sourceRoundComplexity.{u, v} K hK p q Δ σ L ε := by
  unfold sourceRoundComplexity objectiveRoundComplexity
  exact le_iSup_of_le d <| le_iSup_of_le I.objective <|
    le_iSup_of_le Seed <| le_iSup_of_le inferInstance <|
    le_iSup_of_le I <| le_iSup_of_le rfl le_rfl

/-- All-slot risk lower bounds on one legal instance imply the source complexity
lower bound. The premise concerns the actual response-free queried decisions. -/
theorem sourceRoundComplexity_ge_of_all_slot_risk_lower {d K : ℕ}
    {Seed : Type u} [MeasurableSpace Seed]
    {p q Δ σ L ε C : ℝ} (hK : 0 < K) (I : Admissible d Seed p q Δ σ L)
    (h : ∀ (Private : Type v) (m : MeasurableSpace Private),
      letI := m
      ∀ (A : Algorithm d K Private), ZeroRespecting.{u, v} A →
        ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) ≤ C →
          ∀ k : Fin K, ENNReal.ofReal ε < slotRisk I A n k) :
    ENNReal.ofReal C ≤ sourceRoundComplexity.{u, v} K hK p q Δ σ L ε := by
  apply le_trans (instanceRoundComplexity_ge_of_risk_lower I ⟨0, hK⟩ ?_)
    (instanceRoundComplexity_le_source hK I)
  intro Private m
  letI := m
  intro A hA n hn
  exact h Private m A hA n hn ⟨0, hK⟩

end
end HeavyTailedNoise.Fradin
