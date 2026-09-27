import HeavyTailedNoise.Lower.Fradin.Complexity

/-!
Response-only algorithms from Fradin v2 B.1.3 and the canonical query-record
representation use the same objective, oracle and iid runtime. An algorithm's
own queries are reconstructed from its private seed and past observations.
The reconstruction has no oracle or oracle-seed argument. Equality with the
canonical algorithm is asserted on actual runs, not on unreachable histories.
The first-slot stationarity normalization is the same in both representations.
-/

namespace HeavyTailedNoise.Fradin
open MeasureTheory
noncomputable section
set_option autoImplicit false
universe u v

abbrev ObservationTranscript (d K n : ℕ) := Fin n → Fin K → ℝ × Point d

def eraseQueries {d K n : ℕ} (h : Transcript d K n) : ObservationTranscript d K n :=
  fun j k => (h j k).2

theorem measurable_eraseQueries (d K n : ℕ) :
    Measurable (eraseQueries (d := d) (K := K) (n := n)) :=
  measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k =>
    measurable_snd.comp ((measurable_pi_apply k).comp (measurable_pi_apply j))

/-- The source decision maps see only past population values and gradients. -/
structure ObservedAlgorithm (d K : ℕ) (Private : Type v) [MeasurableSpace Private] where
  privateLaw : Measure Private
  private_probability : IsProbabilityMeasure privateLaw
  decide : (n : ℕ) → Private → ObservationTranscript d K n → Batch d K
  measurable_decide : ∀ n, Measurable
    (fun z : Private × ObservationTranscript d K n => decide n z.1 z.2)

/-- Forget the query component before applying each original decision map. -/
def ObservedAlgorithm.toAlgorithm {d K : ℕ} {Private : Type v}
    [MeasurableSpace Private] (B : ObservedAlgorithm d K Private) : Algorithm d K Private where
  privateLaw := B.privateLaw
  private_probability := B.private_probability
  decide := fun n r h => B.decide n r (eraseQueries h)
  measurable_decide := fun n => (B.measurable_decide n).comp
    (measurable_fst.prodMk ((measurable_eraseQueries d K n).comp measurable_snd))

@[simp] theorem ObservedAlgorithm.toAlgorithm_privateLaw {d K : ℕ} {Private : Type v}
    [MeasurableSpace Private] (B : ObservedAlgorithm d K Private) :
    B.toAlgorithm.privateLaw = B.privateLaw := rfl

/-- The observation-only runtime is the projection of the one canonical runtime. -/
def observedRun {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (B : ObservedAlgorithm d K Private)
    (r : Private) (n : ℕ) (seeds : Fin n → Seed) : ObservationTranscript d K n :=
  eraseQueries (runTranscript O B.toAlgorithm r n seeds)

def observedNextBatch {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (B : ObservedAlgorithm d K Private)
    (n : ℕ) (r : Private) (seeds : Fin n → Seed) : Batch d K :=
  B.decide n r (observedRun O B r n seeds)

theorem observedRun_succ {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (B : ObservedAlgorithm d K Private)
    (r : Private) (n : ℕ) (seeds : Fin (n+1) → Seed) :
    observedRun O B r (n+1) seeds =
      Fin.snoc (observedRun O B r n (fun i => seeds i.castSucc))
        (fun k => let x := observedNextBatch O B n r (fun i => seeds i.castSucc) k
          (O.value x, O.gradient.response x (seeds (Fin.last n)))) := by
  funext j k
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [observedRun, observedNextBatch, eraseQueries, runTranscript,
      ObservedAlgorithm.toAlgorithm]
  · simp [observedRun, eraseQueries, runTranscript]

/-- Recover only the algorithm's own query book from r and an observation list. -/
def reconstruct {d K : ℕ} {Private : Type v} [MeasurableSpace Private]
    (A : Algorithm d K Private) (r : Private) :
    (n : ℕ) → ObservationTranscript d K n → Transcript d K n
  | 0, _ => fun j => j.elim0
  | n+1, obs =>
    let h := reconstruct A r n (fun j => obs j.castSucc)
    let x := A.decide n r h
    Fin.snoc h (fun k => (x k, obs (Fin.last n) k))

theorem measurable_reconstruct {d K : ℕ} {Private : Type v}
    [MeasurableSpace Private] (A : Algorithm d K Private) (n : ℕ) :
    Measurable (fun z : Private × ObservationTranscript d K n => reconstruct A z.1 n z.2) := by
  induction n with
  | zero =>
      refine measurable_pi_iff.mpr ?_
      intro j
      exact j.elim0
  | succ n ih =>
      have hp : Measurable (fun z : Private × ObservationTranscript d K (n+1) =>
          (z.1, fun j : Fin n => z.2 j.castSucc)) :=
        measurable_fst.prodMk (measurable_pi_iff.mpr fun j =>
          (measurable_pi_apply j.castSucc).comp measurable_snd)
      have hh := ih.comp hp
      have hx := (A.measurable_decide n).comp (measurable_fst.prodMk hh)
      have hl : Measurable (fun z : Private × ObservationTranscript d K (n+1) =>
          fun k : Fin K =>
            (A.decide n z.1 (reconstruct A z.1 n (fun j => z.2 j.castSucc)) k,
              z.2 (Fin.last n) k)) := by
        refine measurable_pi_iff.mpr fun k => ?_
        exact ((measurable_pi_apply k).comp hx).prodMk
          ((measurable_pi_apply k).comp
            ((measurable_pi_apply (Fin.last n)).comp measurable_snd))
      refine measurable_pi_iff.mpr fun j => ?_
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [reconstruct, Fin.snoc_last] using hl
      · simpa only [reconstruct, Fin.snoc_castSucc, Function.comp_def] using
          (measurable_pi_apply i).comp hh

theorem eraseQueries_reconstruct {d K : ℕ} {Private : Type v}
    [MeasurableSpace Private] (A : Algorithm d K Private) (r : Private)
    (n : ℕ) (obs : ObservationTranscript d K n) :
    eraseQueries (reconstruct A r n obs) = obs := by
  induction n with
  | zero =>
      funext j
      exact j.elim0
  | succ n ih =>
      funext j k
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [eraseQueries, reconstruct]
      · simpa only [eraseQueries, reconstruct, Fin.snoc_castSucc] using
          congrFun (congrFun (ih (fun j => obs j.castSucc)) i) k

/-- The reconstruction of a real transcript is exactly that transcript. -/
theorem reconstruct_eraseQueries_run {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private) (r : Private)
    (n : ℕ) (seeds : Fin n → Seed) :
    reconstruct A r n (eraseQueries (runTranscript O A r n seeds)) =
      runTranscript O A r n seeds := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hobs :
          (fun j : Fin n => eraseQueries (runTranscript O A r (n+1) seeds) j.castSucc) =
            eraseQueries (runTranscript O A r n (fun i => seeds i.castSucc)) := by
        funext j k
        simp only [eraseQueries, runTranscript_prefix]
      change Fin.snoc (α := fun _ : Fin (n+1) => BatchRecord d K)
        (reconstruct A r n (fun j => eraseQueries (runTranscript O A r (n+1) seeds) j.castSucc))
        (fun k =>
          (A.decide n r (reconstruct A r n
            (fun j => eraseQueries (runTranscript O A r (n+1) seeds) j.castSucc)) k,
            eraseQueries (runTranscript O A r (n+1) seeds) (Fin.last n) k)) = _
      rw [hobs, ih]
      funext j k
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last, eraseQueries, runTranscript_last, nextBatch]
      · simp only [Fin.snoc_castSucc, runTranscript_prefix]

/-- Response-only simulation of a rich algorithm, using its own reconstruction. -/
def forgetQueries {d K : ℕ} {Private : Type v} [MeasurableSpace Private]
    (A : Algorithm d K Private) : ObservedAlgorithm d K Private where
  privateLaw := A.privateLaw
  private_probability := A.private_probability
  decide := fun n r obs => A.decide n r (reconstruct A r n obs)
  measurable_decide := fun n => (A.measurable_decide n).comp
    (measurable_fst.prodMk (measurable_reconstruct A n))

@[simp] theorem forgetQueries_privateLaw {d K : ℕ} {Private : Type v}
    [MeasurableSpace Private] (A : Algorithm d K Private) :
    (forgetQueries A).privateLaw = A.privateLaw := rfl

/-- Actual query records coincide for every oracle, private value and finite tape. -/
theorem run_forgetQueries_toAlgorithm {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private) (r : Private)
    (n : ℕ) (seeds : Fin n → Seed) :
    runTranscript O (forgetQueries A).toAlgorithm r n seeds =
      runTranscript O A r n seeds := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [runTranscript, ih]
      have hx : (forgetQueries A).toAlgorithm.decide n r
          (runTranscript O A r n (fun i => seeds i.castSucc)) =
            A.decide n r (runTranscript O A r n (fun i => seeds i.castSucc)) := by
        change A.decide n r (reconstruct A r n
          (eraseQueries (runTranscript O A r n (fun i => seeds i.castSucc)))) = _
        rw [reconstruct_eraseQueries_run]
      rw [hx]

theorem nextBatch_forgetQueries_toAlgorithm {d K : ℕ}
    {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private)
    (n : ℕ) (r : Private) (seeds : Fin n → Seed) :
    nextBatch O (forgetQueries A).toAlgorithm n r seeds = nextBatch O A n r seeds := by
  unfold nextBatch
  rw [run_forgetQueries_toAlgorithm]
  change A.decide n r (reconstruct A r n (eraseQueries (runTranscript O A r n seeds))) = _
  rw [reconstruct_eraseQueries_run]

theorem observedRun_forgetQueries {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private) (r : Private)
    (n : ℕ) (seeds : Fin n → Seed) :
    observedRun O (forgetQueries A) r n seeds =
      eraseQueries (runTranscript O A r n seeds) := by
  unfold observedRun
  rw [run_forgetQueries_toAlgorithm]

/-- Support condition stated using only the original observed gradients. -/
def ObservedZeroRespectingOn {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (B : ObservedAlgorithm d K Private) : Prop :=
  ∀ n, ∀ᵐ z ∂B.privateLaw.prod (freshSeedLaw O.gradient n),
    ∀ k : Fin K, ∀ i : Fin d,
      observedNextBatch O B n z.1 z.2 k i ≠ 0 →
        ∃ j : Fin n, ∃ l : Fin K, (observedRun O B z.1 n z.2 j l).2 i ≠ 0

/-- All C¹ populations and integrable unbiased oracles, with explicit universes. -/
def ObservedZeroRespecting {d K : ℕ} {Private : Type v} [MeasurableSpace Private]
    (B : ObservedAlgorithm d K Private) : Prop :=
  ∀ (Seed : Type u) (m : MeasurableSpace Seed),
    letI := m
    ∀ O : FirstOrderOracle d Seed, O.IsUnbiased → ObservedZeroRespectingOn O B

theorem observedZeroRespectingOn_iff {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (B : ObservedAlgorithm d K Private) :
    ObservedZeroRespectingOn O B ↔ ZeroRespectingOn O B.toAlgorithm := Iff.rfl

theorem observedZeroRespecting_iff {d K : ℕ} {Private : Type v}
    [MeasurableSpace Private] (B : ObservedAlgorithm d K Private) :
    ObservedZeroRespecting.{u, v} B ↔ ZeroRespecting.{u, v} B.toAlgorithm := Iff.rfl

theorem zeroRespectingOn_forgetQueries_toAlgorithm_iff {d K : ℕ}
    {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    (O : FirstOrderOracle d Seed) (A : Algorithm d K Private) :
    ZeroRespectingOn O (forgetQueries A).toAlgorithm ↔ ZeroRespectingOn O A := by
  simp only [ZeroRespectingOn, ObservedAlgorithm.toAlgorithm_privateLaw,
    forgetQueries_privateLaw, nextBatch_forgetQueries_toAlgorithm, run_forgetQueries_toAlgorithm]

theorem observedZeroRespecting_forgetQueries_iff {d K : ℕ} {Private : Type v}
    [MeasurableSpace Private] (A : Algorithm d K Private) :
    ObservedZeroRespecting.{u, v} (forgetQueries A) ↔ ZeroRespecting.{u, v} A := by
  rw [observedZeroRespecting_iff]
  constructor
  · intro h Seed m
    letI := m
    intro O hO
    exact (zeroRespectingOn_forgetQueries_toAlgorithm_iff O A).mp (h Seed m O hO)
  · intro h Seed m
    letI := m
    intro O hO
    exact (zeroRespectingOn_forgetQueries_toAlgorithm_iff O A).mpr (h Seed m O hO)

def observedSlotRisk {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (B : ObservedAlgorithm d K Private) (n : ℕ) (k : Fin K) : ENNReal :=
  ∫⁻ z : Private × (Fin n → Seed),
    ENNReal.ofReal ‖I.objective.grad
      (observedNextBatch (FirstOrderOracle.ofAdmissible I) B n z.1 z.2 k)‖
    ∂B.privateLaw.prod (freshSeedLaw I.oracle n)

theorem observedSlotRisk_eq {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (B : ObservedAlgorithm d K Private) (n : ℕ) (k : Fin K) :
    observedSlotRisk I B n k = slotRisk I B.toAlgorithm n k := rfl

theorem slotRisk_forgetQueries_toAlgorithm {d K : ℕ}
    {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (A : Algorithm d K Private) (n : ℕ) (k : Fin K) :
    slotRisk I (forgetQueries A).toAlgorithm n k = slotRisk I A n k := by
  change (∫⁻ z : Private × (Fin n → Seed),
    ENNReal.ofReal ‖I.objective.grad
      (nextBatch (FirstOrderOracle.ofAdmissible I) (forgetQueries A).toAlgorithm n z.1 z.2 k)‖
    ∂A.privateLaw.prod (freshSeedLaw I.oracle n)) = _
  simp only [nextBatch_forgetQueries_toAlgorithm, slotRisk]

def observedRoundInfimum {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (B : ObservedAlgorithm d K Private) (ε : ℝ) (k : Fin K) : ENNReal :=
  sInf {r : ENNReal | ∃ n : ℕ,
    r = ((n+1 : ℕ) : ENNReal) ∧ observedSlotRisk I B n k ≤ ENNReal.ofReal ε}

theorem observedRoundInfimum_eq {d K : ℕ} {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (B : ObservedAlgorithm d K Private) (ε : ℝ) (k : Fin K) :
    observedRoundInfimum I B ε k = roundInfimum I B.toAlgorithm ε k := rfl

theorem roundInfimum_forgetQueries_toAlgorithm {d K : ℕ}
    {Seed : Type u} {Private : Type v}
    [MeasurableSpace Seed] [MeasurableSpace Private]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (A : Algorithm d K Private) (ε : ℝ) (k : Fin K) :
    roundInfimum I (forgetQueries A).toAlgorithm ε k = roundInfimum I A ε k := by
  simp only [roundInfimum, slotRisk_forgetQueries_toAlgorithm]

/-- Infimum over the source's response-only globally zero-respecting algorithms. -/
def observedInstanceRoundComplexity {d K : ℕ} {Seed : Type u} [MeasurableSpace Seed]
    {p q Δ σ L : ℝ} (I : Admissible d Seed p q Δ σ L)
    (ε : ℝ) (k : Fin K) : ENNReal :=
  ⨅ (Private : Type v) (m : MeasurableSpace Private),
    letI := m
    ⨅ (B : ObservedAlgorithm d K Private) (_ : ObservedZeroRespecting.{u, v} B),
      observedRoundInfimum I B ε k

theorem instanceRoundComplexity_le_observed {d K : ℕ}
    {Seed : Type u} [MeasurableSpace Seed]
    {p q Δ σ L ε : ℝ} (I : Admissible d Seed p q Δ σ L) (k : Fin K) :
    instanceRoundComplexity.{u, v} I ε k ≤ observedInstanceRoundComplexity.{u, v} I ε k := by
  unfold observedInstanceRoundComplexity
  refine le_iInf fun Private => le_iInf fun m => ?_
  letI := m
  refine le_iInf fun B => le_iInf fun hB => ?_
  rw [observedRoundInfimum_eq]
  unfold instanceRoundComplexity
  exact iInf_le_of_le Private <| iInf_le_of_le m <| iInf_le_of_le B.toAlgorithm <|
    iInf_le_of_le ((observedZeroRespecting_iff B).mp hB) le_rfl

theorem observedInstanceRoundComplexity_le {d K : ℕ}
    {Seed : Type u} [MeasurableSpace Seed]
    {p q Δ σ L ε : ℝ} (I : Admissible d Seed p q Δ σ L) (k : Fin K) :
    observedInstanceRoundComplexity.{u, v} I ε k ≤ instanceRoundComplexity.{u, v} I ε k := by
  unfold instanceRoundComplexity
  refine le_iInf fun Private => le_iInf fun m => ?_
  letI := m
  refine le_iInf fun A => le_iInf fun hA => ?_
  have hb : ObservedZeroRespecting.{u, v} (forgetQueries A) :=
    (observedZeroRespecting_forgetQueries_iff A).mpr hA
  have hle : observedInstanceRoundComplexity.{u, v} I ε k ≤
      observedRoundInfimum I (forgetQueries A) ε k := by
    unfold observedInstanceRoundComplexity
    exact iInf_le_of_le Private <| iInf_le_of_le m <| iInf_le_of_le (forgetQueries A) <|
      iInf_le_of_le hb le_rfl
  rw [observedRoundInfimum_eq, roundInfimum_forgetQueries_toAlgorithm] at hle
  exact hle

theorem observedInstanceRoundComplexity_eq {d K : ℕ}
    {Seed : Type u} [MeasurableSpace Seed]
    {p q Δ σ L ε : ℝ} (I : Admissible d Seed p q Δ σ L) (k : Fin K) :
    observedInstanceRoundComplexity.{u, v} I ε k = instanceRoundComplexity.{u, v} I ε k :=
  le_antisymm (observedInstanceRoundComplexity_le I k) (instanceRoundComplexity_le_observed I k)

def observedObjectiveRoundComplexity {d K : ℕ} {p q Δ σ L : ℝ}
    (F : Objective d Δ) (ε : ℝ) (k : Fin K) : ENNReal :=
  ⨆ (Seed : Type u) (m : MeasurableSpace Seed),
    letI := m
    ⨆ (I : Admissible d Seed p q Δ σ L) (_ : I.objective = F),
      observedInstanceRoundComplexity.{u, v} I ε k

def observedSourceRoundComplexity (K : ℕ) (hK : 0 < K)
    (p q Δ σ L ε : ℝ) : ENNReal :=
  ⨆ d : ℕ, ⨆ F : Objective d Δ,
    observedObjectiveRoundComplexity.{u, v} (p := p) (q := q) (σ := σ) (L := L)
      F ε ⟨0, hK⟩

/-- Same natural rounds, same stationarity slot, same sup/inf order and value. -/
theorem observedSourceRoundComplexity_eq (K : ℕ) (hK : 0 < K)
    (p q Δ σ L ε : ℝ) :
    observedSourceRoundComplexity.{u, v} K hK p q Δ σ L ε =
      sourceRoundComplexity.{u, v} K hK p q Δ σ L ε := by
  unfold observedSourceRoundComplexity sourceRoundComplexity
    observedObjectiveRoundComplexity objectiveRoundComplexity
  simp only [observedInstanceRoundComplexity_eq]

end
end HeavyTailedNoise.Fradin
