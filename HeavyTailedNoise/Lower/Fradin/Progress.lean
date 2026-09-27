import HeavyTailedNoise.Lower.Fradin.Protocol
import HeavyTailedNoise.Probability.BernoulliCounting
import HeavyTailedNoise.Probability.GaussianSeedSplit

/-!
Actual adapted support progress under one shared Bernoulli bit per round.
The zero-respecting premise is only almost sure on the actual runs. No support
condition on unreachable histories, fixed private tape, conditional law,
stopping time, or Gaussian/Haar model is substituted.

The two deterministic response-tail properties and the population-gradient
barrier are explicit premises. A final lower-bound entry must discharge them
for its own actual scaled admissible oracle.
-/

namespace HeavyTailedNoise.Fradin

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false
universe v

/-- Coordinates numbered m and later, in zero-based Fin notation, are zero. -/
def tailZero {d : ℕ} (x : Point d) (m : ℕ) : Prop :=
  ∀ i : Fin d, m ≤ i.val → x i = 0

theorem tailZero.mono {d m l : ℕ} {x : Point d}
    (hx : tailZero x m) (hml : m ≤ l) : tailZero x l :=
  fun i hi => hx i (hml.trans hi)

/-- Pulling back a null exceptional set along the actual iid prefix law does
not require any structural hypothesis on the private measurable space. -/
theorem run_prefix_quasiMeasurePreserving {d K : ℕ}
    {Private : Type v} [MeasurableSpace Private]
    (O : FirstOrderOracle d Bool) (A : Algorithm d K Private) (n : ℕ) :
    Measure.QuasiMeasurePreserving
      (fun z : Private × (Fin (n+1) → Bool) =>
        (z.1, fun i : Fin n => z.2 i.castSucc))
      (A.privateLaw.prod (freshSeedLaw O.gradient (n+1)))
      (A.privateLaw.prod (freshSeedLaw O.gradient n)) := by
  letI := O.gradient.law_probability
  letI := A.private_probability
  have hsplit : MeasurePreserving
      (fun ξ : Fin (n+1) → Bool =>
        ((fun i : Fin n => ξ i.castSucc), ξ (Fin.last n)))
      (Measure.pi (fun _ : Fin (n+1) => O.gradient.law))
      ((Measure.pi (fun _ : Fin n => O.gradient.law)).prod O.gradient.law) := by
    refine ⟨?_, iidSeedLaw_map_prefix_last O.gradient.law n⟩
    exact (measurable_pi_iff.mpr fun i => measurable_pi_apply i.castSucc).prodMk
      (measurable_pi_apply (Fin.last n))
  have hprefix := MeasureTheory.QuasiMeasurePreserving.fst hsplit.quasiMeasurePreserving
  have hp : Measure.QuasiMeasurePreserving
      (Prod.map id (fun ξ : Fin (n+1) → Bool => fun i : Fin n => ξ i.castSucc))
      (A.privateLaw.prod (freshSeedLaw O.gradient (n+1)))
      (A.privateLaw.prod (freshSeedLaw O.gradient n)) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.QuasiMeasurePreserving.id A.privateLaw) hprefix
  have hmap :
      (Prod.map id (fun ξ : Fin (n+1) → Bool => fun i : Fin n => ξ i.castSucc)) =
      (fun z : Private × (Fin (n+1) → Bool) =>
        (z.1, fun i : Fin n => z.2 i.castSucc)) := by
    funext z
    cases z
    rfl
  rw [hmap] at hp
  exact hp

/-- The common reveal count controls every historical returned gradient and
all K decisions of the next response-free batch. All exceptions are under
privateLaw × the actual iid oracle seed law. -/
theorem ae_history_and_nextBatch_tailZero {d K : ℕ}
    {Private : Type v} [MeasurableSpace Private]
    (O : FirstOrderOracle d Bool) (A : Algorithm d K Private)
    (hZR : ZeroRespectingOn O A)
    (hfalse : ∀ (x : Point d) (m : ℕ), tailZero x m →
      tailZero (O.gradient.response x false) m)
    (htrue : ∀ (x : Point d) (m : ℕ), tailZero x m →
      tailZero (O.gradient.response x true) (m+1)) (n : ℕ) :
    ∀ᵐ z ∂A.privateLaw.prod (freshSeedLaw O.gradient n),
      (∀ (j : Fin n) (l : Fin K),
        tailZero (runTranscript O A z.1 n z.2 j l).2.2 (revealCount z.2)) ∧
      (∀ k : Fin K, tailZero (nextBatch O A n z.1 z.2 k) (revealCount z.2)) := by
  induction n with
  | zero =>
      filter_upwards [hZR 0] with z hz
      refine ⟨fun j => j.elim0, ?_⟩
      intro k i hi
      by_contra hx
      obtain ⟨j, l, hj⟩ := hz k i hx
      exact j.elim0
  | succ n ih =>
      filter_upwards [(run_prefix_quasiMeasurePreserving O A n).ae ih,
        hZR (n+1)] with z hz hzr
      let seedPrefix : Fin n → Bool := fun i => z.2 i.castSucc
      have hcount : revealCount z.2 = revealCount seedPrefix +
          if z.2 (Fin.last n) then 1 else 0 := revealCount_succ z.2
      have hmono : revealCount seedPrefix ≤ revealCount z.2 := by rw [hcount]; omega
      have hhist : ∀ (j : Fin (n+1)) (l : Fin K),
          tailZero (runTranscript O A z.1 (n+1) z.2 j l).2.2
            (revealCount z.2) := by
        intro j l
        refine Fin.lastCases ?_ (fun i => ?_) j
        · rw [runTranscript_last]
          change tailZero (O.gradient.response (nextBatch O A n z.1 seedPrefix l)
            (z.2 (Fin.last n))) (revealCount z.2)
          cases hbit : z.2 (Fin.last n) with
          | false =>
              have hc : revealCount z.2 = revealCount seedPrefix := by simpa [hbit] using hcount
              rw [hc]
              exact hfalse _ _ (hz.2 l)
          | true =>
              have hc : revealCount z.2 = revealCount seedPrefix + 1 := by simpa [hbit] using hcount
              rw [hc]
              exact htrue _ _ (hz.2 l)
        · rw [runTranscript_prefix]
          exact (hz.1 i l).mono hmono
      refine ⟨hhist, ?_⟩
      intro k i hi
      by_contra hx
      obtain ⟨j, l, hj⟩ := hzr k i hx
      exact hj (hhist j l i hi)

/-- The next batch has only coordinates revealed by the common shared bits. -/
theorem ae_nextBatch_tailZero {d K : ℕ} {Private : Type v}
    [MeasurableSpace Private]
    (O : FirstOrderOracle d Bool) (A : Algorithm d K Private)
    (hZR : ZeroRespectingOn O A)
    (hfalse : ∀ (x : Point d) (m : ℕ), tailZero x m →
      tailZero (O.gradient.response x false) m)
    (htrue : ∀ (x : Point d) (m : ℕ), tailZero x m →
      tailZero (O.gradient.response x true) (m+1)) (n : ℕ) :
    ∀ᵐ z ∂A.privateLaw.prod (freshSeedLaw O.gradient n),
      ∀ k : Fin K, tailZero (nextBatch O A n z.1 z.2 k) (revealCount z.2) :=
  (ae_history_and_nextBatch_tailZero O A hZR hfalse htrue n).mono fun _ hz => hz.2

/-- One common failure event leaves an unrevealed zero coordinate in every
slot, rather than separate slot-specific exceptional events. -/
theorem ae_common_unrevealed_coordinate {d K T : ℕ} {Private : Type v}
    [MeasurableSpace Private]
    (O : FirstOrderOracle d Bool) (A : Algorithm d K Private)
    (hZR : ZeroRespectingOn O A)
    (hfalse : ∀ (x : Point d) (m : ℕ), tailZero x m →
      tailZero (O.gradient.response x false) m)
    (htrue : ∀ (x : Point d) (m : ℕ), tailZero x m →
      tailZero (O.gradient.response x true) (m+1))
    (hTd : T ≤ d) (n : ℕ) :
    ∀ᵐ z ∂A.privateLaw.prod (freshSeedLaw O.gradient n),
      revealCount z.2 < T → ∀ k : Fin K,
        ∃ i : Fin d, (nextBatch O A n z.1 z.2 k) i = 0 := by
  filter_upwards [ae_nextBatch_tailZero O A hZR hfalse htrue n] with z hz
  intro hcount k
  let i : Fin d := ⟨revealCount z.2, lt_of_lt_of_le hcount hTd⟩
  exact ⟨i, hz k i le_rfl⟩

/-- The common count event has probability at least 3/4, integrated over any
independent private probability law. This reuses BernoulliCounting's bound. -/
theorem revealCount_good_probability {d K T : ℕ} {Private : Type v}
    [MeasurableSpace Private] (A : Algorithm d K Private)
    (θ : unitInterval) (n : ℕ) (hT : 0 < T)
    (hbudget : 4*(n : ℝ)*(θ : ℝ) ≤ (T : ℝ)) :
    3/4 ≤ (A.privateLaw.prod
      (Measure.pi (fun _ : Fin n => bernoulliMeasure true false θ))).real
        {z | revealCount z.2 < T} := by
  letI := A.private_probability
  let π : Measure (Fin n → Bool) := Measure.pi (fun _ => bernoulliMeasure true false θ)
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have htail := revealCount_tail_le_quarter n θ hTreal hbudget
  have hbad : MeasurableSet {ξ : Fin n → Bool | (T : ℝ) ≤ (revealCount ξ : ℝ)} :=
    (Set.toFinite _).measurableSet
  have hgoodcomp : {ξ : Fin n → Bool | revealCount ξ < T} =
      {ξ : Fin n → Bool | (T : ℝ) ≤ (revealCount ξ : ℝ)}ᶜ := by
    ext ξ
    change revealCount ξ < T ↔ ¬ ((T : ℝ) ≤ (revealCount ξ : ℝ))
    rw [not_le]
    norm_cast
  have hgood : 3/4 ≤ π.real {ξ | revealCount ξ < T} := by
    rw [hgoodcomp, probReal_compl_eq_one_sub hbad]
    change 3/4 ≤ 1 - (Measure.pi (fun _ : Fin n =>
      bernoulliMeasure true false θ)).real {ξ | (T : ℝ) ≤ (revealCount ξ : ℝ)}
    linarith
  have hevent : {z : Private × (Fin n → Bool) | revealCount z.2 < T} =
      (Set.univ : Set Private) ×ˢ {ξ | revealCount ξ < T} := by
    ext z
    simp
  rw [hevent, measureReal_prod_prod, probReal_univ, one_mul]
  exact hgood

/-- A common unrevealed-tail event and a gradient barrier give every slot a
strict expected-norm lower bound. Legality, actual response tails and the
actual population barrier remain visible premises of this generic bridge. -/
theorem slotRisk_gt_of_Bernoulli_tail_barrier {d K T : ℕ}
    {Private : Type v} [MeasurableSpace Private]
    {p q Δ σ L ε : ℝ} (I : Admissible d Bool p q Δ σ L)
    (A : Algorithm d K Private) (θ : unitInterval)
    (hLaw : I.oracle.law = bernoulliMeasure true false θ)
    (hZR : ZeroRespectingOn (FirstOrderOracle.ofAdmissible I) A)
    (hfalse : ∀ (x : Point d) (m : ℕ), tailZero x m →
      tailZero (I.oracle.response x false) m)
    (htrue : ∀ (x : Point d) (m : ℕ), tailZero x m →
      tailZero (I.oracle.response x true) (m+1))
    (hbarrier : ∀ (x : Point d) (m : ℕ), m < d → tailZero x m →
      2*ε < ‖I.objective.grad x‖)
    (hε : 0 < ε) (hT : 0 < T) (hTd : T ≤ d) (n : ℕ)
    (hbudget : 4*(n : ℝ)*(θ : ℝ) ≤ (T : ℝ)) (k : Fin K) :
    ENNReal.ofReal ε < slotRisk I A n k := by
  classical
  let μ := A.privateLaw.prod (freshSeedLaw I.oracle n)
  letI : IsProbabilityMeasure μ := runLaw_probability (FirstOrderOracle.ofAdmissible I) A n
  let E : Set (Private × (Fin n → Bool)) := {z | revealCount z.2 < T}
  have hEmeas : MeasurableSet E :=
    ((Set.toFinite {ξ : Fin n → Bool | revealCount ξ < T}).measurableSet).preimage
      measurable_snd
  have hprob : 3/4 ≤ μ.real E := by
    simpa only [μ, E, freshSeedLaw, hLaw] using
      revealCount_good_probability A θ n hT hbudget
  have hmass : ENNReal.ofReal (3/4 : ℝ) ≤ μ E := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ E)]
    exact ENNReal.ofReal_le_ofReal hprob
  have htail := ae_nextBatch_tailZero (FirstOrderOracle.ofAdmissible I) A
    hZR hfalse htrue n
  have hlower : ENNReal.ofReal (2*ε) * μ E ≤ slotRisk I A n k := by
    rw [← lintegral_indicator_const hEmeas]
    apply lintegral_mono_ae
    filter_upwards [htail] with z hz
    by_cases hE : z ∈ E
    · rw [Set.indicator_of_mem hE]
      have hc : revealCount z.2 < d := lt_of_lt_of_le hE hTd
      exact ENNReal.ofReal_le_ofReal (hbarrier _ _ hc (hz k)).le
    · rw [Set.indicator_of_notMem hE]
      exact zero_le
  have hstrict : ENNReal.ofReal ε <
      ENNReal.ofReal (2*ε) * ENNReal.ofReal (3/4 : ℝ) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*ε)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).2
    linarith
  exact hstrict.trans_le ((mul_le_mul_right hmass _).trans hlower)

end
end HeavyTailedNoise.Fradin
