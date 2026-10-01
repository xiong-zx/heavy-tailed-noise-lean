import HeavyTailedNoise.Upper.K1.InitialMemoryCanonical
import HeavyTailedNoise.Upper.Foundations.FiniteAverageL2

/-!
The canonical initialization term is genuinely in L² under the one seed
tape. The finite-time L²-to-L¹ lemma then gives the exact expected average
norm needed by the estimator-risk assembly.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem actualInitialMemorySampleError_seed_memLp_two
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (t : ℕ) :
    MemLp (fun seeds : Fin (responseCount P) → Seed =>
      actualInitialMemorySampleError P O seeds t) 2
      (freshSeedLaw O (responseCount P)) := by
  by_cases hpos : 0 < initialResponses P
  · letI : IsProbabilityMeasure O.law := O.law_probability
    letI : IsProbabilityMeasure (freshSeedLaw O (initialResponses P)) :=
      freshSeedLaw_probability O (initialResponses P)
    let pairLaw := O.law.prod (freshSeedLaw O (initialResponses P))
    have hpairMeas := measurable_initialMemoryErrorAtPair P O t
    have hpairSq := initialMemoryErrorAtPair_sq_integrable P O t
    have hpair : MemLp (initialMemoryErrorAtPair P O t) 2 pairLaw :=
      (memLp_two_iff_integrable_sq_norm
        hpairMeas.aestronglyMeasurable).2 hpairSq
    have hmap := measurePreserving_first_initialSeedBlock P O
    have hcomp := hpair.comp_measurePreserving hmap
    have hfun :
        (fun seeds : Fin (responseCount P) → Seed =>
          actualInitialMemorySampleError P O seeds t) =
        initialMemoryErrorAtPair P O t ∘
          (fun seeds =>
            (seeds ⟨0, responseCount_pos P⟩,
              initialSeedBlock P seeds)) := by
      funext seeds
      exact actualInitialMemorySampleError_eq_pair P O seeds t hpos
    rw [hfun]
    exact hcomp
  · have hzero : initialResponses P = 0 := Nat.eq_zero_of_not_pos hpos
    have hfun :
        (fun seeds : Fin (responseCount P) → Seed =>
          actualInitialMemorySampleError P O seeds t) =
        (fun _ => (0 : Point d)) := by
      funext seeds
      exact actualInitialMemorySampleError_zero_of_no_initial
        P O seeds t hzero
    rw [hfun]
    exact MemLp.zero'

theorem Admissible.paperSchedule_actualInitialMemoryError_seed_memLp_two
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch)
    (hκ : 0 < κ) (hκle : κ ≤ 1)
    (hCb : 0 < Cb) (hCI : 0 < CI)
    (t : ℕ) (ht : 0 < t) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI
    MemLp (fun seeds : Fin (responseCount P) → Seed =>
      actualInitialMemoryError P I.oracle seeds t) 2
      (freshSeedLaw I.oracle (responseCount P)) := by
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCI
  dsimp only
  have hfun :
      (fun seeds : Fin (responseCount P) → Seed =>
        actualInitialMemoryError P I.oracle seeds t) =
      (fun seeds => actualInitialMemorySampleError P I.oracle seeds t) := by
    funext seeds
    exact Admissible.paperSchedule_actualInitialMemoryError_eq_sampleError I
      ε Ctail ch κ Cb CI hε hch hκ hκle hCb hCI seeds t ht
  rw [hfun]
  exact actualInitialMemorySampleError_seed_memLp_two P I.oracle t

/-- With a legal initialization constant of at least 4096, the genuine
expected average norm of the canonical initial term costs at most ε/32.
The bound includes the absent-initialization branch. -/
theorem Admissible.paperSchedule_actualInitialMemoryError_average_norm_le
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {p q Δ σ Lbar : ℝ} (I : Admissible d Seed p q Δ σ Lbar)
    (ε Ctail ch κ Cb CI : ℝ)
    (hε : 0 < ε) (hch : 0 < ch)
    (hκ : 0 < κ) (hκle : κ ≤ 1)
    (hCb : 0 < Cb) (hCI : 4096 ≤ CI) :
    let P := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb (by linarith)
    (P.T : ENNReal)⁻¹ *
      (∫⁻ seeds : Fin (responseCount P) → Seed,
        ENNReal.ofReal
          (∑ u : Fin P.T,
            ‖actualInitialMemoryError P I.oracle seeds (u.val + 1)‖)
        ∂freshSeedLaw I.oracle (responseCount P)) ≤
      ENNReal.ofReal (ε / 32) := by
  have hCIpos : 0 < CI := by linarith
  let P : Schedule q := paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
    hε hch hCb hCIpos
  dsimp only
  letI : IsProbabilityMeasure (freshSeedLaw I.oracle (responseCount P)) :=
    freshSeedLaw_probability I.oracle (responseCount P)
  let E : Fin P.T → (Fin (responseCount P) → Seed) → Point d :=
    fun u seeds => actualInitialMemoryError P I.oracle seeds (u.val + 1)
  have hE (u : Fin P.T) : MemLp (E u) 2
      (freshSeedLaw I.oracle (responseCount P)) := by
    exact Admissible.paperSchedule_actualInitialMemoryError_seed_memLp_two I
      ε Ctail ch κ Cb CI hε hch hκ hκle hCb hCIpos
      (u.val + 1) (Nat.zero_lt_succ _)
  have hL2 := Admissible.paperSchedule_actualInitialMemoryError_average_seed_le I
    ε Ctail ch κ Cb CI hε hch hκ hκle hCb hCIpos
  have hT : (0 : ℝ) < P.T := Nat.cast_pos.mpr P.T_pos
  have hsecond :
      (∑ u : Fin P.T,
        ∫ seeds : Fin (responseCount P) → Seed,
          ‖E u seeds‖ ^ 2 ∂freshSeedLaw I.oracle (responseCount P)) /
        (P.T : ℝ) ≤ (ε / 32) ^ 2 := by
    have hconv :
        (∑ u : Fin P.T,
          ∫ seeds : Fin (responseCount P) → Seed,
            ‖E u seeds‖ ^ 2 ∂freshSeedLaw I.oracle (responseCount P)) /
          (P.T : ℝ) =
        (P.T : ℝ)⁻¹ *
          ∑ u : Fin P.T,
            ∫ seeds : Fin (responseCount P) → Seed,
              ‖E u seeds‖ ^ 2 ∂freshSeedLaw I.oracle (responseCount P) := by
      rw [div_eq_mul_inv, mul_comm]
    rw [hconv]
    calc
      _ ≤ 4 * ε ^ 2 / CI := hL2
      _ ≤ (ε / 32) ^ 2 := by
        have hεsq : 0 ≤ ε ^ 2 := sq_nonneg ε
        have hscale := mul_nonneg hεsq (sub_nonneg.mpr hCI)
        apply (div_le_iff₀ hCIpos).2
        nlinarith [hscale]
  have hnorm := finite_average_l2_to_l1
    (freshSeedLaw I.oracle (responseCount P)) P.T_pos E hE
    (a := ε / 32) (by positivity) hsecond
  simpa only [E] using hnorm

end

end HeavyTailedNoise.UpperK1
