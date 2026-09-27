import HeavyTailedNoise.Lower.Gated.IdealNoiseTruncation
import HeavyTailedNoise.Probability.GaussianOracle

/-!
Fixed-time Gaussian product splitting. At any deterministic time, the public-
zero truncation of the tape is independent of every remaining Gaussian seed.
Random stage starts will be handled by finite event decomposition, not by
assuming this fixed-time fact automatically extends to a stopping time.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

def idealNoisePrefixIndices (N t : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i.val < t)

def idealNoiseSuffixIndices (N t : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => t ≤ i.val)

lemma idealNoisePrefixSuffix_disjoint (N t : ℕ) :
    Disjoint (idealNoisePrefixIndices N t)
      (idealNoiseSuffixIndices N t) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp [idealNoisePrefixIndices] at hi
  simp [idealNoiseSuffixIndices] at hj
  omega

def idealNoiseFill {d N : ℕ} (S : Finset (Fin N))
    (p : S → Point d) : Fin N → Point d :=
  fun i => if h : i ∈ S then p ⟨i, h⟩ else 0

lemma measurable_idealNoiseFill {d N : ℕ} (S : Finset (Fin N)) :
    Measurable (idealNoiseFill (d := d) S) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i ∈ S
  · simpa [idealNoiseFill, hi] using
      (measurable_pi_apply (⟨i, hi⟩ : S) :
        Measurable (fun p : S → Point d => p ⟨i, hi⟩))
  · simp [idealNoiseFill, hi]

theorem idealNoiseTruncate_indep_suffix {d N : ℕ} (t : ℕ) :
    IndepFun
      (idealNoiseTruncate (d := d) (N := N) t)
      (fun ξ : Fin N → Point d =>
        fun i : idealNoiseSuffixIndices N t => ξ i.1)
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d)) := by
  let S := idealNoisePrefixIndices N t
  let T := idealNoiseSuffixIndices N t
  have hcoord : iIndepFun
      (fun i (ξ : Fin N → Point d) => ξ i)
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d)) :=
    iIndepFun_pi (X := fun _ : Fin N => id)
      (fun _ => aemeasurable_id)
  have hbase : IndepFun
      (fun ξ : Fin N → Point d => fun i : S => ξ i.1)
      (fun ξ : Fin N → Point d => fun i : T => ξ i.1)
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d)) :=
    hcoord.indepFun_finset S T
      (idealNoisePrefixSuffix_disjoint N t)
      (fun i => measurable_pi_apply i)
  have hfill := hbase.comp (measurable_idealNoiseFill S) measurable_id
  have heq :
      (idealNoiseFill S ∘
        (fun ξ : Fin N → Point d => fun i : S => ξ i.1)) =
      idealNoiseTruncate t := by
    funext ξ i
    by_cases hi : i.val < t
    · have hmem : i ∈ S := by simp [S, idealNoisePrefixIndices, hi]
      simp [idealNoiseFill, idealNoiseTruncate, hi, hmem]
    · have hmem : i ∉ S := by simp [S, idealNoisePrefixIndices, hi]
      simp [idealNoiseFill, idealNoiseTruncate, hi, hmem]
  simpa only [heq, Function.comp_def, id_eq] using hfill

end

end HeavyTailedNoise
