import HeavyTailedNoise.Lower.Gated.IdealNoiseAdapted

/-!
At a fixed possible stage-start time, replace every later Gaussian seed by a
public zero. The start event and its pre-response record are unchanged.
-/

namespace HeavyTailedNoise

noncomputable section

def idealNoiseTruncate {d N : ℕ} (t : ℕ)
    (ξ : Fin N → Point d) : Fin N → Point d :=
  fun i => if i.val < t then ξ i else 0

lemma measurable_idealNoiseTruncate {d N : ℕ} (t : ℕ) :
    Measurable (idealNoiseTruncate (d := d) (N := N) t) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i.val < t
  · simpa [idealNoiseTruncate, hi] using
      (measurable_pi_apply i :
        Measurable (fun ξ : Fin N → Point d => ξ i))
  · simp [idealNoiseTruncate, hi]

lemma idealNoiseTruncate_eq_of_lt {d N t : ℕ}
    (ξ : Fin N → Point d) (i : Fin N) (hi : i.val < t) :
    idealNoiseTruncate t ξ i = ξ i := by
  simp [idealNoiseTruncate, hi]

/-- The event that stage `j` starts at the response-bearing or response-free
decision `t` depends only on noise strictly before `t`. -/
theorem idealStageStart_eq_iff_truncate {d T N t : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (j : ℕ) (htN : t ≤ N) :
    idealStageStart hT U A r ξ a j = t ↔
      idealStageStart hT U A r (idealNoiseTruncate t ξ) a j = t := by
  have hpre : ∀ i : Fin N, i.val < t →
      ξ i = idealNoiseTruncate t ξ i := by
    intro i hi
    exact (idealNoiseTruncate_eq_of_lt ξ i hi).symm
  constructor
  · intro h
    exact idealStageStart_eq_of_noise_agree_at
      hT U A r a j htN hpre h
  · intro h
    exact idealStageStart_eq_of_noise_agree_at
      hT U A r a j htN (fun i hi => (hpre i hi).symm) h

/-- On the start event, the complete stopped snapshot is also a function of
the strictly earlier noise coordinates. -/
theorem idealStoppedPreHistory_eq_truncate_on_start {d T N t : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) (htN : t ≤ N)
    (hstart : idealStageStart hT U A r ξ a (k.val + 1) = t) :
    idealStoppedPreHistory hT U k A r ξ a =
      idealStoppedPreHistory hT U k A r
        (idealNoiseTruncate t ξ) a := by
  apply idealStoppedPreHistory_eq_of_noise_agree_at
    hT U k A r a htN _ hstart
  intro i hi
  exact (idealNoiseTruncate_eq_of_lt ξ i hi).symm

end

end HeavyTailedNoise
