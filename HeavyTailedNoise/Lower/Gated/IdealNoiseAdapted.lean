import HeavyTailedNoise.Lower.Gated.IdealStoppedHistory

/-!
Pathwise nonanticipation of the ideal process in its Gaussian noise tape.
These facts are the deterministic input for a finite-horizon proof of fresh
noise after the random stage-start time.
-/

namespace HeavyTailedNoise

noncomputable section

lemma idealNoiseAt_eq_of_agree {d N n t : ℕ}
    {ξ ζ : Fin N → Point d}
    (h : ∀ i : Fin N, i.val < n → ξ i = ζ i)
    (htn : t < n) : idealNoiseAt ξ t = idealNoiseAt ζ t := by
  by_cases ht : t < N
  · simpa [idealNoiseAt, ht] using h ⟨t, ht⟩ htn
  · simp [idealNoiseAt, ht]

theorem idealStateAt_eq_of_noise_agree {d T N n : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    {ξ ζ : Fin N → Point d} (a : ℝ)
    (h : ∀ i : Fin N, i.val < n → ξ i = ζ i) :
    idealStateAt hT U A r ξ a n = idealStateAt hT U A r ζ a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprev : ∀ i : Fin N, i.val < n → ξ i = ζ i :=
        fun i hi => h i (by omega)
      have hs := ih hprev
      have hn : idealNoiseAt ξ n = idealNoiseAt ζ n :=
        idealNoiseAt_eq_of_agree h (by omega)
      change idealStepState hT U A r ξ a
          (idealStateAt hT U A r ξ a n) =
        idealStepState hT U A r ζ a
          (idealStateAt hT U A r ζ a n)
      rw [hs]
      simp [idealStepState, hn]

theorem idealDecisionAt_eq_of_noise_agree {d T N t : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    {ξ ζ : Fin N → Point d} (a : ℝ) (htN : t ≤ N)
    (h : ∀ i : Fin N, i.val < t → ξ i = ζ i) :
    idealDecisionAt hT U A r ξ a t =
      idealDecisionAt hT U A r ζ a t := by
  have hs := idealStateAt_eq_of_noise_agree hT U A r a h
  by_cases ht : t < N
  · simp [idealDecisionAt, ht, hs]
  · have heq : t = N := by omega
    subst t
    simp [idealDecisionAt, hs]

theorem idealAfterAt_eq_of_noise_agree {d T N t : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    {ξ ζ : Fin N → Point d} (a : ℝ) (htN : t ≤ N)
    (h : ∀ i : Fin N, i.val < t → ξ i = ζ i) :
    idealAfterAt hT U A r ξ a t =
      idealAfterAt hT U A r ζ a t := by
  have hs := idealStateAt_eq_of_noise_agree hT U A r a h
  have hq := idealDecisionAt_eq_of_noise_agree hT U A r a htN h
  simp [idealAfterAt, hs, hq]

theorem idealStageStart_eq_of_noise_agree_at {d T N t : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d)
    (A : RandomAlgorithm d N Private) (r : Private)
    {ξ ζ : Fin N → Point d} (a : ℝ) (j : ℕ)
    (htN : t ≤ N)
    (h : ∀ i : Fin N, i.val < t → ξ i = ζ i)
    (hstart : idealStageStart hT U A r ξ a j = t) :
    idealStageStart hT U A r ζ a j = t := by
  have hhitξ : j ≤ idealAfterAt hT U A r ξ a t := by
    rw [← hstart]
    exact idealStageStart_hit hT U A r ξ a j (by omega)
  have hhitζ : j ≤ idealAfterAt hT U A r ζ a t := by
    rw [← idealAfterAt_eq_of_noise_agree hT U A r a htN h]
    exact hhitξ
  have hexζ : ∃ s : ℕ, s ≤ N ∧
      j ≤ idealAfterAt hT U A r ζ a s := ⟨t, htN, hhitζ⟩
  have hminζ (s : ℕ) (hs : s < t) :
      ¬ (s ≤ N ∧ j ≤ idealAfterAt hT U A r ζ a s) := by
    rintro ⟨hsN, hge⟩
    have hpre : ∀ i : Fin N, i.val < s → ξ i = ζ i :=
      fun i hi => h i (by omega)
    have heq := idealAfterAt_eq_of_noise_agree hT U A r a hsN hpre
    have hbefore := idealStageStart_before hT U A r ξ a j s
      (by omega) hsN
    omega
  unfold idealStageStart
  rw [dif_pos hexζ]
  exact (Nat.find_eq_iff hexζ).2 ⟨⟨htN, hhitζ⟩, hminζ⟩

theorem idealStoppedPreHistory_eq_of_noise_agree_at {d T N t : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    {ξ ζ : Fin N → Point d} (a : ℝ) (htN : t ≤ N)
    (h : ∀ i : Fin N, i.val < t → ξ i = ζ i)
    (hstart : idealStageStart hT U A r ξ a (k.val + 1) = t) :
    idealStoppedPreHistory hT U k A r ξ a =
      idealStoppedPreHistory hT U k A r ζ a := by
  have hstartζ := idealStageStart_eq_of_noise_agree_at
    hT U A r a (k.val + 1) htN h hstart
  have hs := idealStateAt_eq_of_noise_agree hT U A r a h
  have hq := idealDecisionAt_eq_of_noise_agree hT U A r a htN h
  unfold idealStoppedPreHistory
  rw [hstart, hstartζ]
  simp [idealPreHistoryAtTime, htN, hs, hq]

end

end HeavyTailedNoise
