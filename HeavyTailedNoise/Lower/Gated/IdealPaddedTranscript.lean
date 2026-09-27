import HeavyTailedNoise.Lower.Gated.ActualFrozenQueryRule

/-!
Exact interface between the ideal recursion's variable-length full transcript
and the fixed `N`-slot transcript state used by the frozen Gaussian law.
-/

namespace HeavyTailedNoise

noncomputable section

lemma idealPadTranscript_restrict
    {d N n : ℕ} (hn : n ≤ N) (tr : Transcript d n) :
    (fun i : Fin n =>
      idealPadTranscript (N := N) tr ⟨i.val, by omega⟩) = tr := by
  classical
  funext i
  simp [idealPadTranscript, i.isLt]

lemma idealPadTranscript_snoc_eq_update
    {d N n : ℕ} (hn : n < N)
    (tr : Transcript d n) (v : Point d × Point d) :
    idealPadTranscript (N := N) (Fin.snoc tr v) =
      Function.update (idealPadTranscript (N := N) tr)
        (⟨n, hn⟩ : Fin N) v := by
  classical
  funext i
  by_cases hi : i.val = n
  · have heq : i = (⟨n, hn⟩ : Fin N) := Fin.ext hi
    subst i
    simp [idealPadTranscript, Fin.snoc, Function.update]
  · have hne : i ≠ (⟨n, hn⟩ : Fin N) := by
      intro heq
      exact hi (congrArg Fin.val heq)
    by_cases hlt : i.val < n
    · have hlt' : i.val < n + 1 := by omega
      simp [idealPadTranscript, Fin.snoc, Function.update,
        hne, hlt, hlt']
    · have hge : ¬ i.val < n + 1 := by omega
      simp [idealPadTranscript, Function.update, hne, hlt, hge]

end

end HeavyTailedNoise
