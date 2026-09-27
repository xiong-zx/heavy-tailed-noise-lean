import HeavyTailedNoise.Lower.Gated.PrefixContrast
import HeavyTailedNoise.Probability.HaarConditionalFrame

/-!
The checked 300-gradient contrast requires only an orthonormal revealed
prefix. In dimension `T ≤ d`, any such prefix can be completed to a full
orthonormal frame; exact prefix locality then transfers the existing bound.
The completion is a proof witness, never an algorithm observation.
-/

namespace HeavyTailedNoise

noncomputable section

theorem exists_orthonormalFrame_agree_prefix
    {d T : ℕ} (hTd : T ≤ d) (U : Fin T → Point d) (j : Fin T)
    (hpre : Orthonormal ℝ
      (framePrefix (Nat.succ_le_iff.mpr j.isLt) U)) :
    ∃ W : Fin T → Point d,
      Orthonormal ℝ W ∧ ∀ i : Fin T, i ≤ j → W i = U i := by
  let hj : j.val + 1 ≤ T := Nat.succ_le_iff.mpr j.isLt
  let v : Fin (j.val + 1) → Point d := framePrefix hj U
  let s : Set (Fin d) := {i | i.val < j.val + 1}
  let vFull : Fin d → Point d :=
    fun i => if h : i.val < j.val + 1 then v ⟨i.val, h⟩ else 0
  let f : s → Fin (j.val + 1) := fun i => ⟨i.1.val, i.2⟩
  have hf : Function.Injective f := by
    intro i k heq
    have hv : i.1.val = k.1.val := by
      simpa [f] using congrArg Fin.val heq
    exact Subtype.ext (Fin.ext hv)
  have hdom : s.domRestrict vFull = v ∘ f := by
    funext i
    have hi : i.1.val < j.val + 1 := i.2
    change vFull i.1 = v (f i)
    change (if h : i.1.val < j.val + 1 then v ⟨i.1.val, h⟩ else 0) =
      v (f i)
    rw [dif_pos hi]
  have hvDom : Orthonormal ℝ (s.domRestrict vFull) := by
    rw [hdom]
    exact hpre.comp f hf
  have hdim : Module.finrank ℝ (Point d) = Fintype.card (Fin d) := by
    simp [Point]
  obtain ⟨b, hb⟩ :=
    hvDom.exists_orthonormalBasis_extension_of_card_eq hdim
  let W : Fin T → Point d := fun i => b (i.castLE hTd)
  have hW : Orthonormal ℝ W :=
    b.orthonormal.comp (Fin.castLE hTd) (Fin.castLE_injective hTd)
  refine ⟨W, hW, ?_⟩
  intro i hi
  have hlt : i.val < j.val + 1 := by omega
  have hmem : (i.castLE hTd) ∈ s := hlt
  change b (i.castLE hTd) = U i
  rw [hb _ hmem]
  have hltCast : (i.castLE hTd).val < j.val + 1 := by simpa using hlt
  change (if h : (i.castLE hTd).val < j.val + 1 then
      v ⟨(i.castLE hTd).val, h⟩ else 0) = U i
  rw [dif_pos hltCast]
  rfl

theorem norm_gradient_prefixHardPotential_sub_le_300_of_prefix
    {d T : ℕ} (hTd : T ≤ d)
    {U V : Fin T → Point d} (j : Fin T)
    (hU : Orthonormal ℝ
      (framePrefix (Nat.succ_le_iff.mpr j.isLt) U))
    (hV : Orthonormal ℝ
      (framePrefix (Nat.succ_le_iff.mpr j.isLt) V))
    (hagree : ∀ i : Fin T, i < j → U i = V i)
    (x : Point d) :
    ‖gradient (prefixHardPotential U j) x -
      gradient (prefixHardPotential V j) x‖ ≤ 300 := by
  obtain ⟨U', hU', hEqU⟩ :=
    exists_orthonormalFrame_agree_prefix hTd U j hU
  obtain ⟨V', hV', hEqV⟩ :=
    exists_orthonormalFrame_agree_prefix hTd V j hV
  have hpotU : prefixHardPotential U j = prefixHardPotential U' j :=
    prefixHardPotential_eq_of_agree j
      (fun i hi => (hEqU i hi).symm)
  have hpotV : prefixHardPotential V j = prefixHardPotential V' j :=
    prefixHardPotential_eq_of_agree j
      (fun i hi => (hEqV i hi).symm)
  rw [hpotU, hpotV]
  apply norm_gradient_prefixHardPotential_sub_le_300 hU' hV' j
  intro i hi
  rw [hEqU i (le_of_lt hi), hEqV i (le_of_lt hi)]
  exact hagree i hi

end

end HeavyTailedNoise
