import HeavyTailedNoise.Lower.Gated.JointPrefixGradientMeas

/-!
Keep the stopped frozen mean in its lightweight prefix-gradient form while
proving history composition measurability. The recursive mean is identified
pointwise afterward, avoiding an expensive definition expansion.
-/

namespace HeavyTailedNoise

noncomputable section

theorem measurable_frozenPrefixMean_comp
    {H : Type*} [MeasurableSpace H] {d T : ℕ}
    (hT : 0 < T) (j : Fin T)
    (frame : H → Fin T → Point d) (hframe : Measurable frame)
    (q : H → Point d) (hq : Measurable q) :
    Measurable (fun h : H =>
      gradient (prefixHardPotential (frame h) j) (q h)) := by
  let f : ((Fin T → Point d) × Point d) → Point d :=
    fun z => gradient (prefixHardPotential z.1 j) z.2
  let g : H → (Fin T → Point d) × Point d := fun h => (frame h, q h)
  have hf : Measurable f := measurable_joint_prefixGradient hT j
  have hg : Measurable g := hframe.prodMk hq
  have hfg : Measurable (f ∘ g) := hf.comp hg
  change Measurable (f ∘ g)
  exact hfg

theorem frozenPrefixMean_eq_idealResponseMean
    {d T : ℕ} (hT : 0 < T) (j : Fin T)
    (U : Fin T → Point d) (x : Point d) :
    gradient (prefixHardPotential U j) x =
      idealResponseMean hT U j.val x := by
  have hj : idealPrefixIndex hT j.val = j := by
    apply Fin.ext
    simp [idealPrefixIndex]
    omega
  change gradient (prefixHardPotential U j) x =
    gradient (prefixHardPotential U (idealPrefixIndex hT j.val)) x
  rw [hj]

end

end HeavyTailedNoise
