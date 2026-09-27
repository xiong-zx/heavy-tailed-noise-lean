import HeavyTailedNoise.Probability.GaussianSeedRecursion

/-!
Joint measurability of a full-history Gaussian state recursion in an
unobserved parameter and its independent finite seed tape. The parameter may
be a candidate next Haar direction; it is never passed to the algorithm.
-/

namespace HeavyTailedNoise

noncomputable section

theorem measurable_joint_gaussianSeedState
    {Θ H : Type*} [MeasurableSpace Θ] [MeasurableSpace H]
    (d : ℕ) (h₀ : H)
    (m : Θ → ℕ → H → Point d)
    (hm : ∀ t, Measurable (fun z : Θ × H => m z.1 t z.2))
    (a : ℝ) (update : ℕ → H × Point d → H)
    (hUpdate : ∀ t, Measurable (update t)) :
    ∀ n, Measurable (fun z : Θ × (Fin n → Point d) =>
      gaussianSeedState d h₀ (m z.1) a update n z.2) := by
  intro n
  induction n with
  | zero =>
      exact measurable_const
  | succ n ih =>
      have hprefix : Measurable (fun z : Θ × (Fin (n + 1) → Point d) =>
          (z.1, fun i : Fin n => z.2 i.castSucc)) := by
        apply measurable_fst.prodMk
        apply measurable_pi_iff.mpr
        intro i
        exact (measurable_pi_apply i.castSucc).comp measurable_snd
      have hstate : Measurable (fun z : Θ × (Fin (n + 1) → Point d) =>
          gaussianSeedState d h₀ (m z.1) a update n
            (fun i => z.2 i.castSucc)) := ih.comp hprefix
      have hmean : Measurable (fun z : Θ × (Fin (n + 1) → Point d) =>
          m z.1 n
            (gaussianSeedState d h₀ (m z.1) a update n
              (fun i => z.2 i.castSucc))) :=
        (hm n).comp (measurable_fst.prodMk hstate)
      have hnoise : Measurable (fun z : Θ × (Fin (n + 1) → Point d) =>
          a • z.2 (Fin.last n)) := by fun_prop
      have hresponse : Measurable (fun z : Θ × (Fin (n + 1) → Point d) =>
          m z.1 n
            (gaussianSeedState d h₀ (m z.1) a update n
              (fun i => z.2 i.castSucc)) +
            a • z.2 (Fin.last n)) := hmean.add hnoise
      have hpair := hstate.prodMk hresponse
      simpa only [gaussianSeedState, Function.comp_def] using
        (hUpdate n).comp hpair

end

end HeavyTailedNoise
