import HeavyTailedNoise.Probability.GaussianKernelSeedRepresentation
import HeavyTailedNoise.Probability.GaussianSeedSplit

/-!
The explicit measurable full-history state recursion driven by exactly one
fresh standard Gaussian seed per response slot. Its law will be identified
with `adaptiveGaussianLaw` using the checked one-step and tape-split lemmas.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

def gaussianSeedState
    {H : Type*} [MeasurableSpace H]
    (d : ℕ) (h₀ : H) (m : ℕ → H → Point d) (a : ℝ)
    (update : ℕ → H × Point d → H) :
    (n : ℕ) → (Fin n → Point d) → H
  | 0, _ => h₀
  | n + 1, ξ =>
      let h := gaussianSeedState d h₀ m a update n
        (fun i => ξ i.castSucc)
      update n (h, m n h + a • ξ (Fin.last n))

lemma gaussianSeedState_succ
    {H : Type*} [MeasurableSpace H]
    (d : ℕ) (h₀ : H) (m : ℕ → H → Point d) (a : ℝ)
    (update : ℕ → H × Point d → H)
    (n : ℕ) (ξ : Fin (n + 1) → Point d) :
    gaussianSeedState d h₀ m a update (n + 1) ξ =
      update n
        (gaussianSeedState d h₀ m a update n
          (fun i => ξ i.castSucc),
         m n (gaussianSeedState d h₀ m a update n
          (fun i => ξ i.castSucc)) + a • ξ (Fin.last n)) := rfl

theorem measurable_gaussianSeedState
    {H : Type*} [MeasurableSpace H]
    (d : ℕ) (h₀ : H) (m : ℕ → H → Point d)
    (hm : ∀ t, Measurable (m t)) (a : ℝ)
    (update : ℕ → H × Point d → H)
    (hUpdate : ∀ t, Measurable (update t)) :
    ∀ n, Measurable (gaussianSeedState d h₀ m a update n) := by
  intro n
  induction n with
  | zero =>
      exact measurable_const
  | succ n ih =>
      have hprefix : Measurable
          (fun ξ : Fin (n + 1) → Point d =>
            fun i : Fin n => ξ i.castSucc) := by
        apply measurable_pi_iff.mpr
        intro i
        exact measurable_pi_apply i.castSucc
      have hstate : Measurable
          (fun ξ : Fin (n + 1) → Point d =>
            gaussianSeedState d h₀ m a update n
              (fun i => ξ i.castSucc)) := ih.comp hprefix
      have hmean : Measurable
          (fun ξ : Fin (n + 1) → Point d =>
            m n (gaussianSeedState d h₀ m a update n
              (fun i => ξ i.castSucc))) := (hm n).comp hstate
      have hnoise : Measurable
          (fun ξ : Fin (n + 1) → Point d =>
            a • ξ (Fin.last n)) := by fun_prop
      have hresponse : Measurable
          (fun ξ : Fin (n + 1) → Point d =>
            m n (gaussianSeedState d h₀ m a update n
              (fun i => ξ i.castSucc)) + a • ξ (Fin.last n)) :=
        hmean.add hnoise
      have hpair := hstate.prodMk hresponse
      simpa only [gaussianSeedState, Function.comp_def] using
        (hUpdate n).comp hpair

theorem gaussianSeedState_zero_law
    {H : Type*} [MeasurableSpace H]
    (d : ℕ) (h₀ : H) (m : ℕ → H → Point d) (a : ℝ)
    (update : ℕ → H × Point d → H) :
    (Measure.pi (fun _ : Fin 0 => standardGaussianLaw d)).map
      (gaussianSeedState d h₀ m a update 0) = Measure.dirac h₀ := by
  simp [gaussianSeedState, Measure.map_const]

end

end HeavyTailedNoise
