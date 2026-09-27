import HeavyTailedNoise.Probability.GaussianSeedRecursion
import HeavyTailedNoise.Probability.GaussianSeedPushforward
import HeavyTailedNoise.Probability.GaussianKLAdaptive

/-!
The entire fixed-length adaptive Gaussian state law equals the pushforward of
one iid standard-Gaussian seed per response. The state is an arbitrary
measurable type and may contain the full algorithm transcript.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

theorem gaussianSeedState_law_eq_adaptiveGaussianLaw
    {H : Type*} [MeasurableSpace H]
    (d : ℕ) (h₀ : H)
    (m : ℕ → H → Point d) (hm : ∀ t, Measurable (m t))
    (a : ℝ) (update : ℕ → H × Point d → H)
    (hUpdate : ∀ t, Measurable (update t)) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => standardGaussianLaw d)).map
      (gaussianSeedState d h₀ m a update n) =
      adaptiveGaussianLaw d (Measure.dirac h₀)
        (fun t => gaussianMeanKernel d (m t) (hm t) a)
        update n := by
  let κ : ℕ → Kernel H (Point d) :=
    fun t => gaussianMeanKernel d (m t) (hm t) a
  induction n with
  | zero =>
      simpa only [adaptiveGaussianLaw] using
        gaussianSeedState_zero_law d h₀ m a update
  | succ n ih =>
      let πn : Measure (Fin n → Point d) :=
        Measure.pi (fun _ : Fin n => standardGaussianLaw d)
      let πsucc : Measure (Fin (n + 1) → Point d) :=
        Measure.pi (fun _ : Fin (n + 1) => standardGaussianLaw d)
      let ν : Measure (Point d) := standardGaussianLaw d
      let F : (Fin n → Point d) → H :=
        gaussianSeedState d h₀ m a update n
      let split : (Fin (n + 1) → Point d) →
          (Fin n → Point d) × Point d :=
        fun ξ => ((fun i => ξ i.castSucc), ξ (Fin.last n))
      let u : H × Point d → H :=
        fun z => update n (z.1, m n z.1 + a • z.2)
      let G : ((Fin n → Point d) × Point d) → H :=
        fun z => u (F z.1, z.2)
      have hF : Measurable F :=
        measurable_gaussianSeedState d h₀ m hm a update hUpdate n
      have hsplit : Measurable split := by
        have hp : Measurable
            (fun ξ : Fin (n + 1) → Point d =>
              fun i : Fin n => ξ i.castSucc) := by
          apply measurable_pi_iff.mpr
          intro i
          exact measurable_pi_apply i.castSucc
        exact hp.prodMk (measurable_pi_apply (Fin.last n))
      have hu : Measurable u := by
        have hmean : Measurable (fun z : H × Point d => m n z.1) :=
          (hm n).comp measurable_fst
        have hnoise : Measurable
            (fun z : H × Point d => a • z.2) := by fun_prop
        exact (hUpdate n).comp
          (measurable_fst.prodMk (hmean.add hnoise))
      have hG : Measurable G :=
        hu.comp ((hF.comp measurable_fst).prodMk measurable_snd)
      have hmap :
          πsucc.map (gaussianSeedState d h₀ m a update (n + 1)) =
          (πsucc.map split).map G := by
        rw [Measure.map_map hG hsplit]
        congr 1
      have hsplitLaw : πsucc.map split = πn.prod ν :=
        iidSeedLaw_map_prefix_last ν n
      have hpush : (πn.prod ν).map G =
          ((πn.map F).prod ν).map u :=
        map_prod_seed_state πn ν F hF u hu
      have hstep := gaussianMeanKernel_compProd_update_eq_seed_map
        d (πn.map F) (m n) (hm n) a (update n) (hUpdate n)
      calc
        πsucc.map (gaussianSeedState d h₀ m a update (n + 1)) =
            (πsucc.map split).map G := hmap
        _ = (πn.prod ν).map G := by rw [hsplitLaw]
        _ = ((πn.map F).prod ν).map u := hpush
        _ = ((πn.map F ⊗ₘ κ n).map (update n)) := by
          exact hstep.symm
        _ = adaptiveGaussianLaw d (Measure.dirac h₀) κ update (n + 1) := by
          rw [ih]
          rfl

end

end HeavyTailedNoise
