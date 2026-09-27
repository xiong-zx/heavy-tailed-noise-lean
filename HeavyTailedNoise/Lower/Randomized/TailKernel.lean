import HeavyTailedNoise.Lower.Randomized.HaarGeometry

/-!
The entire remaining-frame kernel after a prefix, made from the same
projected-Gaussian transitions as the actual preselected prior. No oracle,
algorithm, or query-dependent replacement prior is introduced here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

namespace HeavyTailedNoise.RandomizedLift

/-- Start with the given prefix and append k actual next-direction draws. -/
def frameCompletionKernel (d j : ℕ) :
    (k : ℕ) → Kernel (Fin j → Point d) (Fin (j + k) → Point d)
  | 0 => Kernel.id
  | k + 1 =>
      (((Kernel.id : Kernel (Fin (j + k) → Point d) (Fin (j + k) → Point d)) ×ₖ
        frameNextKernel d (j + k)) ∘ₖ frameCompletionKernel d j k).map
          (fun p => Fin.snoc (α := fun _ : Fin (j + k + 1) => Point d) p.1 p.2)

instance frameCompletionKernel_markov (d j k : ℕ) :
    IsMarkovKernel (frameCompletionKernel d j k) := by
  induction k with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (Fin j → Point d) _); infer_instance
  | succ k ih =>
      letI : IsMarkovKernel (frameCompletionKernel d j k) := ih
      change IsMarkovKernel
        ((((Kernel.id : Kernel (Fin (j + k) → Point d) (Fin (j + k) → Point d)) ×ₖ
          frameNextKernel d (j + k)) ∘ₖ frameCompletionKernel d j k).map
            (fun p => Fin.snoc (α := fun _ : Fin (j + k + 1) => Point d) p.1 p.2))
      exact Kernel.IsMarkovKernel.map _ (measurable_frameSnoc d (j + k))

theorem frameCompletionKernel_zero_apply (d j : ℕ) (v : Fin j → Point d) :
    frameCompletionKernel d j 0 v = Measure.dirac v := by
  simp [frameCompletionKernel, Kernel.id_apply]

theorem frameCompletionKernel_succ_apply (d j k : ℕ) (v : Fin j → Point d) :
    frameCompletionKernel d j (k + 1) v =
      ((frameCompletionKernel d j k v) ⊗ₘ frameNextKernel d (j + k)).map
        (fun p => Fin.snoc (α := fun _ : Fin (j + k + 1) => Point d) p.1 p.2) := by
  rw [frameCompletionKernel, Kernel.map_apply _ (measurable_frameSnoc d (j + k))]
  change (((Kernel.id : Kernel (Fin (j + k) → Point d) _) ×ₖ
    frameNextKernel d (j + k)) ∘ₘ (frameCompletionKernel d j k v)).map _ = _
  rw [← Measure.compProd_eq_comp_prod]

/-- Covariance of every remaining column jointly, conditional on a given
prefix. Fixed-prefix stabilizer invariance is its immediate corollary. -/
theorem frameCompletionKernel_frameAction (d j k : ℕ)
    (W : Point d ≃ₗᵢ[ℝ] Point d) (v : Fin j → Point d) :
    frameCompletionKernel d j k (frameAction W v) =
      (frameCompletionKernel d j k v).map (frameAction W) := by
  induction k with
  | zero =>
      rw [frameCompletionKernel_zero_apply, frameCompletionKernel_zero_apply,
        Measure.map_dirac' (measurable_frameAction W)]
  | succ k ih =>
      rw [frameCompletionKernel_succ_apply, frameCompletionKernel_succ_apply, ih,
        ← frameStep_frameAction W (frameCompletionKernel d j k v)]
      have hF : Measurable
          (fun p : (Fin (j + k) → Point d) × Point d =>
            (frameAction W p.1, W p.2)) :=
        ((measurable_frameAction W).comp measurable_fst).prodMk
          (W.continuous.measurable.comp measurable_snd)
      rw [Measure.map_map (measurable_frameSnoc d (j + k)) hF,
        Measure.map_map (measurable_frameAction W) (measurable_frameSnoc d (j + k))]
      congr 1
      funext p i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
      · simp [frameAction, Function.comp_def]
      · simp [frameAction, Function.comp_def]

theorem frameCompletionKernel_stabilizer_invariant (d j k : ℕ)
    (W : Point d ≃ₗᵢ[ℝ] Point d) (v : Fin j → Point d)
    (hfix : ∀ i, W (v i) = v i) :
    (frameCompletionKernel d j k v).map (frameAction W) =
      frameCompletionKernel d j k v := by
  rw [← frameCompletionKernel_frameAction]
  congr 1
  funext i
  exact hfix i

/-- Matching the fixed prior is proved, rather than an application premise. -/
theorem frameCompletionKernel_comp_prior (d j k : ℕ) :
    frameCompletionKernel d j k ∘ₘ preselectedProjectedGaussianLaw d j =
      preselectedProjectedGaussianLaw d (j + k) := by
  letI := preselectedProjectedGaussianLaw_probability d j
  induction k with
  | zero => simp [frameCompletionKernel]
  | succ k ih =>
      letI := preselectedProjectedGaussianLaw_probability d (j + k)
      rw [frameCompletionKernel, ← Measure.map_comp _ _ (measurable_frameSnoc d (j + k)),
        ← Measure.comp_assoc, ih, ← Measure.compProd_eq_comp_prod]
      rfl

private theorem completionPrefix_snoc {d j k : ℕ}
    (w : Fin (j + k) → Point d) (u : Point d) :
    framePrefix (Nat.le_add_right j (k + 1)) (Fin.snoc w u) =
      framePrefix (Nat.le_add_right j k) w := by
  funext i
  unfold framePrefix
  have hi : i.castLE (Nat.le_add_right j (k + 1)) =
      (i.castLE (Nat.le_add_right j k)).castSucc := by
    apply Fin.ext
    rfl
  rw [hi, Fin.snoc_castSucc]

/-- The completion preserves its starting prefix almost surely, including
on invalid prefixes where the totalized transition may return zero. -/
theorem frameCompletionKernel_prefix_ae (d j k : ℕ) (v : Fin j → Point d) :
    ∀ᵐ u ∂frameCompletionKernel d j k v,
      framePrefix (Nat.le_add_right j k) u = v := by
  induction k with
  | zero =>
      rw [frameCompletionKernel_zero_apply]
      apply (ae_dirac_iff
        (measurableSet_eq_fun
          (measurable_framePrefix (Nat.le_add_right j 0)) measurable_const)).2
      funext i
      rfl
  | succ k ih =>
      rw [frameCompletionKernel_succ_apply]
      apply (ae_map_iff (measurable_frameSnoc d (j + k)).aemeasurable
        (measurableSet_eq_fun
          (measurable_framePrefix (Nat.le_add_right j (k + 1))) measurable_const)).2
      have hold := Measure.ae_compProd_of_ae_fst (frameNextKernel d (j + k))
        (measurableSet_eq_fun
          (measurable_framePrefix (Nat.le_add_right j k)) measurable_const) ih
      filter_upwards [hold] with p hp
      rw [completionPrefix_snoc]
      exact hp

/-- At every valid prefix the completion is supported on actual
orthonormal frames; the statement concerns all remaining columns jointly. -/
theorem frameCompletionKernel_orthonormal_ae (d j k : ℕ)
    (v : Fin j → Point d) (hv : Orthonormal ℝ v) (hT : j + k ≤ d) :
    ∀ᵐ u ∂frameCompletionKernel d j k v, Orthonormal ℝ u := by
  induction k with
  | zero =>
      rw [frameCompletionKernel_zero_apply]
      exact (ae_dirac_iff (measurableSet_orthonormal_fin d j)).2 hv
  | succ k ih =>
      have hprev : j + k ≤ d := by omega
      have hj : j + k < d := by omega
      have hold := ih hprev
      rw [frameCompletionKernel_succ_apply]
      apply (ae_map_iff (measurable_frameSnoc d (j + k)).aemeasurable
        (measurableSet_orthonormal_fin d (j + k + 1))).2
      apply Measure.ae_compProd_of_ae_ae
        ((measurable_frameSnoc d (j + k))
          (measurableSet_orthonormal_fin d (j + k + 1)))
      filter_upwards [hold] with w hw
      rw [frameNextKernel_apply]
      have hsnoc : Measurable (fun y : Point d =>
          Fin.snoc (α := fun _ : Fin (j + k + 1) => Point d) w y) := by
        simpa [Function.comp_def] using
          (measurable_frameSnoc d (j + k)).comp
            (measurable_const.prodMk measurable_id : Measurable (fun y : Point d => (w, y)))
      apply (ae_map_iff (measurable_frameNextDirection_fixed w).aemeasurable
        (hsnoc (measurableSet_orthonormal_fin d (j + k + 1)))).2
      filter_upwards [frameResidual_ne_zero_ae hj w hw] with z hz
      exact frameSnoc_orthonormal_of_residual_ne_zero w hw z hz

/-- The full prefix/frame joint decomposition under the actual fixed prior.
This identifies the entire remaining-frame kernel, not merely the next
column, and leaves no law-matching premise for the application. -/
theorem preselectedProjectedGaussianLaw_completion_joint (d j k : ℕ) :
    (preselectedProjectedGaussianLaw d (j + k)).map
      (fun u => (framePrefix (Nat.le_add_right j k) u, u)) =
      (preselectedProjectedGaussianLaw d j) ⊗ₘ frameCompletionKernel d j k := by
  let q := preselectedProjectedGaussianLaw d j
  let κ := frameCompletionKernel d j k
  letI := preselectedProjectedGaussianLaw_probability d j
  have hpair : Measurable
      (fun u : Fin (j + k) → Point d =>
        (framePrefix (Nat.le_add_right j k) u, u)) :=
    (measurable_framePrefix (Nat.le_add_right j k)).prodMk measurable_id
  have hmarg : (q ⊗ₘ κ).map Prod.snd =
      preselectedProjectedGaussianLaw d (j + k) := by
    change (q ⊗ₘ κ).snd = _
    rw [Measure.snd_compProd]
    exact frameCompletionKernel_comp_prior d j k
  have hprefix : ∀ᵐ p ∂q ⊗ₘ κ,
      framePrefix (Nat.le_add_right j k) p.2 = p.1 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun
        ((measurable_framePrefix (Nat.le_add_right j k)).comp measurable_snd)
        measurable_fst)
    exact Filter.Eventually.of_forall (frameCompletionKernel_prefix_ae d j k)
  calc
    _ = ((q ⊗ₘ κ).map Prod.snd).map
        (fun u => (framePrefix (Nat.le_add_right j k) u, u)) := by rw [hmarg]
    _ = (q ⊗ₘ κ).map
        (fun p => (framePrefix (Nat.le_add_right j k) p.2, p.2)) := by
          rw [Measure.map_map hpair measurable_snd]
          rfl
    _ = (q ⊗ₘ κ).map id := by
          apply Measure.map_congr
          filter_upwards [hprefix] with p hp
          simp [hp]
    _ = _ := Measure.map_id

theorem preselectedProjectedGaussianLaw_completion_hasCondDistrib (d j k : ℕ) :
    HasCondDistrib (id : (Fin (j + k) → Point d) → _)
      (framePrefix (Nat.le_add_right j k)) (frameCompletionKernel d j k)
      (preselectedProjectedGaussianLaw d (j + k)) := by
  refine ⟨((measurable_framePrefix (Nat.le_add_right j k)).prodMk
    measurable_id).aemeasurable, ?_⟩
  change (preselectedProjectedGaussianLaw d (j + k)).map
      (fun u => (framePrefix (Nat.le_add_right j k) u, u)) = _
  rw [preselectedProjectedGaussianLaw_prefix d j (j + k) (Nat.le_add_right j k)]
  exact preselectedProjectedGaussianLaw_completion_joint d j k

/-- The same entire-frame conditional kernel under the actual repaired
orthonormal-frame prior. Null-set repair does not change its joint law. -/
theorem preselectedOrthonormalFrameLaw_completion_hasCondDistrib
    (d j k : ℕ) (hT : j + k ≤ d) :
    HasCondDistrib
      (Subtype.val : {u : Fin (j + k) → Point d // Orthonormal ℝ u} → _)
      (fun u : {u : Fin (j + k) → Point d // Orthonormal ℝ u} =>
        framePrefix (Nat.le_add_right j k) u.1)
      (frameCompletionKernel d j k)
      (preselectedOrthonormalFrameLaw d (j + k) hT) := by
  let P := preselectedOrthonormalFrameLaw d (j + k) hT
  let val := (Subtype.val : {u : Fin (j + k) → Point d // Orthonormal ℝ u} → _)
  let pref := framePrefix (d := d) (Nat.le_add_right j k)
  have hprefix : Measurable pref := measurable_framePrefix _
  have hval : Measurable val := measurable_subtype_coe
  have hpair : Measurable (fun u : Fin (j + k) → Point d => (pref u, u)) :=
    hprefix.prodMk measurable_id
  have hmap : P.map val = preselectedProjectedGaussianLaw d (j + k) :=
    preselectedOrthonormalFrameLaw_map_val d (j + k) hT
  have hmargin : P.map (pref ∘ val) = preselectedProjectedGaussianLaw d j := by
    rw [← Measure.map_map hprefix hval, hmap]
    exact preselectedProjectedGaussianLaw_prefix d j (j + k) _
  refine ⟨((hprefix.comp hval).prodMk hval).aemeasurable, ?_⟩
  change P.map (fun u => (pref (val u), val u)) =
    (P.map (pref ∘ val)) ⊗ₘ frameCompletionKernel d j k
  rw [hmargin]
  calc
    _ = (P.map val).map (fun u => (pref u, u)) := by
      rw [Measure.map_map hpair hval]
      rfl
    _ = _ := by
      rw [hmap]
      exact preselectedProjectedGaussianLaw_completion_joint d j k

end HeavyTailedNoise.RandomizedLift
