import HeavyTailedNoise.Lower.Gated.IdealStoppedNoiseJointLaw

/-!
An auxiliary extended Gaussian tape supplies hidden independent coordinates
after the algorithm's fixed `N` response slots. The algorithm still receives
only its original `N` gradient responses.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

def idealExtendedNoiseTake {d N m : ℕ}
    (ξ : Fin (N + m) → Point d) : Fin N → Point d :=
  fun i => ξ ⟨i.val, by omega⟩

lemma measurable_idealExtendedNoiseTake {d N m : ℕ} :
    Measurable (idealExtendedNoiseTake (d := d) (N := N) (m := m)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply (⟨i.val, by omega⟩ : Fin (N + m))

def idealExtendedNoiseTail {d N m : ℕ} (t : ℕ) (ht : t ≤ N)
    (ξ : Fin (N + m) → Point d) : Fin m → Point d :=
  fun i => ξ ⟨t + i.val, by omega⟩

lemma measurable_idealExtendedNoiseTail {d N m : ℕ}
    (t : ℕ) (ht : t ≤ N) :
    Measurable (idealExtendedNoiseTail (d := d) (m := m) t ht) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply (⟨t + i.val, by omega⟩ : Fin (N + m))

def idealExtendedSuffixBlock {d N m : ℕ} (t : ℕ) (ht : t ≤ N)
    (p : idealNoiseSuffixIndices (N + m) t → Point d) : Fin m → Point d :=
  fun i => p ⟨⟨t + i.val, by omega⟩,
    by simp [idealNoiseSuffixIndices]⟩

lemma measurable_idealExtendedSuffixBlock {d N m : ℕ}
    (t : ℕ) (ht : t ≤ N) :
    Measurable (idealExtendedSuffixBlock (d := d) (m := m) t ht) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply
    (⟨⟨t + i.val, by omega⟩,
      by simp [idealNoiseSuffixIndices]⟩ :
        idealNoiseSuffixIndices (N + m) t)

theorem idealExtendedNoiseTruncate_indep_tail {d N m : ℕ}
    (t : ℕ) (ht : t ≤ N) :
    IndepFun
      (idealNoiseTruncate (d := d) (N := N + m) t)
      (idealExtendedNoiseTail (d := d) (m := m) t ht)
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)) := by
  have hbase := idealNoiseTruncate_indep_suffix
    (d := d) (N := N + m) t
  have hc := hbase.comp measurable_id
    (measurable_idealExtendedSuffixBlock t ht)
  have heq :
      (fun ξ : Fin (N + m) → Point d =>
        idealExtendedSuffixBlock t ht
          (fun i : idealNoiseSuffixIndices (N + m) t => ξ i.1)) =
      idealExtendedNoiseTail t ht := by
    funext ξ i
    rfl
  have hc' : IndepFun
      (fun ξ : Fin (N + m) → Point d => idealNoiseTruncate t ξ)
      (fun ξ : Fin (N + m) → Point d =>
        idealExtendedSuffixBlock t ht
          (fun i : idealNoiseSuffixIndices (N + m) t => ξ i.1))
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)) := by
    simpa only [Function.comp_def, id_eq] using hc
  rw [heq] at hc'
  exact hc'

theorem idealExtendedNoiseTail_law {d N m : ℕ}
    (t : ℕ) (ht : t ≤ N) :
    (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).map
      (idealExtendedNoiseTail (d := d) (m := m) t ht) =
      Measure.pi (fun _ : Fin m => standardGaussianLaw d) := by
  let ν : Measure (Fin (N + m) → Point d) :=
    Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)
  have hind : iIndepFun
      (fun i (ξ : Fin (N + m) → Point d) => ξ i) ν :=
    iIndepFun_pi (X := fun _ : Fin (N + m) => id)
      (fun _ => aemeasurable_id)
  have hinj : Function.Injective (fun i : Fin m =>
      (⟨t + i.val, by omega⟩ : Fin (N + m))) := by
    intro i j hij
    apply Fin.ext
    have hv : t + i.val = t + j.val := congrArg Fin.val hij
    omega
  have hindTail : iIndepFun (fun i : Fin m =>
      fun ξ : Fin (N + m) → Point d => ξ ⟨t + i.val, by omega⟩) ν :=
    hind.precomp (g := fun i : Fin m =>
      (⟨t + i.val, by omega⟩ : Fin (N + m))) hinj
  have hcoord (i : Fin m) :
      HasLaw (fun ξ : Fin (N + m) → Point d =>
        ξ ⟨t + i.val, by omega⟩) (standardGaussianLaw d) ν := by
    exact ⟨(measurable_pi_apply (⟨t + i.val, by omega⟩ :
        Fin (N + m))).aemeasurable,
      (measurePreserving_eval
        (fun _ : Fin (N + m) => standardGaussianLaw d)
          (⟨t + i.val, by omega⟩ : Fin (N + m))).map_eq⟩
  exact (hindTail.hasLaw_pi hcoord).map_eq

lemma idealExtendedNoiseTake_truncate {d N m t : ℕ}
    (ξ : Fin (N + m) → Point d) :
    idealExtendedNoiseTake (idealNoiseTruncate t ξ) =
      idealNoiseTruncate t (idealExtendedNoiseTake ξ) := by
  funext i
  by_cases hi : i.val < t
  · simp [idealExtendedNoiseTake, idealNoiseTruncate, hi]
  · simp [idealExtendedNoiseTake, idealNoiseTruncate, hi]

end

end HeavyTailedNoise
