import HeavyTailedNoise.Lower.Gated.IdealStoppedExtendedJointLaw

/-!
Measurable bounded random-stage-start time and its fixed-length auxiliary
Gaussian tail. The tail begins at the start time when it is at most `N`, and
at `N` for the never-started sentinel `N+1`.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

def idealExtendedStageStart
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (ξ : Fin (N + m) → Point d) : ℕ :=
  idealStageStart hT U A r (idealExtendedNoiseTake ξ) a (k.val + 1)

lemma measurable_idealExtendedStageStart
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Measurable (idealExtendedStageStart (m := m) hT U k A r a) := by
  have hrecord := (measurable_idealStoppedPreTuple_fixed hT U k A r a).comp
    (measurable_idealExtendedNoiseTake (d := d) (N := N) (m := m))
  have hp : Measurable (fun z : Bool × ℕ × Transcript d N × Point d =>
      z.2.1) := measurable_fst.comp measurable_snd
  have hc := hp.comp hrecord
  have heq :
      (fun ξ : Fin (N + m) → Point d =>
        (idealPreResponseTuple
          (idealStoppedPreHistory hT U k A r
            (idealExtendedNoiseTake ξ) a)).2.1) =
      idealExtendedStageStart hT U k A r a := by
    funext ξ
    exact idealStoppedPreTuple_time hT U k A r
      (idealExtendedNoiseTake ξ) a
  rw [← heq]
  exact hc

def idealRandomStartTail
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (ξ : Fin (N + m) → Point d) : Fin m → Point d :=
  idealExtendedNoiseTail
    (min (idealExtendedStageStart hT U k A r a ξ) N)
    (Nat.min_le_right _ _) ξ

lemma measurable_idealRandomStartTail
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Measurable (idealRandomStartTail (m := m) hT U k A r a) := by
  let f : (Fin (N + m) → Point d) × ℕ → (Fin m → Point d) :=
    fun z => idealExtendedNoiseTail (min z.2 N)
      (Nat.min_le_right _ _) z.1
  have hf : Measurable f :=
    measurable_from_prod_countable_left (fun t =>
      measurable_idealExtendedNoiseTail (min t N)
        (Nat.min_le_right _ _))
  have hpair : Measurable (fun ξ : Fin (N + m) → Point d =>
      (ξ, idealExtendedStageStart hT U k A r a ξ)) :=
    measurable_id.prodMk
      (measurable_idealExtendedStageStart hT U k A r a)
  have hc := hf.comp hpair
  change Measurable (f ∘ fun ξ : Fin (N + m) → Point d =>
    (ξ, idealExtendedStageStart hT U k A r a ξ))
  exact hc

lemma idealRandomStartTail_on_start
    {d T N m t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (htN : t ≤ N) (ξ : Fin (N + m) → Point d)
    (hstart : idealExtendedStageStart hT U k A r a ξ = t) :
    idealRandomStartTail hT U k A r a ξ =
      idealExtendedNoiseTail t htN ξ := by
  funext i
  change ξ ⟨min (idealExtendedStageStart hT U k A r a ξ) N + i.val,
      by omega⟩ = ξ ⟨t + i.val, by omega⟩
  apply congrArg ξ
  apply Fin.ext
  simp only [Fin.val_mk]
  rw [hstart, Nat.min_eq_left htN]

lemma idealRandomStartTail_never_started
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (ξ : Fin (N + m) → Point d)
    (hstart : idealExtendedStageStart hT U k A r a ξ = N + 1) :
    idealRandomStartTail hT U k A r a ξ =
      idealExtendedNoiseTail N le_rfl ξ := by
  funext i
  change ξ ⟨min (idealExtendedStageStart hT U k A r a ξ) N + i.val,
      by omega⟩ = ξ ⟨N + i.val, by omega⟩
  apply congrArg ξ
  apply Fin.ext
  simp only [Fin.val_mk]
  rw [hstart]
  omega

end

end HeavyTailedNoise
