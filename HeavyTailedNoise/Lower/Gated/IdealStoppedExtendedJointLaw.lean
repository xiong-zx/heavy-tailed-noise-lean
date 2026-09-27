import HeavyTailedNoise.Lower.Gated.IdealExtendedNoise

/-!
The fixed-time stage-start record, computed only from the algorithm's first
`N` noise seeds, is independent of an auxiliary length-`m` Gaussian block
starting at that possible stage-start time.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

def idealStoppedExtendedEventTuple
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (t : ℕ) (ξ : Fin (N + m) → Point d) :
    Bool × (Bool × ℕ × Transcript d N × Point d) :=
  idealStoppedEventTuple hT U k A r a t (idealExtendedNoiseTake ξ)

lemma measurable_idealStoppedExtendedEventTuple
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (t : ℕ) :
    Measurable (idealStoppedExtendedEventTuple
      (m := m) hT U k A r a t) :=
  (measurable_idealStoppedEventTuple hT U k A r a t).comp
    measurable_idealExtendedNoiseTake

theorem idealStoppedExtendedEventTuple_eq_truncate
    {d T N m t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (htN : t ≤ N) (ξ : Fin (N + m) → Point d) :
    idealStoppedExtendedEventTuple hT U k A r a t ξ =
      idealStoppedExtendedEventTuple hT U k A r a t
        (idealNoiseTruncate t ξ) := by
  change idealStoppedEventTuple hT U k A r a t
      (idealExtendedNoiseTake ξ) =
    idealStoppedEventTuple hT U k A r a t
      (idealExtendedNoiseTake (idealNoiseTruncate t ξ))
  rw [idealExtendedNoiseTake_truncate]
  exact idealStoppedEventTuple_eq_truncate
    hT U k A r a htN (idealExtendedNoiseTake ξ)

theorem idealStoppedExtendedEventTuple_indep_tail
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (t : ℕ) (htN : t ≤ N) :
    IndepFun
      (idealStoppedExtendedEventTuple (m := m) hT U k A r a t)
      (idealExtendedNoiseTail (d := d) (m := m) t htN)
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)) := by
  have hbase := idealExtendedNoiseTruncate_indep_tail
    (d := d) (m := m) t htN
  have hc := hbase.comp
    (measurable_idealStoppedExtendedEventTuple
      (m := m) hT U k A r a t) measurable_id
  have hc' : IndepFun
      (fun ξ : Fin (N + m) → Point d =>
        idealStoppedExtendedEventTuple hT U k A r a t
          (idealNoiseTruncate t ξ))
      (idealExtendedNoiseTail (d := d) (m := m) t htN)
      (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)) := by
    simpa only [Function.comp_def, id_eq] using hc
  have heq :
      (fun ξ : Fin (N + m) → Point d =>
        idealStoppedExtendedEventTuple hT U k A r a t
          (idealNoiseTruncate t ξ)) =
      idealStoppedExtendedEventTuple hT U k A r a t := by
    funext ξ
    exact (idealStoppedExtendedEventTuple_eq_truncate
      hT U k A r a htN ξ).symm
  rw [heq] at hc'
  exact hc'

theorem idealStoppedExtendedEventTuple_jointLaw
    {d T N m : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (t : ℕ) (htN : t ≤ N) :
    (Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).map
      (fun ξ : Fin (N + m) → Point d =>
        (idealStoppedExtendedEventTuple hT U k A r a t ξ,
          idealExtendedNoiseTail t htN ξ)) =
      ((Measure.pi (fun _ : Fin (N + m) => standardGaussianLaw d)).map
        (idealStoppedExtendedEventTuple hT U k A r a t)).prod
          (Measure.pi (fun _ : Fin m => standardGaussianLaw d)) := by
  have hprod := (idealStoppedExtendedEventTuple_indep_tail
    (m := m) hT U k A r a t htN).map_prod_eq_prod_map_map
      (measurable_idealStoppedExtendedEventTuple
        (m := m) hT U k A r a t).aemeasurable
      (measurable_idealExtendedNoiseTail t htN).aemeasurable
  rw [idealExtendedNoiseTail_law t htN] at hprod
  exact hprod

end

end HeavyTailedNoise
