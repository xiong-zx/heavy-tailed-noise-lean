import HeavyTailedNoise.Lower.Gated.IdealNoiseIndependence
import HeavyTailedNoise.Lower.Gated.JointPrefixGradientMeas

/-!
At each fixed possible start time, the event and stopped pre-response record
are independent of the entire suffix of unused Gaussian seeds. This is a
finite-horizon building block for the random-time fresh-noise kernel.
-/

namespace HeavyTailedNoise

open MeasureTheory ProbabilityTheory

noncomputable section

lemma idealStoppedPreTuple_time {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (ξ : Fin N → Point d) (a : ℝ) :
    (idealPreResponseTuple
      (idealStoppedPreHistory hT U k A r ξ a)).2.1 =
        idealStageStart hT U A r ξ a (k.val + 1) := by
  let τ := idealStageStart hT U A r ξ a (k.val + 1)
  have hbound : τ ≤ N + 1 := idealStageStart_le_succ hT U A r ξ a _
  by_cases ht : τ ≤ N
  · simp [idealStoppedPreHistory, idealPreHistoryAtTime,
      idealPreResponseTuple, τ, ht]
  · have hτ : τ = N + 1 := by omega
    simp [idealStoppedPreHistory, idealPreHistoryAtTime,
      idealPreResponseTuple, τ, hτ]

lemma measurable_idealStoppedPreTuple_fixed
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ) :
    Measurable (fun ξ : Fin N → Point d =>
      idealPreResponseTuple (idealStoppedPreHistory hT U k A r ξ a)) := by
  have hin : Measurable (fun ξ : Fin N → Point d =>
      (framePrefix (Nat.succ_le_iff.mpr k.isLt) U, (r, ξ))) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hc := (measurable_idealStoppedPreHistoryFromPrefix hT k A a).comp hin
  have heq :
      (fun ξ : Fin N → Point d =>
        idealPreResponseTuple (idealStoppedPreHistory hT U k A r ξ a)) =
      (fun ξ : Fin N → Point d =>
        idealStoppedPreHistoryFromPrefix hT k A a
          (framePrefix (Nat.succ_le_iff.mpr k.isLt) U, (r, ξ))) := by
    funext ξ
    exact idealStoppedPreHistoryFromPrefix_eq hT U k A r ξ a
  rw [heq]
  exact hc

def idealStoppedEventTuple {d T N : ℕ}
    {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (t : ℕ) (ξ : Fin N → Point d) :
    Bool × (Bool × ℕ × Transcript d N × Point d) := by
  classical
  exact if idealStageStart hT U A r ξ a (k.val + 1) = t then
    (true, idealPreResponseTuple (idealStoppedPreHistory hT U k A r ξ a))
  else (false, (false, 0, fun _ => (0, 0), 0))

lemma measurable_idealStoppedEventTuple
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (t : ℕ) :
    Measurable (idealStoppedEventTuple hT U k A r a t) := by
  classical
  have hrec := measurable_idealStoppedPreTuple_fixed hT U k A r a
  have htime : Measurable (fun ξ : Fin N → Point d =>
      idealStageStart hT U A r ξ a (k.val + 1)) := by
    have hp : Measurable (fun z : Bool × ℕ × Transcript d N × Point d =>
        z.2.1) := measurable_fst.comp measurable_snd
    have hc := hp.comp hrec
    have heq :
        (fun ξ : Fin N → Point d =>
          (idealPreResponseTuple
            (idealStoppedPreHistory hT U k A r ξ a)).2.1) =
        (fun ξ : Fin N → Point d =>
          idealStageStart hT U A r ξ a (k.val + 1)) := by
      funext ξ
      exact idealStoppedPreTuple_time hT U k A r ξ a
    rw [← heq]
    exact hc
  have hset : MeasurableSet
      {ξ : Fin N → Point d |
        idealStageStart hT U A r ξ a (k.val + 1) = t} :=
    measurableSet_eq_fun htime measurable_const
  unfold idealStoppedEventTuple
  exact Measurable.ite hset (measurable_const.prodMk hrec) measurable_const

theorem idealStoppedEventTuple_eq_truncate
    {d T N t : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (htN : t ≤ N) (ξ : Fin N → Point d) :
    idealStoppedEventTuple hT U k A r a t ξ =
      idealStoppedEventTuple hT U k A r a t
        (idealNoiseTruncate t ξ) := by
  classical
  have hiff := idealStageStart_eq_iff_truncate hT U A r ξ a
    (k.val + 1) htN
  by_cases hstart : idealStageStart hT U A r ξ a (k.val + 1) = t
  · have hstart' := hiff.mp hstart
    have hrec := idealStoppedPreHistory_eq_truncate_on_start
      hT U k A r ξ a htN hstart
    simp [idealStoppedEventTuple, hstart, hstart', hrec]
  · have hstart' :
        idealStageStart hT U A r (idealNoiseTruncate t ξ) a
          (k.val + 1) ≠ t := fun hh => hstart (hiff.mpr hh)
    simp [idealStoppedEventTuple, hstart, hstart']

theorem idealStoppedEventTuple_indep_suffix
    {d T N : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private) (a : ℝ)
    (t : ℕ) (htN : t ≤ N) :
    IndepFun
      (idealStoppedEventTuple hT U k A r a t)
      (fun ξ : Fin N → Point d =>
        fun i : idealNoiseSuffixIndices N t => ξ i.1)
      (Measure.pi (fun _ : Fin N => standardGaussianLaw d)) := by
  have hbase := idealNoiseTruncate_indep_suffix (d := d) (N := N) t
  have hc := hbase.comp
    (measurable_idealStoppedEventTuple hT U k A r a t) measurable_id
  have heq :
      (idealStoppedEventTuple hT U k A r a t ∘
        idealNoiseTruncate t) =
      idealStoppedEventTuple hT U k A r a t := by
    funext ξ
    exact (idealStoppedEventTuple_eq_truncate
      hT U k A r a htN ξ).symm
  simpa only [heq, Function.comp_def, id_eq] using hc

end

end HeavyTailedNoise
