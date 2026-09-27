import HeavyTailedNoise.Lower.Gated.IdealStoppedHistory

/-!
The common query rule after a fixed stopped pre-response snapshot. The state
is the full `N`-slot query/response transcript. At the hard response cap, the
query is the algorithm's output and the update ignores auxiliary responses.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace HeavyTailedNoise

/-- A relative slot is response-bearing exactly while the fixed stopped
snapshot has started and its absolute query time is below the hard cap. -/
def actualFrozenActive {d N : ℕ} (s : IdealPreResponseHistory d N)
    (t : ℕ) : Prop :=
  s.started = true ∧ s.time + t < N

/-- Extract the entire already returned history at absolute time `s.time+t`
from the common padded full transcript. -/
def actualFrozenPast {d N : ℕ} (s : IdealPreResponseHistory d N)
    (t : ℕ) (ht : s.time + t < N)
    (tr : Transcript d N) : Transcript d (s.time + t) :=
  fun i => tr ⟨i.val, lt_trans i.isLt ht⟩

lemma measurable_actualFrozenPast {d N : ℕ}
    (s : IdealPreResponseHistory d N) (t : ℕ)
    (ht : s.time + t < N) :
    Measurable (actualFrozenPast s t ht) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply (⟨i.val, lt_trans i.isLt ht⟩ : Fin N)

lemma actualFrozenPast_apply {d N : ℕ}
    (s : IdealPreResponseHistory d N) (t : ℕ)
    (ht : s.time + t < N) (tr : Transcript d N)
    (i : Fin (s.time + t)) :
    actualFrozenPast s t ht tr i =
      tr ⟨i.val, lt_trans i.isLt ht⟩ := rfl

/-- The first response-bearing query is the snapshot's already selected query.
Later responsive queries use `A.decide` on every returned pair, including all
pre-stop pairs. At or after the hard cap this is the response-free output. -/
def actualFrozenQuery {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N)
    (t : ℕ) (tr : Transcript d N) : Point d := by
  classical
  exact if ha : actualFrozenActive s t then
    if t = 0 then s.query
    else A.decide (s.time + t) r (actualFrozenPast s t ha.2 tr)
  else A.output r tr

lemma actualFrozenQuery_first {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N)
    (ha : actualFrozenActive s 0) (tr : Transcript d N) :
    actualFrozenQuery A r s 0 tr = s.query := by
  simp [actualFrozenQuery, ha]

lemma actualFrozenQuery_later {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N) (t : ℕ)
    (ha : actualFrozenActive s t) (ht : t ≠ 0)
    (tr : Transcript d N) :
    actualFrozenQuery A r s t tr =
      A.decide (s.time + t) r (actualFrozenPast s t ha.2 tr) := by
  simp [actualFrozenQuery, ha, ht]

lemma measurable_actualFrozenQuery {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N) (t : ℕ) :
    Measurable (actualFrozenQuery A r s t) := by
  classical
  unfold actualFrozenQuery
  by_cases ha : actualFrozenActive s t
  · by_cases ht : t = 0
    · simp only [dif_pos ha, if_pos ht]
      exact measurable_const
    · have hp := measurable_actualFrozenPast s t ha.2
      have hq := (A.measurable_decide (s.time + t)).comp
        ((measurable_const : Measurable (fun _ : Transcript d N => r)).prodMk hp)
      have hq' : Measurable (fun tr : Transcript d N =>
          A.decide (s.time + t) r (actualFrozenPast s t ha.2 tr)) := by
        simpa only [Function.comp_def] using hq
      simpa only [dif_pos ha, if_neg ht] using hq'
  · have hq := A.measurable_output.comp
      ((measurable_const : Measurable (fun _ : Transcript d N => r)).prodMk
        (measurable_id : Measurable (id : Transcript d N → Transcript d N)))
    have hq' : Measurable (fun tr : Transcript d N => A.output r tr) := by
      simpa only [Function.comp_def, id_eq] using hq
    simpa only [dif_neg ha] using hq'

/-- One common state update. The same query rule is used under both hidden
directions. A response at or beyond `N` changes no transcript coordinate. -/
def actualFrozenUpdate {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N) (t : ℕ) :
    Transcript d N × Point d → Transcript d N := by
  classical
  exact fun z => if ha : actualFrozenActive s t then
    Function.update z.1 ⟨s.time + t, ha.2⟩
      (actualFrozenQuery A r s t z.1, z.2)
  else z.1

lemma actualFrozenUpdate_active {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N) (t : ℕ)
    (ha : actualFrozenActive s t) (tr : Transcript d N)
    (y : Point d) :
    actualFrozenUpdate A r s t (tr, y)
      ⟨s.time + t, ha.2⟩ =
      (actualFrozenQuery A r s t tr, y) := by
  simp [actualFrozenUpdate, ha]

lemma measurable_actualFrozenUpdate {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N) (t : ℕ) :
    Measurable (actualFrozenUpdate A r s t) := by
  classical
  unfold actualFrozenUpdate
  by_cases ha : actualFrozenActive s t
  · have hpair : Measurable (fun z : Transcript d N × Point d =>
        (z.1, (actualFrozenQuery A r s t z.1, z.2))) :=
      measurable_fst.prodMk
        (((measurable_actualFrozenQuery A r s t).comp measurable_fst).prodMk
          measurable_snd)
    simpa only [dif_pos ha, Function.comp_def] using
      (measurable_update' (a := (⟨s.time + t, ha.2⟩ : Fin N))).comp hpair
  · simpa only [dif_neg ha] using
      (measurable_fst : Measurable
        (fun z : Transcript d N × Point d => z.1))

lemma actualFrozenQuery_at_cap {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N) (t : ℕ)
    (hcap : N ≤ s.time + t) (tr : Transcript d N) :
    actualFrozenQuery A r s t tr = A.output r tr := by
  have ha : ¬actualFrozenActive s t := by
    intro h
    exact (not_lt_of_ge hcap) h.2
  simp [actualFrozenQuery, ha]

lemma actualFrozenUpdate_at_cap {d N : ℕ} {Private : Type*}
    [MeasurableSpace Private] (A : RandomAlgorithm d N Private)
    (r : Private) (s : IdealPreResponseHistory d N) (t : ℕ)
    (hcap : N ≤ s.time + t) (z : Transcript d N × Point d) :
    actualFrozenUpdate A r s t z = z.1 := by
  have ha : ¬actualFrozenActive s t := by
    intro h
    exact (not_lt_of_ge hcap) h.2
  simp [actualFrozenUpdate, ha]

end HeavyTailedNoise
