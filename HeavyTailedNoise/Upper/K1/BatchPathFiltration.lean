import HeavyTailedNoise.Upper.K1.Algorithm
import HeavyTailedNoise.Upper.Foundations.ClippedBatch
import HeavyTailedNoise.Upper.Foundations.SourceOrthogonality

/-!
The full pre-batch history and the fresh seed block of one runtime batch.
No response from the current batch enters the history used for its query or
center. The private output index is retained in the history type, though the
query rule does not read it.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- Full private information and returned transcript before runtime batch `u`. -/
abbrev BatchHistory (d : ℕ) (u : Fin P.T) :=
  Fin P.T × Transcript d (batchStart P u.val)

def batchDecision {d : ℕ} (u : Fin P.T) (H : BatchHistory P d u) : Point d :=
  query P (batchStart P u.val) H.2

def batchCenter {d : ℕ} (u : Fin P.T) (H : BatchHistory P d u) : Point d :=
  center P (stateAt P (batchStart P u.val) H.2)

theorem measurable_batchDecision {d : ℕ} (u : Fin P.T) :
    Measurable (batchDecision (d := d) P u) :=
  (measurable_query P (batchStart P u.val)).comp measurable_snd

theorem measurable_batchCenter {d : ℕ} (u : Fin P.T) :
    Measurable (batchCenter (d := d) P u) := by
  exact measurable_fst.comp (measurable_snd.comp
    ((measurable_stateAt P (batchStart P u.val)).comp measurable_snd))

private theorem batchStart_le_responseCount (u : Fin P.T) :
    batchStart P u.val ≤ responseCount P := by
  have hu : u.val ≤ P.T := Nat.le_of_lt u.isLt
  have hmul := Nat.mul_le_mul_right P.n hu
  dsimp [batchStart, responseCount]
  omega

private theorem batchIndex_lt_responseCount (u : Fin P.T) (j : Fin P.n) :
    batchStart P u.val + j.val < responseCount P := by
  have hu : u.val + 1 ≤ P.T := Nat.succ_le_iff.mpr u.isLt
  have hmul : (u.val + 1) * P.n ≤ P.T * P.n :=
    Nat.mul_le_mul_right P.n hu
  have hsmall : u.val * P.n + j.val < (u.val + 1) * P.n := by
    have hj : j.val < P.n := j.isLt
    rw [Nat.succ_mul]
    omega
  calc
    batchStart P u.val + j.val =
        1 + initialResponses P + (u.val * P.n + j.val) := by
          dsimp [batchStart]
          omega
    _ < 1 + initialResponses P + (u.val + 1) * P.n :=
      Nat.add_lt_add_left hsmall _
    _ ≤ 1 + initialResponses P + P.T * P.n :=
      Nat.add_le_add_left hmul _
    _ = responseCount P := rfl

/-- The `j`th current-batch response is the global response at exactly this
index; the prefix and the later seed coordinates are disjoint from its block. -/
def batchResponseIndex (u : Fin P.T) (j : Fin P.n) : Fin (responseCount P) :=
  ⟨batchStart P u.val + j.val, batchIndex_lt_responseCount P u j⟩

@[simp] theorem batchResponseIndex_val (u : Fin P.T) (j : Fin P.n) :
    (batchResponseIndex P u j).val = batchStart P u.val + j.val := rfl

theorem batchResponseIndex_ge_start (u : Fin P.T) (j : Fin P.n) :
    batchStart P u.val ≤ (batchResponseIndex P u j).val := by
  simp [batchResponseIndex]

theorem batchResponseIndex_lt_end (u : Fin P.T) (j : Fin P.n) :
    (batchResponseIndex P u j).val < batchStart P u.val + P.n := by
  simp only [batchResponseIndex_val]
  omega

def batchSeedBlock {Seed : Type*} (u : Fin P.T)
    (seeds : Fin (responseCount P) → Seed) : Fin P.n → Seed :=
  fun j => seeds (batchResponseIndex P u j)

theorem measurable_batchSeedBlock {Seed : Type*} [MeasurableSpace Seed]
    (u : Fin P.T) :
    Measurable (batchSeedBlock (Seed := Seed) P u) := by
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_pi_apply (batchResponseIndex P u j)

theorem runTranscript_prefix_le {d N : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] {Private : Type*} [MeasurableSpace Private]
    (O : GradientOracle d Seed) (A : RandomAlgorithm d N Private)
    (r : Private) :
    ∀ (m n : ℕ) (hm : m ≤ n) (seeds : Fin n → Seed) (i : Fin m),
      runTranscript O A r n seeds (i.castLE hm) =
        runTranscript O A r m (fun j => seeds (j.castLE hm)) i := by
  intro m n
  induction n generalizing m with
  | zero =>
      intro hm seeds i
      have hm0 : m = 0 := by omega
      subst m
      exact i.elim0
  | succ n ih =>
      intro hm seeds i
      by_cases hmn : m ≤ n
      · have hi : i.castLE hm = (i.castLE hmn).castSucc := Fin.ext rfl
        rw [hi, runTranscript_prefix]
        have hprefix := ih m hmn (fun k : Fin n => seeds k.castSucc) i
        have hseed :
            (fun j : Fin m => seeds ((j.castLE hmn).castSucc)) =
              (fun j : Fin m => seeds (j.castLE hm)) := by
          funext j
          congr 1
        simpa only [hseed] using hprefix
      · have hmEq : m = n + 1 := by omega
        subst m
        rfl

/-- The actual pre-batch history is measurable in the private index and all
fresh seeds. Only the strict seed prefix is read to build its transcript. -/
def batchHistoryOfRun {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (u : Fin P.T)
    (z : Fin P.T × (Fin (responseCount P) → Seed)) :
    BatchHistory P d u :=
  (z.1, runTranscript O (algorithm (d := d) P) z.1 (batchStart P u.val)
    (fun i => z.2 (i.castLE (batchStart_le_responseCount P u))))

theorem measurable_batchHistoryOfRun {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (u : Fin P.T) :
    Measurable (batchHistoryOfRun (d := d) P O u) := by
  have hprefix : Measurable
      (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
        (fun i : Fin (batchStart P u.val) =>
          z.2 (i.castLE (batchStart_le_responseCount P u)))) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (i.castLE (batchStart_le_responseCount P u))).comp
      measurable_snd
  exact measurable_fst.prodMk
    ((measurable_runTranscript O (algorithm (d := d) P)
      (batchStart P u.val)).comp (measurable_fst.prodMk hprefix))

theorem measurable_batchDecisionOfRun {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (u : Fin P.T) :
    Measurable (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
      batchDecision P u (batchHistoryOfRun P O u z)) :=
  (measurable_batchDecision P u).comp (measurable_batchHistoryOfRun P O u)

theorem measurable_batchCenterOfRun {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed) (u : Fin P.T) :
    Measurable (fun z : Fin P.T × (Fin (responseCount P) → Seed) =>
      batchCenter P u (batchHistoryOfRun P O u z)) :=
  (measurable_batchCenter P u).comp (measurable_batchHistoryOfRun P O u)

/-- Every response logged in runtime batch `u` is queried at the same
decision selected from the complete pre-batch history. -/
theorem batch_logged_response_at_prebatch_decision {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (O : GradientOracle d Seed)
    (r u : Fin P.T) (seeds : Fin (responseCount P) → Seed) (j : Fin P.n) :
    (runTranscript O (algorithm (d := d) P) r (responseCount P) seeds
      (batchResponseIndex P u j)).1 =
      batchDecision P u (batchHistoryOfRun P O u (r, seeds)) := by
  let k := batchResponseIndex P u j
  have hlog := algorithm_logged_query P O r (responseCount P) seeds k
  rw [hlog]
  change query P (batchStart P u.val + j.val)
      (runTranscript O (algorithm (d := d) P) r (batchStart P u.val + j.val)
        (fun i => seeds (i.castLE
          (Nat.le_of_lt (batchIndex_lt_responseCount P u j))))) = _
  rw [batch_query_fixed P u j]
  congr 1
  funext i
  have hi : batchStart P u.val ≤ batchStart P u.val + j.val := Nat.le_add_right _ _
  exact runTranscript_prefix_le O (algorithm (d := d) P) r
    (batchStart P u.val) (batchStart P u.val + j.val) hi
    (fun k => seeds (k.castLE
      (Nat.le_of_lt (batchIndex_lt_responseCount P u j)))) i

end

end HeavyTailedNoise.UpperK1
