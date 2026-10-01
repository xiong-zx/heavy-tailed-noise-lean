import HeavyTailedNoise.Upper.K1.CoarseTrackerInitialQuery
import HeavyTailedNoise.Upper.K1.BatchSeedProduct

/-!
The optional initialization block consists of the global seed coordinates
strictly after the first response and before runtime. Each such coordinate
produces one response at point zero; there is no seed reuse or new query.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

variable {q : ℝ} (P : Schedule q)

def initialSeedIndex (i : Fin (initialResponses P)) :
    Fin (responseCount P) :=
  ⟨1 + i.val, by
    have hi := i.isLt
    dsimp [responseCount]
    omega⟩

def initialSeedBlock {Seed : Type*}
    (seeds : Fin (responseCount P) → Seed) :
    Fin (initialResponses P) → Seed :=
  fun i => seeds (initialSeedIndex P i)

theorem measurable_initialSeedBlock {Seed : Type*}
    [MeasurableSpace Seed] :
    Measurable (initialSeedBlock (Seed := Seed) P) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply (initialSeedIndex P i)

theorem initial_logged_response_eq_oracle {d : ℕ} {Seed : Type*}
    [MeasurableSpace Seed]
    (O : GradientOracle d Seed)
    (r : Fin P.T) (seeds : Fin (responseCount P) → Seed)
    (i : Fin (initialResponses P)) :
    (runTranscript O (algorithm (d := d) P) r
      (responseCount P) seeds (initialSeedIndex P i)).2 =
      O.response 0 (initialSeedBlock P seeds i) := by
  let k := 1 + i.val
  have hk : k + 1 ≤ responseCount P := by
    have hi := i.isLt
    dsimp [k, responseCount]
    omega
  let seedPrefix : Fin (k + 1) → Seed :=
    fun j => seeds (j.castLE hk)
  have hprefix := runTranscript_prefix_le O (algorithm (d := d) P) r
    (k + 1) (responseCount P) hk seeds (Fin.last k)
  have hindex : (Fin.last k).castLE hk = initialSeedIndex P i :=
    Fin.ext rfl
  rw [hindex] at hprefix
  have hpair := hprefix.trans (algorithm_last_response P O r k seedPrefix)
  have hy := congrArg Prod.snd hpair
  dsimp at hy
  have hquery : query P k
      (runTranscript O (algorithm (d := d) P) r k
        (fun j : Fin k => seedPrefix j.castSucc)) = 0 :=
    initial_query_zero P i.val (Nat.le_of_lt i.isLt) _
  have hseed : seedPrefix (Fin.last k) = initialSeedBlock P seeds i := by
    change seeds ((Fin.last k).castLE hk) = seeds (initialSeedIndex P i)
    congr 1
  rw [hquery, hseed] at hy
  exact hy

end

end HeavyTailedNoise.UpperK1
