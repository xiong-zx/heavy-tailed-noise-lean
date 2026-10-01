import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchAccumulatorPrefix
import HeavyTailedNoise.Upper.K1.CoarseTrackerBatchEstimate

/-!
The proper-prefix accumulator plus the last returned vector is the full
batch sum. These identities preserve the one frozen center and the unique
accumulator used by `Algorithm.step`, including `n=1`.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem batch_sum_eq_prefix_add_last {d : ℕ}
    (f : Fin P.n → Point d) :
    (∑ i : Fin P.n, f i) =
      (∑ i : Fin (P.n - 1), f (prefixResponseIndex P i)) +
        f (lastResponseIndex P) := by
  classical
  let k := P.n - 1
  have hlen : k + 1 = P.n := by
    dsimp [k]
    have hn := P.n_pos
    omega
  let g : Fin (k + 1) → Point d := fun i => f (i.cast hlen)
  have hcast : (∑ i : Fin (k + 1), g i) =
      ∑ i : Fin P.n, f i := by
    dsimp [g]
    apply Finset.sum_bij (fun i _ => i.cast hlen)
    · intro i hi
      simp
    · intro i hi i' hi' heq
      apply Fin.ext
      simpa only [Fin.val_cast] using congrArg Fin.val heq
    · intro b hb
      refine ⟨b.cast hlen.symm, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      rfl
    · intro i hi
      rfl
  calc
    (∑ i : Fin P.n, f i) = ∑ i : Fin (k + 1), g i := hcast.symm
    _ = (∑ i : Fin k, g i.castSucc) + g (Fin.last k) :=
      Fin.sum_univ_castSucc g
    _ = (∑ i : Fin (P.n - 1), f (prefixResponseIndex P i)) +
          f (lastResponseIndex P) := by
        congr 1

theorem accumulateResponse_full_low {d : ℕ} (u : Fin P.T)
    (s : State d P.J) (ys : Fin P.n → Point d) :
    let k := P.n - 1
    let pre := foldResponses P (batchStart P u.val) s k
      (fun i : Fin k => ys (prefixResponseIndex P i))
    (accumulateResponse P pre (ys (lastResponseIndex P))).1 =
      lowSum P s + ∑ i : Fin P.n,
        lowBand P (ys i - center P s) := by
  dsimp only
  let k := P.n - 1
  let pre := foldResponses P (batchStart P u.val) s k
    (fun i : Fin k => ys (prefixResponseIndex P i))
  have hk : k < P.n := by
    dsimp [k]
    have hn := P.n_pos
    omega
  have hcenter := (foldResponses_prefix_point_center P u s k hk
    (fun i : Fin k => ys (prefixResponseIndex P i))).2
  have hlow := foldResponses_prefix_lowSum P u s k hk
    (fun i : Fin k => ys (prefixResponseIndex P i))
  have hfull := batch_sum_eq_prefix_add_last P
    (fun i : Fin P.n => lowBand P (ys i - center P s))
  change lowSum P pre +
      lowBand P (ys (lastResponseIndex P) - center P pre) = _
  rw [hlow, hcenter, hfull]
  abel

theorem accumulateResponse_full_high {d : ℕ} (u : Fin P.T)
    (s : State d P.J) (ys : Fin P.n → Point d) (j : Fin P.J) :
    let k := P.n - 1
    let pre := foldResponses P (batchStart P u.val) s k
      (fun i : Fin k => ys (prefixResponseIndex P i))
    (accumulateResponse P pre (ys (lastResponseIndex P))).2 j =
      highSums P s j + ∑ i : Fin P.n,
        highBand P j (ys i - center P s) := by
  dsimp only
  let k := P.n - 1
  let pre := foldResponses P (batchStart P u.val) s k
    (fun i : Fin k => ys (prefixResponseIndex P i))
  have hk : k < P.n := by
    dsimp [k]
    have hn := P.n_pos
    omega
  have hcenter := (foldResponses_prefix_point_center P u s k hk
    (fun i : Fin k => ys (prefixResponseIndex P i))).2
  have hhigh := foldResponses_prefix_highSums P u s k hk
    (fun i : Fin k => ys (prefixResponseIndex P i)) j
  have hfull := batch_sum_eq_prefix_add_last P
    (fun i : Fin P.n => highBand P j (ys i - center P s))
  change highSums P pre j +
      highBand P j (ys (lastResponseIndex P) - center P pre) = _
  rw [hhigh, hcenter, hfull]
  abel

end

end HeavyTailedNoise.UpperK1
