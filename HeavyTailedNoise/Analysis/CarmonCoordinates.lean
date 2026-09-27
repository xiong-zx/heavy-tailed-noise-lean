import HeavyTailedNoise.Analysis.FrameCoordinates

namespace HeavyTailedNoise

open Set Filter
open scoped BigOperators Topology Classical
noncomputable section

def chainPredecessor {T : ℕ} (z : Fin T → ℝ) (k : Fin T) : ℝ :=
  if h : k.val = 0 then 1 else z ⟨k.val - 1, by omega⟩

theorem contDiff_chainPredecessor {T : ℕ} (k : Fin T) :
    ContDiff ℝ 2 (fun z : Fin T → ℝ => chainPredecessor z k) := by
  unfold chainPredecessor
  split <;> fun_prop

def chainPredecessorVector {d T : ℕ} (U : Fin T → Point d) (k : Fin T) : Point d :=
  if h : k.val = 0 then 0 else U ⟨k.val - 1, by omega⟩

theorem hasFDerivAt_chainPredecessor_pullback {d T : ℕ} (U : Fin T → Point d)
    (k : Fin T) (y : Point d) :
    HasFDerivAt (fun x => chainPredecessor (frameCoordinates U x) k)
      (innerSL ℝ (chainPredecessorVector U k)) y := by
  by_cases hk : k.val = 0
  · simpa [chainPredecessor, chainPredecessorVector, hk] using
      (hasFDerivAt_const (𝕜 := ℝ) (c := (1 : ℝ)) (x := y))
  · simpa [chainPredecessor, chainPredecessorVector, frameCoordinates, hk] using
      (innerSL ℝ (U ⟨k.val - 1, by omega⟩)).hasFDerivAt (x := y)

theorem chainPredecessorVector_norm_le {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) : ‖chainPredecessorVector U k‖ ≤ 1 := by
  by_cases hk : k.val = 0
  · simp [chainPredecessorVector, hk]
  · simp [chainPredecessorVector, hk, hU.norm_eq_one]

theorem chainPredecessorVector_orthogonal {d T : ℕ} {U : Fin T → Point d}
    (hU : Orthonormal ℝ U) (k : Fin T) :
    inner ℝ (chainPredecessorVector U k) (U k) = 0 := by
  by_cases hk : k.val = 0
  · simp [chainPredecessorVector, hk]
  · unfold chainPredecessorVector
    simp only [dif_neg hk]
    apply hU.inner_eq_zero
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega


end

end HeavyTailedNoise
