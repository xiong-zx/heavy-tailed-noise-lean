import HeavyTailedNoise.Lower.Gated.IdealFrozenZeroExitQuery
import HeavyTailedNoise.Lower.Gated.IdealRandomStartFreshNoise

/-!
On the actual started path, every responsive prefix of the random-start
auxiliary Gaussian tail is exactly the corresponding segment of the original
`N`-response noise tape. Coordinates beyond `N` stay auxiliary and unseen.
-/

namespace HeavyTailedNoise

noncomputable section

def idealTailPrefix {d m u : ℕ} (hu : u ≤ m)
    (ζ : Fin m → Point d) : Fin u → Point d :=
  fun i => ζ ⟨i.val, by omega⟩

theorem idealRandomStartTail_prefix_eq_originalNoiseSlice
    {d T N m u : ℕ} {Private : Type*} [MeasurableSpace Private]
    (hT : 0 < T) (U : Fin T → Point d) (k : Fin T)
    (A : RandomAlgorithm d N Private) (r : Private)
    (Ξ : Fin (N + m) → Point d) (a : ℝ)
    (hstart : idealStageStart hT U A r
      (idealExtendedNoiseTake Ξ) a (k.val + 1) ≤ N)
    (hu : u ≤ m)
    (hcap : idealStageStart hT U A r
      (idealExtendedNoiseTake Ξ) a (k.val + 1) + u ≤ N) :
    idealTailPrefix hu (idealRandomStartTail hT U k A r a Ξ) =
      idealNoiseSlice
        (idealStageStart hT U A r
          (idealExtendedNoiseTake Ξ) a (k.val + 1))
        hcap (idealExtendedNoiseTake Ξ) := by
  let τ := idealStageStart hT U A r
    (idealExtendedNoiseTake Ξ) a (k.val + 1)
  have htail : idealRandomStartTail hT U k A r a Ξ =
      idealExtendedNoiseTail τ hstart Ξ :=
    idealRandomStartTail_on_start hT U k A r a hstart Ξ rfl
  rw [htail]
  funext i
  rfl

end

end HeavyTailedNoise
