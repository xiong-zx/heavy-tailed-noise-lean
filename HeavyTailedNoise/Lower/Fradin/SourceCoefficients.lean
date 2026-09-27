import HeavyTailedNoise.Lower.Fradin.Parameters

/-! The simultaneous coefficient equations in Fradin v2 C.3. This purely
numerical witness checks the deferred-coefficient logic independently of an
algorithm or an oracle realization. Oracle legality is proved separately. -/

namespace HeavyTailedNoise.Fradin
noncomputable section
set_option autoImplicit false

/-- Once θ is fixed, choose L, then β, then α. All three constraints hold
simultaneously; there is no circular dependence on an algorithm or sample. -/
theorem source_coefficient_realization {ℓ C Lbar ε θ q : ℝ}
    (hℓ : 0 < ℓ) (hC : 0 < C) (hL : 0 < Lbar) (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ L β α : ℝ, 0 < L ∧ 0 < β ∧ 0 < α ∧
      L = (ℓ*Lbar/C)*θ^((q-1)/q) ∧
      β = L/(2*ℓ*ε) ∧ α = L/(β^2*ℓ) ∧
      α*β = 2*ε ∧ α*β^2*ℓ = L ∧
      α*β^2*C/θ^((q-1)/q) = Lbar := by
  let t := θ^((q-1)/q)
  have ht : 0 < t := Real.rpow_pos_of_pos hθ _
  let L := (ℓ*Lbar/C)*t
  have hLp : 0 < L := mul_pos (div_pos (mul_pos hℓ hL) hC) ht
  let β := L/(2*ℓ*ε)
  have hβ : 0 < β := div_pos hLp (by positivity)
  let α := L/(β^2*ℓ)
  have hα : 0 < α := div_pos hLp (mul_pos (sq_pos_of_pos hβ) hℓ)
  refine ⟨L, β, α, hLp, hβ, hα, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · dsimp [α, β]
    field_simp [hLp.ne', hℓ.ne', hε.ne']
    <;> ring
  · dsimp [α]
    field_simp [hβ.ne', hℓ.ne']
  · change α*β^2*C/t = Lbar
    dsimp [α, β, L]
    field_simp [hℓ.ne', hC.ne', hε.ne', ht.ne']
    <;> ring

end
end HeavyTailedNoise.Fradin
