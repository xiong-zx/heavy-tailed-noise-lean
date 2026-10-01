import HeavyTailedNoise.Upper.K1.SharedKernel
import HeavyTailedNoise.Upper.Foundations.ClippedBatch

/-!
One deterministic shared-source kernel is applied to each fresh response as a
whole.  The finite bound here permits conditional batch integration without
assuming independence among the clipping bands of that response.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

/-- A deliberately coarse but finite bound for the exact combined lag kernel. -/
def kernelPhiBound (k : ℕ) : ℝ :=
  P.tau ⟨0, Nat.zero_lt_succ P.J⟩ +
    ∑ j : Fin P.J,
      |P.alpha j * (1 - P.alpha j) ^ k| *
        (P.tau j.succ + P.tau j.castSucc)

theorem highBand_norm_le {d : ℕ} (j : Fin P.J) (z : Point d) :
    ‖highBand P j z‖ ≤ P.tau j.succ + P.tau j.castSucc := by
  unfold highBand upperShell
  calc
    ‖upperClip (P.tau j.succ) z - upperClip (P.tau j.castSucc) z‖ ≤
        ‖upperClip (P.tau j.succ) z‖ +
          ‖upperClip (P.tau j.castSucc) z‖ := norm_sub_le _ _
    _ ≤ P.tau j.succ + P.tau j.castSucc :=
      add_le_add (upperClip_norm_le (P.tau_pos j.succ) z)
        (upperClip_norm_le (P.tau_pos j.castSucc) z)

theorem kernelPsi_norm_le {d : ℕ} (k : ℕ) (z : Point d) :
    ‖kernelPsi P k z‖ ≤
      ∑ j : Fin P.J,
        |P.alpha j * (1 - P.alpha j) ^ k| *
          (P.tau j.succ + P.tau j.castSucc) := by
  unfold kernelPsi
  calc
    ‖∑ j : Fin P.J,
        (P.alpha j * (1 - P.alpha j) ^ k) • highBand P j z‖ ≤
        ∑ j : Fin P.J,
          ‖(P.alpha j * (1 - P.alpha j) ^ k) • highBand P j z‖ :=
            norm_sum_le _ _
    _ ≤ ∑ j : Fin P.J,
        |P.alpha j * (1 - P.alpha j) ^ k| *
          (P.tau j.succ + P.tau j.castSucc) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left
              (highBand_norm_le P j z) (abs_nonneg _)

theorem kernelPhi_norm_le {d : ℕ} (k : ℕ) (z : Point d) :
    ‖kernelPhi P k z‖ ≤ kernelPhiBound P k := by
  by_cases hk : k = 0
  · have hlow : ‖lowBand P z‖ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩ :=
      upperClip_norm_le (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩) z
    calc
      ‖kernelPhi P k z‖ = ‖lowBand P z + kernelPsi P k z‖ := by
        simp [kernelPhi, hk]
      _ ≤ ‖lowBand P z‖ + ‖kernelPsi P k z‖ := norm_add_le _ _
      _ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩ +
          ∑ j : Fin P.J,
            |P.alpha j * (1 - P.alpha j) ^ k| *
              (P.tau j.succ + P.tau j.castSucc) :=
                add_le_add hlow (kernelPsi_norm_le P k z)
      _ = kernelPhiBound P k := rfl
  · calc
      ‖kernelPhi P k z‖ = ‖kernelPsi P k z‖ := by
        simp [kernelPhi, hk]
      _ ≤ ∑ j : Fin P.J,
          |P.alpha j * (1 - P.alpha j) ^ k| *
            (P.tau j.succ + P.tau j.castSucc) := kernelPsi_norm_le P k z
      _ ≤ P.tau ⟨0, Nat.zero_lt_succ P.J⟩ +
          ∑ j : Fin P.J,
            |P.alpha j * (1 - P.alpha j) ^ k| *
              (P.tau j.succ + P.tau j.castSucc) :=
                le_add_of_nonneg_left
                  (le_of_lt (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩))
      _ = kernelPhiBound P k := rfl

@[simp] theorem highBand_zero_input {d : ℕ} (j : Fin P.J) :
    highBand P j (0 : Point d) = 0 := by
  simp [highBand, upperShell]

@[simp] theorem lowBand_zero_input {d : ℕ} :
    lowBand P (0 : Point d) = 0 := by
  simp [lowBand]

@[simp] theorem kernelPsi_zero_input {d : ℕ} (k : ℕ) :
    kernelPsi P k (0 : Point d) = 0 := by
  simp [kernelPsi]

@[simp] theorem kernelPhi_zero_input {d : ℕ} (k : ℕ) :
    kernelPhi P k (0 : Point d) = 0 := by
  by_cases hk : k = 0 <;> simp [kernelPhi, hk]

end

end HeavyTailedNoise.UpperK1
