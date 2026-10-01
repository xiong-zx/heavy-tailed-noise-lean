import HeavyTailedNoise.Upper.K1.StationarityActualPhysicalConditional

/-!
The first deterministic identity needed for the actual estimator-error
decomposition: its low clip and all high shells telescope to the terminal
clip. The source-mean and runtime-error identities are added only after this
small algebraic base has compiled.
-/

namespace HeavyTailedNoise.UpperK1

open scoped BigOperators

noncomputable section

private theorem fin_shell_telescope {d n : ℕ}
    (f : Fin (n + 1) → Point d) :
    f 0 + ∑ j : Fin n, (f j.succ - f j.castSucc) =
      f (Fin.last n) := by
  rw [Finset.sum_sub_distrib]
  have hsucc := Fin.sum_univ_succ f
  have hcast := Fin.sum_univ_castSucc f
  calc
    f 0 + ((∑ j : Fin n, f j.succ) -
        (∑ j : Fin n, f j.castSucc)) =
        (∑ i : Fin (n + 1), f i) -
          (∑ j : Fin n, f j.castSucc) := by rw [hsucc]; abel
    _ = f (Fin.last n) := by rw [hcast]; abel

/-- The exact finite clipping telescope, including `J=0` and the `q=1`
branch where all bands still exist but have unit EMA weight. -/
theorem lowBand_add_highBands_eq_terminalClip {q : ℝ}
    (P : Schedule q) {d : ℕ} (z : Point d) :
    lowBand P z + ∑ j : Fin P.J, highBand P j z =
      upperClip (P.tau (Fin.last P.J)) z := by
  change upperClip (P.tau 0) z +
      ∑ j : Fin P.J,
        (upperClip (P.tau j.succ) z -
          upperClip (P.tau j.castSucc) z) = _
  exact fin_shell_telescope (fun i : Fin (P.J + 1) =>
    upperClip (P.tau i) z)

end

end HeavyTailedNoise.UpperK1
