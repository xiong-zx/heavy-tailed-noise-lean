import HeavyTailedNoise.Upper.K1.StationarityActualErrorDecomposition
import HeavyTailedNoise.Upper.K1.KernelBatch

/-!
The clipping telescope commutes with the single auxiliary-source mean. It
uses boundedness of each transformed residual and the original oracle law;
there is no extra response, independence assumption, or raw second moment.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {q : ℝ} (P : Schedule q)

theorem lowSourceMean_add_highSourceMeans_eq_terminalClip
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (O : GradientOracle d Seed) (x w : Point d) :
    upperResidualSourceMean O (lowBand P) x w +
      ∑ j : Fin P.J,
        upperResidualSourceMean O (highBand P j) x w =
      upperResidualSourceMean O
        (upperClip (P.tau (Fin.last P.J))) x w := by
  let R : Seed → Point d := fun ξ => O.response x ξ - w
  have hlow : Integrable (fun ξ => lowBand P (R ξ)) O.law :=
    upperResidualSource_integrable O (lowBand P)
      (measurable_lowBand P)
      (P.tau ⟨0, Nat.zero_lt_succ P.J⟩)
      (fun z => upperClip_norm_le
        (P.tau_pos ⟨0, Nat.zero_lt_succ P.J⟩) z) x w
  have hhigh (j : Fin P.J) :
      Integrable (fun ξ => highBand P j (R ξ)) O.law :=
    upperResidualSource_integrable O (highBand P j)
      (measurable_highBand P j)
      (P.tau j.succ + P.tau j.castSucc)
      (highBand_norm_le P j) x w
  have hsum : Integrable
      (fun ξ => ∑ j : Fin P.J, highBand P j (R ξ)) O.law := by
    apply integrable_finset_sum
    intro j hj
    exact hhigh j
  change (∫ ξ, lowBand P (R ξ) ∂O.law) +
      (∑ j : Fin P.J, ∫ ξ, highBand P j (R ξ) ∂O.law) =
    ∫ ξ, upperClip (P.tau (Fin.last P.J)) (R ξ) ∂O.law
  calc
    (∫ ξ, lowBand P (R ξ) ∂O.law) +
        (∑ j : Fin P.J, ∫ ξ, highBand P j (R ξ) ∂O.law) =
      (∫ ξ, lowBand P (R ξ) ∂O.law) +
        ∫ ξ, ∑ j : Fin P.J, highBand P j (R ξ) ∂O.law := by
          rw [integral_finsetSum]
          intro j hj
          exact hhigh j
    _ = ∫ ξ, lowBand P (R ξ) +
        ∑ j : Fin P.J, highBand P j (R ξ) ∂O.law := by
          exact (integral_add hlow hsum).symm
    _ = ∫ ξ, upperClip (P.tau (Fin.last P.J)) (R ξ) ∂O.law := by
          congr 1
          funext ξ
          exact lowBand_add_highBands_eq_terminalClip P (R ξ)

end

end HeavyTailedNoise.UpperK1
