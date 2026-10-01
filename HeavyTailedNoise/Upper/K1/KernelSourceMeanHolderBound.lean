import HeavyTailedNoise.Upper.K1.KernelSourceHolder

/-!
The terminal cutoff makes the mixed source-drift integrand integrable, while
the sharper untruncated envelope is controlled by same-seed Hölder.  The
maximum residual uses only endpoint `p` moments.  The increment uses the
oracle's same-seed `q` moment; no absolute residual `q` moment is assumed.
-/

namespace HeavyTailedNoise.UpperK1

open MeasureTheory

noncomputable section

private theorem capped_mix_le_uncapped
    {s ν U C R D : ℝ}
    (hs : 0 < s) (hν : 0 < ν) (hU : 0 ≤ U)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    2 * D * (C * (min (R / ν) U) ^ s) ≤
      (2 * C / ν ^ s) * (R ^ s * D) := by
  have hmin : 0 ≤ min (R / ν) U :=
    le_min (div_nonneg hR hν.le) hU
  have hpow := Real.rpow_le_rpow hmin (min_le_left _ _) hs.le
  calc
    2 * D * (C * (min (R / ν) U) ^ s) ≤
        2 * D * (C * (R / ν) ^ s) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow hC) (by positivity)
    _ = (2 * C / ν ^ s) * (R ^ s * D) := by
      rw [Real.div_rpow hR hν.le]
      ring

/-- The paper's capped mixed integrand is bounded by the untruncated
Hölder product.  Both endpoint residuals and their increment use one seed. -/
theorem paperSchedule_kernel_mix_integral_le_holder
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hε : 0 < ε) (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI)
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (I : Admissible d Seed p q Δ σ Lbar)
    (x x' w w' : Point d) :
    let s := paperSexp p q
    let ν := paperNu σ ε
    let U : ℝ := 12 * (2 : ℝ) ^ paperJ p σ ε Ctail
    let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
    let X : Seed → Point d := fun ξ => I.oracle.response x ξ - w
    let Y : Seed → Point d := fun ξ => I.oracle.response x' ξ - w'
    let R : Seed → ℝ := fun ξ => max ‖Y ξ‖ ‖X ξ‖
    let D : Seed → ℝ := fun ξ => ‖Y ξ - X ξ‖
    (∫ ξ, 2 * D ξ * (C * (min (R ξ / ν) U) ^ s) ∂I.oracle.law) ≤
      (2 * C / ν ^ s) *
        ((∫ ξ, ((R ξ) ^ s) ^ (q / (q - 1)) ∂I.oracle.law) ^
            (1 / (q / (q - 1))) *
          (∫ ξ, (D ξ) ^ q ∂I.oracle.law) ^ (1 / q)) := by
  dsimp only
  let s := paperSexp p q
  let ν := paperNu σ ε
  let U : ℝ := 12 * (2 : ℝ) ^ paperJ p σ ε Ctail
  let C : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
  let X : Seed → Point d := fun ξ => I.oracle.response x ξ - w
  let Y : Seed → Point d := fun ξ => I.oracle.response x' ξ - w'
  let R : Seed → ℝ := fun ξ => max ‖Y ξ‖ ‖X ξ‖
  let D : Seed → ℝ := fun ξ => ‖Y ξ - X ξ‖
  let K : ℝ := 2 * C / ν ^ s
  letI : IsProbabilityMeasure I.oracle.law := I.oracle.law_probability
  have hν : 0 < ν := paperNu_pos (σ := σ) hε
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hs : 0 < s := by
    dsimp [s, paperSexp]
    apply mul_pos (lt_trans zero_lt_one hp)
    apply sub_pos.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa using hq)
  have htwo : 1 < (2 : ℝ) ^ s :=
    Real.one_lt_rpow (by norm_num) hs
  have hC : 0 ≤ C := by
    dsimp [C]
    exact (div_pos (Real.rpow_pos_of_pos (by norm_num) s)
      (sub_pos.mpr htwo)).le
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hHolder : (q / (q - 1)).HolderConjugate q := by
    simpa only [Real.conjExponent] using
      (Real.HolderConjugate.conjExponent hq).symm
  letI : ENNReal.HolderTriple
      (ENNReal.ofReal (q / (q - 1))) (ENNReal.ofReal q) 1 :=
    hHolder.ennrealOfReal
  have hR : MemLp (fun ξ => (R ξ) ^ s)
      (ENNReal.ofReal (q / (q - 1))) I.oracle.law := by
    simpa only [R, X, Y, s] using
      (Admissible.same_seed_max_residual_rpow_memLp I hq x x' w w')
  have hD : MemLp (fun ξ => Y ξ - X ξ)
      (ENNReal.ofReal q) I.oracle.law := by
    simpa only [X, Y] using
      (Admissible.same_seed_residual_increment_memLp I x x' w w')
  have hProdInt : Integrable (fun ξ => (R ξ) ^ s * D ξ)
      I.oracle.law := by
    have h := hR.integrable_mul hD.norm
    change Integrable
      ((fun ξ => (R ξ) ^ s) * (fun ξ => ‖Y ξ - X ξ‖))
        I.oracle.law
    exact h
  have hMixInt : Integrable
      (fun ξ => 2 * D ξ * (C * (min (R ξ / ν) U) ^ s))
      I.oracle.law := by
    simpa only [D, R, X, Y, C, U, ν, s] using
      (paperSchedule_kernel_mix_integrable
        p q Δ σ Lbar ε Ctail ch κ Cb CI
        hp hq hε hch hCb hCI I x x' w w')
  have hpoint (ξ : Seed) :
      2 * D ξ * (C * (min (R ξ / ν) U) ^ s) ≤
        K * ((R ξ) ^ s * D ξ) := by
    have hRξ : 0 ≤ R ξ :=
      (norm_nonneg (Y ξ)).trans (le_max_left _ _)
    exact capped_mix_le_uncapped hs hν hU hC hRξ (norm_nonneg _)
  have hMixLe :
      (∫ ξ, 2 * D ξ * (C * (min (R ξ / ν) U) ^ s)
        ∂I.oracle.law) ≤
        K * (∫ ξ, (R ξ) ^ s * D ξ ∂I.oracle.law) := by
    calc
      _ ≤ ∫ ξ, K * ((R ξ) ^ s * D ξ) ∂I.oracle.law := by
        apply integral_mono hMixInt (hProdInt.const_mul K)
        exact hpoint
      _ = _ := by rw [integral_const_mul]
  have hH :
      (∫ ξ, (R ξ) ^ s * D ξ ∂I.oracle.law) ≤
        (∫ ξ, ((R ξ) ^ s) ^ (q / (q - 1)) ∂I.oracle.law) ^
            (1 / (q / (q - 1))) *
          (∫ ξ, (D ξ) ^ q ∂I.oracle.law) ^ (1 / q) := by
    simpa only [D, R, X, Y, s] using
      (Admissible.same_seed_residual_product_holder I hq x x' w w')
  calc
    (∫ ξ, 2 * D ξ * (C * (min (R ξ / ν) U) ^ s)
      ∂I.oracle.law) ≤
        K * (∫ ξ, (R ξ) ^ s * D ξ ∂I.oracle.law) := hMixLe
    _ ≤ K *
        ((∫ ξ, ((R ξ) ^ s) ^ (q / (q - 1)) ∂I.oracle.law) ^
            (1 / (q / (q - 1))) *
          (∫ ξ, (D ξ) ^ q ∂I.oracle.law) ^ (1 / q)) :=
      mul_le_mul_of_nonneg_left hH hK

end

end HeavyTailedNoise.UpperK1
