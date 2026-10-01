import HeavyTailedNoise.Upper.K1.BudgetCeilings
import HeavyTailedNoise.Upper.K1.BudgetPowers

/-!
The exact fixed response cap of `alg:k1`, with integer ceilings already
absorbed and both powers converted to the two manuscript rate terms. The
remaining scalar absorption into one `C(p,q)` is a separate theorem.
-/

namespace HeavyTailedNoise.UpperK1

noncomputable section

theorem paperSchedule_responseCount_le_rate_envelope
    (p q Δ σ Lbar ε Ctail ch κ Cb CI : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hq : 1 ≤ q)
    (hε : 0 < ε) (hCtail : 12 ≤ Ctail)
    (hch : 0 < ch) (hCb : 0 < Cb) (hCI : 0 < CI) :
    (responseCount (paperSchedule p q Δ σ Lbar ε Ctail ch κ Cb CI
      hε hch hCb hCI) : ℝ) ≤
      1 + (CI * (2 * Ctail) ^ (paperA p) *
        (paperS σ ε) ^ (p / (p - 1)) + 1) +
      (4 * paperAplus Lbar Δ ε / ch + 1) *
        (Cb * (2 * Ctail) ^ (paperEplus p q) *
          (paperS σ ε) ^ (max 2 ((p / (p - 1)) / q)) + 1) := by
  have hbase := paperSchedule_responseCount_real_le
    p q Δ σ Lbar ε Ctail ch κ Cb CI hε hch hCb hCI
  have hI := paper_initial_power_le_rate p σ ε Ctail
    hp hp2 hε hCtail
  have hR := paper_runtime_power_le_rate p q σ ε Ctail
    hp (by linarith : 0 < q) hε hCtail
  have hI' : CI * (paperS σ ε) ^ 2 *
      (paperU p σ ε Ctail) ^ (paperA p) ≤
      CI * (2 * Ctail) ^ (paperA p) *
        (paperS σ ε) ^ (p / (p - 1)) := by
    calc
      CI * (paperS σ ε) ^ 2 *
          (paperU p σ ε Ctail) ^ (paperA p) =
        CI * ((paperS σ ε) ^ 2 *
          (paperU p σ ε Ctail) ^ (paperA p)) := by ring
      _ ≤ CI * ((2 * Ctail) ^ (paperA p) *
          (paperS σ ε) ^ (p / (p - 1))) :=
        mul_le_mul_of_nonneg_left hI hCI.le
      _ = CI * (2 * Ctail) ^ (paperA p) *
          (paperS σ ε) ^ (p / (p - 1)) := by ring
  have hR' : Cb * (paperS σ ε) ^ 2 *
      (paperU p σ ε Ctail) ^ (paperEplus p q) ≤
      Cb * (2 * Ctail) ^ (paperEplus p q) *
        (paperS σ ε) ^ (max 2 ((p / (p - 1)) / q)) := by
    calc
      Cb * (paperS σ ε) ^ 2 *
          (paperU p σ ε Ctail) ^ (paperEplus p q) =
        Cb * ((paperS σ ε) ^ 2 *
          (paperU p σ ε Ctail) ^ (paperEplus p q)) := by ring
      _ ≤ Cb * ((2 * Ctail) ^ (paperEplus p q) *
          (paperS σ ε) ^ (max 2 ((p / (p - 1)) / q))) :=
        mul_le_mul_of_nonneg_left hR hCb.le
      _ = Cb * (2 * Ctail) ^ (paperEplus p q) *
          (paperS σ ε) ^ (max 2 ((p / (p - 1)) / q)) := by ring
  have hA : 0 ≤ paperAplus Lbar Δ ε :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 _)
  have hT : 0 ≤ 4 * paperAplus Lbar Δ ε / ch + 1 := by
    positivity
  have hprod := mul_le_mul_of_nonneg_left (add_le_add_right hR' 1) hT
  linarith

end

end HeavyTailedNoise.UpperK1
