/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EarlyGaussianWitness

/-! # Shape of the early adaptive Gaussian bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The adaptive Gaussian slope is nonincreasing from its early entrance, since both
correction terms decrease with the logarithmic scale. -/
theorem earlyGaussian_slope_anti {L M : ℝ} (hL : 30000000000 ≤ L) (hLM : L ≤ M) :
    adaptiveGaussianA M ≤ adaptiveGaussianA L := by
  have hL0 : 0 < L := by linarith only [hL]
  have hs : Real.sqrt L ≤ Real.sqrt M := Real.sqrt_le_sqrt hLM
  have h1 : (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt M ≤
      (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L :=
    div_le_div_of_nonneg_left (by norm_num only) (Real.sqrt_pos.2 hL0) hs
  have h2 : (39 : ℝ) / M ≤ 39 / L :=
    div_le_div_of_nonneg_left (by norm_num only) hL0 hLM
  dsimp only [adaptiveGaussianA]
  apply (div_le_div_iff_of_pos_right (by norm_num only)).2
  linarith only [h1, h2]
/-- The normalized Gaussian coefficient is nonincreasing from its early entrance.
The slope is positive and its square preserves the slope comparison. -/
theorem earlyGaussian_coeff_anti {L M : ℝ} (hL : 30000000000 ≤ L) (hLM : L ≤ M) :
    (21 / 10 : ℝ) * adaptiveGaussianA M ^ 2 ≤
      (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2 := by
  have hM : 30000000000 ≤ M := hL.trans hLM
  have hp : 0 ≤ adaptiveGaussianA M := by
    have h := earlyGaussian_slope_lower M hM
    linarith only [h]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp (earlyGaussian_slope_anti hL hLM) 2)
    (by norm_num only)
/-- The Gaussian slope times the scale is nondecreasing from the early entrance.
After multiplication the correction terms become a square root and a constant. -/
theorem earlyGaussian_scaled_mono {L M : ℝ} (hL : 30000000000 ≤ L) (hLM : L ≤ M) :
    adaptiveGaussianA L * L ≤ adaptiveGaussianA M * M := by
  have hl : 0 < L := by linarith only [hL]
  have hm : 0 < M := by linarith only [hL, hLM]
  have hs : Real.sqrt L ≤ Real.sqrt M := Real.sqrt_le_sqrt hLM
  have he (x : ℝ) (hx : 0 < x) :
    adaptiveGaussianA x * x =
      (2 * (20115621 / 50000000) * x + (61 / 100) * (28794111 / 12500000) * Real.sqrt x + 39) /
        (10971611 / 5000000) := by
    have hp : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    dsimp only [adaptiveGaussianA]
    field_simp [hx.ne', hp.ne']
    nlinarith only [Real.sq_sqrt hx.le]
  rw [he L hl, he M hm]
  apply (div_le_div_iff_of_pos_right (by norm_num only)).2
  nlinarith only [hLM, hs]



end PseudoPrime.PrimeTestBounds.MillerRabin
