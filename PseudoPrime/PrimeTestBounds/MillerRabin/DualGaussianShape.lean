/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualGaussianWitness

/-! # Shape of the adaptive Gaussian bound from its new entrance -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Gaussian slope is nonincreasing after the new entrance. -/
theorem dualGaussian_slope_anti {L M : ℝ} (hL : 200000000 ≤ L) (hLM : L ≤ M) :
    adaptiveGaussianA M ≤ adaptiveGaussianA L := by
  have hL0 : 0 < L := by linarith only [hL]
  have hs : Real.sqrt L ≤ Real.sqrt M := Real.sqrt_le_sqrt hLM
  have h1 :
    (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt M ≤
      (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L :=
    div_le_div_of_nonneg_left (by norm_num only) (Real.sqrt_pos.2 hL0) hs
  have h2 : (39 : ℝ) / M ≤ 39 / L := div_le_div_of_nonneg_left (by norm_num only) hL0 hLM
  dsimp only [adaptiveGaussianA]
  apply (div_le_div_iff_of_pos_right (by norm_num only)).2
  linarith only [h1, h2]

/-- The normalized Gaussian coefficient is nonincreasing after the new entrance. -/
theorem dualGaussian_coeff_anti {L M : ℝ} (hL : 200000000 ≤ L) (hLM : L ≤ M) :
    (21 / 10 : ℝ) * adaptiveGaussianA M ^ 2 ≤ (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2 := by
  have hM : 200000000 ≤ M := hL.trans hLM
  have hp : 0 ≤ adaptiveGaussianA M := by
    have h := dualGaussian_slope_lower M hM
    linarith only [h]
  exact
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp (dualGaussian_slope_anti hL hLM) 2)
      (by norm_num only)

/-- The Gaussian slope times the scale is nondecreasing after the new entrance. -/
theorem dualGaussian_scaled_mono {L M : ℝ} (hL : 200000000 ≤ L) (hLM : L ≤ M) :
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
    have hxr : x / Real.sqrt x = Real.sqrt x := by
      apply (div_eq_iff hp.ne').2
      simpa only [pow_two] using (Real.sq_sqrt hx.le).symm
    have hterm :
      (((61 / 100 : ℝ) * (28794111 / 12500000)) / Real.sqrt x) * x =
        ((61 / 100 : ℝ) * (28794111 / 12500000)) * Real.sqrt x := by
      rw [div_mul_eq_mul_div, mul_div_assoc, hxr]
    rw [div_mul_eq_mul_div, add_mul, add_mul, hterm, div_mul_cancel₀ _ hx.ne']
  rw [he L hl, he M hm]
  apply (div_le_div_iff_of_pos_right (by norm_num only)).2
  nlinarith only [hLM, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
