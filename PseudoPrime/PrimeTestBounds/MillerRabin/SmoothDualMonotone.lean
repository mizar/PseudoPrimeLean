/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SmoothDualEnvelope
/-! # Monotonicity of the continuous cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- A logarithm increment is bounded by its linear secant. -/
theorem smooth_log_delta {L M : ℝ} (hL : 0 < L) (hLM : L ≤ M) :
    L * (Real.log M - Real.log L) ≤ M - L := by
  have hM : 0 < M := hL.trans_le hLM
  have ht := Real.log_le_sub_one_of_pos (div_pos hM hL)
  rw [Real.log_div hM.ne' hL.ne'] at ht
  have ht' := mul_le_mul_of_nonneg_right ht hL.le
  have he : (M / L - 1) * L = M - L := by
    rw [sub_mul, div_mul_cancel₀ _ hL.ne', one_mul]
  rw [he] at ht'
  nlinarith only [ht']
/-- The scaled dual shift is nondecreasing at positive scales. -/
theorem smoothDual_shift_scaled {L M : ℝ} (hL : 0 < L) (hLM : L ≤ M) :
    smoothDual_shift L * L ≤ smoothDual_shift M * M := by
  have hM : 0 < M := hL.trans_le hLM
  have hdelta := smooth_log_delta hL hLM
  have hlog := Real.log_le_log hL hLM
  let p := max 0 (36 + Real.log 4 - 2 * Real.log L)
  let q := max 0 (36 + Real.log 4 - 2 * Real.log M)
  have hq : 0 ≤ q := le_max_left _ _
  have hp : p ≤ q + 2 * (Real.log M - Real.log L) := by
    dsimp only [p, q]
    apply max_le
    · have hq' : 0 ≤ max (0 : ℝ) (36 + Real.log 4 - 2 * Real.log M) := le_max_left _ _
      linarith only [hq', hlog]
    · have hq' : 36 + Real.log 4 - 2 * Real.log M ≤
          max (0 : ℝ) (36 + Real.log 4 - 2 * Real.log M) := le_max_right _ _
      linarith only [hq']
  have hpmul := mul_le_mul_of_nonneg_right hp hL.le
  have hqmul := mul_le_mul_of_nonneg_left hLM hq
  unfold smoothDual_shift
  change (36 + p) * L ≤ (36 + q) * M
  nlinarith only [hpmul, hqmul, hdelta, hLM]

/-- The dual radius times the scale is nondecreasing above the entrance. -/
theorem smoothDual_scaled_mono {L M : ℝ} (hL : 5000000 ≤ L) (hLM : L ≤ M) :
    smoothDual_radius L * L ≤ smoothDual_radius M * M := by
  have hL0 : 0 < L := by linarith only [hL]
  have hM0 : 0 < M := hL0.trans_le hLM
  have hs := Real.sqrt_le_sqrt hLM
  have hd := smoothDual_shift_scaled hL0 hLM
  have he (x : ℝ) (hx : 0 < x) :
      smoothDual_radius x * x =
        (smoothDual_shift x * x + (1456 + 13 / 10000000 : ℝ) * Real.sqrt x + 12066) /
          (68 - 3 / 10000) := by
    have hp : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    unfold smoothDual_radius
    have hxr : x / Real.sqrt x = Real.sqrt x := by
      apply (div_eq_iff hp.ne').2
      simpa only [pow_two] using (Real.sq_sqrt hx.le).symm
    have hterm : ((1456 + 13 / 10000000 : ℝ) / Real.sqrt x) * x =
        (1456 + 13 / 10000000 : ℝ) * Real.sqrt x := by
      rw [div_mul_eq_mul_div, mul_div_assoc, hxr]
    rw [div_mul_eq_mul_div, add_mul, add_mul, hterm, div_mul_cancel₀ _ hx.ne']
  rw [he L hL0, he M hM0]
  apply (div_le_div_iff_of_pos_right (by norm_num only)).2
  nlinarith only [hd, hs]
/-- The Gaussian radius times the scale is nondecreasing above the entrance. -/
theorem smoothGaussian_scaled_mono {L M : ℝ} (hL : 5000000 ≤ L) (hLM : L ≤ M) :
    smoothGaussian_radius L * L ≤ smoothGaussian_radius M * M := by
  have hL0 : 0 < L := by linarith only [hL]
  have hM0 : 0 < M := hL0.trans_le hLM
  have hs := Real.sqrt_le_sqrt hLM
  have he (x : ℝ) (hx : 0 < x) :
      smoothGaussian_radius x * x =
        ((161 / 200 : ℝ) * x + (238 / 5 : ℝ) * Real.sqrt x + 91) / (21943 / 10000) := by
    have hp : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    unfold smoothGaussian_radius
    have hxr : x / Real.sqrt x = Real.sqrt x := by
      apply (div_eq_iff hp.ne').2
      simpa only [pow_two] using (Real.sq_sqrt hx.le).symm
    have hterm : ((238 / 5 : ℝ) / Real.sqrt x) * x = (238 / 5 : ℝ) * Real.sqrt x := by
      rw [div_mul_eq_mul_div, mul_div_assoc, hxr]
    rw [div_mul_eq_mul_div, add_mul, add_mul, hterm, div_mul_cancel₀ _ hx.ne']
  rw [he L hL0, he M hM0]
  apply (div_le_div_iff_of_pos_right (by norm_num only)).2
  nlinarith only [hs, hLM]
/-- The continuous cutoff itself is nondecreasing above the entrance. -/
theorem smoothCutoff_mono {L M : ℝ} (hL : 5000000 ≤ L) (hLM : L ≤ M) :
    smoothCoeff L * L ^ 2 ≤ smoothCoeff M * M ^ 2 := by
  have ha0 : 0 ≤ smoothDual_radius L * L :=
    mul_nonneg (by linarith only [(smoothDual_radius_bounds L hL).1]) (by linarith only [hL])
  have hb0 : 0 ≤ smoothGaussian_radius L * L :=
    mul_nonneg (smoothGaussian_radius_pos L hL).le (by linarith only [hL])
  have ha := pow_le_pow_left₀ ha0 (smoothDual_scaled_mono hL hLM) 2
  have hb := pow_le_pow_left₀ hb0 (smoothGaussian_scaled_mono hL hLM) 2
  unfold smoothCoeff
  rw [max_mul_of_nonneg _ _ (sq_nonneg _), max_mul_of_nonneg _ _ (sq_nonneg _)]
  apply max_le_max
  · simpa only [mul_pow] using ha
  · have h := mul_le_mul_of_nonneg_left hb (by norm_num only : (0 : ℝ) ≤ 21 / 10)
    simpa only [mul_pow, mul_assoc] using h
end PseudoPrime.PrimeTestBounds.MillerRabin
