/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogarithmicShiftBounds

/-! # Analytic continuation of squared affine-logarithmic fitting roots -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For real L and rational a,b,c, the affine-logarithmic fitting root is
aL+b log L+c. Signed b,c are permitted; applications use a positive leading
coefficient and a positive root. Its square is the alternative fitting family. -/
noncomputable def affineLogarithmicRoot (L : ℝ) (a b c : ℚ) : ℝ :=
  (a : ℝ) * L + (b : ℝ) * Real.log L + (c : ℝ)

/-- For 0 < L₁ ≤ L₂, nonnegative a and b ≥ -aL₁ make the fitting root
nondecreasing. Bound the logarithmic difference by its tangent at L₁ and
multiply only nonnegative quantities. This also applies to differences of roots. -/
theorem affineLogarithmicRoot_le_of_le {L₁ L₂ : ℝ} {a b c : ℚ} (ha : 0 ≤ a) (hL : 0 < L₁)
    (horder : L₁ ≤ L₂) (hb : -(a : ℝ) * L₁ ≤ (b : ℝ)) :
    affineLogarithmicRoot L₁ a b c ≤ affineLogarithmicRoot L₂ a b c := by
  have hL₂ : 0 < L₂ := hL.trans_le horder
  have hlog := Real.log_le_log hL horder
  have hd : 0 ≤ Real.log L₂ - Real.log L₁ := sub_nonneg.mpr hlog
  have ht := Real.log_le_sub_one_of_pos (div_pos hL₂ hL)
  rw [Real.log_div hL₂.ne' hL.ne'] at ht
  have hmul := mul_le_mul_of_nonneg_right ht hL.le
  have he : (L₂ / L₁ - 1) * L₁ = L₂ - L₁ := by rw [sub_mul, div_mul_cancel₀ _ hL.ne', one_mul]
  rw [he] at hmul
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hs := mul_le_mul_of_nonneg_left hmul haR
  have hbmul := mul_le_mul_of_nonneg_right hb hd
  dsimp only [affineLogarithmicRoot]
  nlinarith only [hs, hbmul]

/-- Subtracting the rational linear slope r from a root changes a to a-r.
Expand the rational cast and use the polynomial identity. This expresses a
comparison with rL as monotonicity of another affine-logarithmic root. -/
theorem affineLogarithmicRoot_sub_slope (L : ℝ) (a b c r : ℚ) :
    affineLogarithmicRoot L (a - r) b c = affineLogarithmicRoot L a b c - (r : ℝ) * L := by
  simp only [affineLogarithmicRoot, Rat.cast_sub]
  ring

/-- If a ≥ r, b ≥ -(a-r)L₀ and the fitting root is at least rL₀ at L₀ > 0,
it is at least rL at every L ≥ L₀. Apply monotonicity to the difference root.
This supplies an analytic continuation criterion beyond a finite fitting interval. -/
theorem affineLogarithmicRoot_ge_linear_on_tail {L₀ L : ℝ} {a b c r : ℚ} (ha : r ≤ a) (hL₀ : 0 < L₀)
    (horder : L₀ ≤ L) (hb : -((a - r : ℚ) : ℝ) * L₀ ≤ (b : ℝ))
    (hbase : (r : ℝ) * L₀ ≤ affineLogarithmicRoot L₀ a b c) :
    (r : ℝ) * L ≤ affineLogarithmicRoot L a b c := by
  have hm := affineLogarithmicRoot_le_of_le (c := c) (sub_nonneg.mpr ha) hL₀ horder hb
  rw [affineLogarithmicRoot_sub_slope, affineLogarithmicRoot_sub_slope] at hm
  linarith only [hm, hbase]

/-- Under the root continuation conditions and r ≥ 0, the squared fitting root
dominates r²L² for every L ≥ L₀. Both roots are nonnegative, so squaring preserves
the comparison. Existing witness bounds may be transferred through this inequality. -/
theorem affineLogarithmicSquare_ge_linear_square_on_tail {L₀ L : ℝ} {a b c r : ℚ} (hr : 0 ≤ r)
    (ha : r ≤ a) (hL₀ : 0 < L₀) (horder : L₀ ≤ L) (hb : -((a - r : ℚ) : ℝ) * L₀ ≤ (b : ℝ))
    (hbase : (r : ℝ) * L₀ ≤ affineLogarithmicRoot L₀ a b c) :
    (r : ℝ) ^ 2 * L ^ 2 ≤ affineLogarithmicRoot L a b c ^ 2 := by
  have hroot := affineLogarithmicRoot_ge_linear_on_tail ha hL₀ horder hb hbase
  have hrR : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have hl : 0 ≤ (r : ℝ) * L := mul_nonneg hrR (hL₀.le.trans horder)
  simpa only [mul_pow] using (sq_le_sq₀ hl (hl.trans hroot)).mpr hroot

end PseudoPrime.Analysis
