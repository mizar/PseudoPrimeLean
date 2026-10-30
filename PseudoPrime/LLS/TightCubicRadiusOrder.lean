/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ParameterizedCubicSquareFactorRadius

/-! # Order of tight cubic conductor and exclusion radii -/

@[expose] public section
namespace PseudoPrime.LLS.PaperStatements
/-- For nonnegative G, increasing the conductor and exclusion budgets increases
or preserves the tight cubic radius. Compare its positive affine term, square
and radicand. This transports exact arithmetic data to coarser published envelopes. -/
theorem tightCubicRadius_mono {G G' E E' : ℝ} (hG : 0 ≤ G) (hGG : G ≤ G') (hEE : E ≤ E') :
    tightCubicExclusionRadius G E ≤ tightCubicExclusionRadius G' E' := by
  have hA : 0 ≤ (10 / 13 : ℝ) * G + 63 / 2 := by linarith only [hG]
  have hAA : (10 / 13 : ℝ) * G + 63 / 2 ≤ (10 / 13 : ℝ) * G' + 63 / 2 := by linarith only [hGG]
  have hs := pow_le_pow_left₀ hA hAA 2
  have hr := Real.sqrt_le_sqrt (by nlinarith only [hs,hGG,hEE] :
    ((10 / 13 : ℝ) * G + 63 / 2) ^ 2 + (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * E ≤
    ((10 / 13 : ℝ) * G' + 63 / 2) ^ 2 + (8 / 5 : ℝ) * G' + 28 + (4 / 3 : ℝ) * E')
  exact add_le_add hAA hr
/-- For nonnegative conductor and cost budgets, increasing either one strictly
while not decreasing the other strictly increases the tight cubic radius.
Use the affine term for a conductor saving and the square root for a cost saving.
This proves that exact quadratic data yield a strict improvement. -/
theorem tightCubicRadius_strict {G G' E E' : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E)
    (hGG : G ≤ G') (hEE : E ≤ E') (hstrict : G < G' ∨ E < E') :
    tightCubicExclusionRadius G E < tightCubicExclusionRadius G' E' := by
  have hA : 0 ≤ (10 / 13 : ℝ) * G + 63 / 2 := by linarith only [hG]
  have hAA : (10 / 13 : ℝ) * G + 63 / 2 ≤ (10 / 13 : ℝ) * G' + 63 / 2 := by linarith only [hGG]
  have hs := pow_le_pow_left₀ hA hAA 2
  rcases hstrict with hg | he
  · have hr := Real.sqrt_le_sqrt (by nlinarith only [hs,hGG,hEE] :
      ((10 / 13 : ℝ) * G + 63 / 2) ^ 2 + (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * E ≤
      ((10 / 13 : ℝ) * G' + 63 / 2) ^ 2 + (8 / 5 : ℝ) * G' + 28 + (4 / 3 : ℝ) * E')
    exact add_lt_add_of_lt_of_le (by linarith only [hg]) hr
  · have hr := Real.sqrt_lt_sqrt
      (by nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 63 / 2),hG,hE] :
        0 ≤ ((10 / 13 : ℝ) * G + 63 / 2) ^ 2 + (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * E)
      (by nlinarith only [hs,hGG,he] :
        ((10 / 13 : ℝ) * G + 63 / 2) ^ 2 + (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * E <
        ((10 / 13 : ℝ) * G' + 63 / 2) ^ 2 + (8 / 5 : ℝ) * G' + 28 + (4 / 3 : ℝ) * E')
    exact add_lt_add_of_le_of_lt hAA hr
end PseudoPrime.LLS.PaperStatements
