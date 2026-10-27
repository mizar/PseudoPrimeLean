/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! # Absorbing a factor two at a rational real-power threshold -/

public section

namespace PseudoPrime.Analysis

/-- For x≥8 and 2A≥3, x≤(x/2)^A. Compare squares and the cubic
power of x/2, then use monotonicity in the real exponent.
This transfers an explicit local threshold to a logarithmic witness bound. -/
theorem self_le_rpow_half_of_eight_le {x A : ℝ} (hx : 8 ≤ x) (hA : 3 ≤ 2 * A) :
    x ≤ (x / 2) ^ A := by
  have hx0 : 0 ≤ x := le_trans (by norm_num only) hx
  have hhalf : 1 ≤ x / 2 := by linarith only [hx]
  have hpoly := mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg x)
  have hcube : x ^ 2 ≤ (x / 2) ^ (3 : ℕ) := by nlinarith only [hpoly]
  have hc := Real.rpow_le_rpow_of_exponent_le hhalf hA
  have he : ((x / 2) ^ A) ^ (2 : ℕ) = (x / 2) ^ (2 * A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith only [hx0] : 0 ≤ x / 2)]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  rw [← he, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast] at hc
  exact
    (pow_le_pow_iff_left₀ hx0 (Real.rpow_nonneg (by linarith only [hx0]) A) (by decide : 2 ≠ 0)).mp
      (hcube.trans hc)

end PseudoPrime.Analysis
