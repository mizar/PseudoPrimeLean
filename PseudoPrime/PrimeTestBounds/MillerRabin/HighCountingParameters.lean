/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighRadiusLogBounds

/-! # High-range floor and ceiling parameter comparisons -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `L ≥ 1024` and `0 < σ ≤ 1`, the high-range exponent chosen by a
ceiling minus one is at most the floor of the prime supply. The floor radius
is at least `L / 2`, so its quadratic supply exceeds `σ * L`; dividing by
the positive logarithmic scale allows the floor-ceiling comparison. -/
theorem high_exponent_le_supply {L σ : ℝ} (hL : 1024 ≤ L) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ⌈σ * L / (2 * Real.log (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ))⌉₊ - 1 ≤
      ⌊((9 / 10 : ℝ) * (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) ^ 2) /
          (2 * Real.log (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ))⌋₊ := by
  let b : ℝ := (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ)
  have hb : L / 2 ≤ b := (high_radius_floor_lower hL).2.1
  have hb1 : 1 < b := by linarith only [hL, hb]
  have hu : 0 < 2 * Real.log b := mul_pos (by norm_num only) (Real.log_pos hb1)
  have hL0 : 0 < L := by linarith only [hL]
  have hs := pow_le_pow_left₀ (show (0 : ℝ) ≤ L / 2 by linarith only [hL]) hb 2
  have hlin : σ * L ≤ L := by nlinarith only [mul_nonneg (sub_nonneg.mpr hσ1) hL0.le]
  have hquad : L < (9 / 10 : ℝ) * b ^ 2 := by nlinarith only [hL, hs, sq_nonneg (L - 1024)]
  apply ceil_sub_one_le_floor (div_pos (mul_pos hσ0 hL0) hu)
  exact (div_lt_div_iff_of_pos_right hu).2 (hlin.trans_lt hquad)

/-- For `L ≥ 1024` and `σ ≥ 2 / 3`, the high-range ceiling-minus-one
exponent is positive. The logarithmic scale is positive and below `L / 64`,
so the quotient exceeds two before taking the ceiling. -/
theorem high_exponent_pos {L σ : ℝ} (hL : 1024 ≤ L) (hσ : (2 / 3 : ℝ) ≤ σ) :
    0 < ⌈σ * L / (2 * Real.log (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ))⌉₊ - 1 := by
  let u := 2 * Real.log (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ)
  have hb := (high_radius_floor_lower hL).2.1
  have hb1 : 1 < (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) := by linarith only [hL, hb]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb1)
  have huL : u < L / 64 := (high_floor_two_log_bounds hL).1
  have hL0 : 0 < L := by linarith only [hL]
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hy : 0 < σ * L / u := div_pos (mul_pos hσ0 hL0) hu
  have hmul : (2 / 3 : ℝ) * L ≤ σ * L := mul_le_mul_of_nonneg_right hσ hL0.le
  have hratio : (2 : ℝ) < σ * L / u := by
    apply (lt_div_iff₀ hu).2
    linarith only [hL, huL, hmul]
  have hk := (ceil_sub_one_bounds hy).1
  have hkpos : (0 : ℝ) < ((⌈σ * L / u⌉₊ - 1 : ℕ) : ℝ) := by linarith only [hratio, hk]
  exact_mod_cast hkpos

end PseudoPrime.PrimeTestBounds.MillerRabin
