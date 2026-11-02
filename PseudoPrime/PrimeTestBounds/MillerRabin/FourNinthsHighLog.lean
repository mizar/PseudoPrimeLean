/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighCounting
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Uniform logarithmic estimates for the high range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `L ≥ 1024`, twice its logarithm is strictly below `L / 64`.
Write `L = 1024 * r`, use `log r ≤ r - 1`, and bound `log 1024` by 7.
This supplies the high-range ceiling and product-size budgets. -/
theorem high_two_log_lt_linear {L : ℝ} (hL : 1024 ≤ L) : 2 * Real.log L < L / 64 := by
  have hlog : Real.log (1024 : ℝ) < 7 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have hr : (1 : ℝ) ≤ L / 1024 := by linarith only [hL]
  have hrpos : 0 < L / 1024 := by linarith only [hr]
  have ht := Real.log_le_sub_one_of_pos hrpos
  have he : Real.log L = Real.log (L / 1024) + Real.log 1024 := by
    rw [← Real.log_mul hrpos.ne' (by norm_num only : (1024 : ℝ) ≠ 0)]
    congr 1
    ring
  linarith only [hlog, hr, ht, he]

/-- For `L ≥ 1024`, twice its logarithm is below
`14 * sqrt (L / 1024)`. Apply the tangent logarithm bound at the square root
of `L / 1024`; this supplies the high-range quadratic error comparison. -/
theorem high_two_log_lt_sqrt {L : ℝ} (hL : 1024 ≤ L) :
    2 * Real.log L < 14 * Real.sqrt (L / 1024) := by
  have hlog : Real.log (1024 : ℝ) < 7 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have hr : (1 : ℝ) ≤ L / 1024 := by linarith only [hL]
  have hrpos : 0 < L / 1024 := by linarith only [hr]
  have hs : 1 ≤ Real.sqrt (L / 1024) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr
  have ht := Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hs)
  have hslog := Real.log_sqrt hrpos.le
  have he : Real.log L = Real.log (L / 1024) + Real.log 1024 := by
    rw [← Real.log_mul hrpos.ne' (by norm_num only : (1024 : ℝ) ≠ 0)]
    congr 1
    ring
  linarith only [hlog, hs, ht, hslog, he]

/-- For the chosen high-range floor radius, twice its logarithm is below both
`L / 64` and `14 * sqrt (L / 1024)`. The radius is positive and at most `L`,
so logarithm monotonicity transfers the two bounds from `L` to the radius. -/
theorem high_floor_two_log_bounds {L : ℝ} (hL : 1024 ≤ L) :
    2 * Real.log (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) < L / 64 ∧
      2 * Real.log (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) < 14 * Real.sqrt (L / 1024) := by
  have hlo := (high_radius_floor_lower hL).2.1
  have hb : 0 < (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) := by linarith only [hL, hlo]
  have hx : 0 ≤ (2 / 3 : ℝ) * L := by linarith only [hL]
  have hf := Nat.floor_le hx
  have hle : (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) ≤ L := by linarith only [hL, hf]
  have hlog := Real.log_le_log hb hle
  constructor
  · linarith only [hlog, high_two_log_lt_linear hL]
  · linarith only [hlog, high_two_log_lt_sqrt hL]

/-- For `L ≥ 1024`, a nonnegative `u ≤ 14 * sqrt (L / 1024)` satisfies
`u ^ 2 + (3 / 10) * u < L / 5`. Bound the square root by `L / 1024`
and square the bound for `u`. This is the high-range kernel-size margin. -/
theorem high_log_quadratic_margin {L u : ℝ} (hL : 1024 ≤ L) (hu0 : 0 ≤ u)
    (hu : u ≤ 14 * Real.sqrt (L / 1024)) : u ^ 2 + (3 / 10 : ℝ) * u < L / 5 := by
  have hr : (1 : ℝ) ≤ L / 1024 := by linarith only [hL]
  have hs0 := Real.sqrt_nonneg (L / 1024)
  have hs2 := Real.sq_sqrt (show 0 ≤ L / 1024 by linarith only [hr])
  have hs1 : 1 ≤ Real.sqrt (L / 1024) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr
  have hsr : Real.sqrt (L / 1024) ≤ L / 1024 := by nlinarith only [hs0, hs1, hs2]
  have hu2 := pow_le_pow_left₀ hu0 hu 2
  nlinarith only [hL, hu, hu2, hs2, hsr]

/-- The chosen floor radius satisfies the high-range quadratic logarithmic
margin. Its logarithm is nonnegative because the radius is at least one, and
the preceding square-root bound supplies the general margin hypothesis. -/
theorem high_floor_log_quadratic_margin {L : ℝ} (hL : 1024 ≤ L) :
    (2 * Real.log (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ)) ^ 2 +
        (3 / 10 : ℝ) * (2 * Real.log (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ)) <
      L / 5 := by
  have hb : (1 : ℝ) ≤ (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) := by
    have hf := (high_radius_floor_lower hL).2.1
    linarith only [hL, hf]
  have hu : 0 ≤ 2 * Real.log (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) := by
    exact mul_nonneg (by norm_num only) (Real.log_nonneg hb)
  exact high_log_quadratic_margin hL hu (high_floor_two_log_bounds hL).2.le

end PseudoPrime.PrimeTestBounds.MillerRabin
