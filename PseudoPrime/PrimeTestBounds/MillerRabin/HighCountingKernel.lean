/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCountingRatio

/-! # Uniform high-range binomial kernel budget -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For all `L ≥ 1024` and `2 / 3 ≤ σ ≤ 1`, the specified high-range
binomial count exceeds `exp (σ * L / 2)`. The radius and floor-ceiling choices
give a positive paired base, the ratio logarithm has a fixed margin, and the
quadratic logarithmic bound makes the selected exponent exceed the kernel budget.
No finite grid of values of `L` is used. -/
theorem high_selected_choose_gt_exp {L σ : ℝ} (hL : 1024 ≤ L) (hσ : (2 / 3 : ℝ) ≤ σ) (hσ1 : σ ≤ 1) :
    let b : ℝ := (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ)
    let u := 2 * Real.log b
    let M := ⌊((9 / 10 : ℝ) * b ^ 2) / u⌋₊
    let k := ⌈σ * L / u⌉₊ - 1
    Real.exp (σ * L / 2) < (Nat.choose M k : ℝ) := by
  dsimp only
  let b : ℝ := (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ)
  let u := 2 * Real.log b
  let M := ⌊((9 / 10 : ℝ) * b ^ 2) / u⌋₊
  let k := ⌈σ * L / u⌉₊ - 1
  let R : ℝ := 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1)
  have hb : 1 < b := by
    have hf := (high_radius_floor_lower hL).2.1
    linarith only [hL, hf]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb)
  have hLpos : 0 < L := by linarith only [hL]
  have hσpos : 0 < σ := by linarith only [hσ]
  have hy : 0 < σ * L / u := div_pos (mul_pos hσpos hLpos) hu
  have hk := (ceil_sub_one_bounds hy).1
  have hm : u ^ 2 + (3 / 10 : ℝ) * u < L / 5 := high_floor_log_quadratic_margin hL
  have hscalar := high_kernel_scalar_budget hLpos hσ hu hm hk
  have hlog : u / 2 + 3 / 20 < Real.log R := high_selected_ratio_log hL hσpos hσ1
  have hkpos : 0 < k := high_exponent_pos hL hσ
  have hmul := mul_lt_mul_of_pos_left hlog (Nat.cast_pos.mpr hkpos)
  have hbudget : σ * L / 2 < (k : ℝ) * Real.log R := hscalar.trans hmul
  have hRpos : 0 < R :=
    (mul_pos (by norm_num only : (0 : ℝ) < 7 / 6)
          (lt_trans (by norm_num only : (0 : ℝ) < 1) hb)).trans
      (high_selected_ratio_lower hL hσpos hσ1)
  exact exp_lt_choose_of_paired_budget M k hRpos hbudget

end PseudoPrime.PrimeTestBounds.MillerRabin
