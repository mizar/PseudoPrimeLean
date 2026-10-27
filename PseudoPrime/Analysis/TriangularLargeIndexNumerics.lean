/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Certified large-index alpha-18 numerical gap -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L >= 10^20 and x=(283/1000)L^2, the scale is above one,
sqrt x lies between L/2 and L, and x^(1/4) is at most L/10^6.
These power bounds reduce the explicit kernel error budgets to rational arithmetic. -/
theorem triangular18_large_scale_bounds {L : ℝ} (hL : (100000000000000000000 : ℝ) ≤ L) :
    let x := (283 / 1000 : ℝ) * L ^ 2;
    1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 := by
  let x := (283 / 1000 : ℝ) * L ^ 2
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hx : 1 < x := by
    dsimp only [x]
    nlinarith only [hL]
  have hs := Real.sq_sqrt (zero_lt_one.trans hx).le
  have hn := Real.sqrt_nonneg x
  have hl : L / 2 ≤ Real.sqrt x := by
    dsimp only [x] at hs
    nlinarith only [hs, hn, hLp]
  have hu : Real.sqrt x ≤ L := by
    dsimp only [x] at hs
    nlinarith only [hs, hn, hLp]
  have ht : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    have he := Real.rpow_mul (zero_lt_one.trans hx).le (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hpow :=
    mul_le_mul_of_nonneg_right
      ((by norm_num only : (1000000000000 : ℝ) ≤ 100000000000000000000).trans hL) hLp.le
  have hquarter : x ^ (1 / 4 : ℝ) ≤ L / 1000000 := by
    have hp := Real.rpow_nonneg (zero_lt_one.trans hx).le (1 / 4)
    nlinarith only [ht, hu, hpow, hp, hLp]
  exact ⟨hx, hl, hu, hquarter⟩

/-- For L >= 10^20 at the quadratic scale, the primitive additive costs
are at most L/1000 and the large-factor correction is at most 100.
Compare the negative exponent with inverse sqrt x and use the scale bounds. -/
theorem triangular18_large_scale_costs {L : ℝ} (hL : (100000000000000000000 : ℝ) ≤ L) :
    let x := (283 / 1000 : ℝ) * L ^ 2;
    (1350000000000000 + 55000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)) ≤ L / 1000 ∧
      36 * L / (Real.sqrt x - 1) ≤ 100 := by
  let x := (283 / 1000 : ℝ) * L ^ 2
  have h := triangular18_large_scale_bounds hL
  change 1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 at h
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (zero_lt_one.trans h.1)
  have hm : 0 ≤ 4000000000000 * (L + 284) := by nlinarith only [hLp]
  have hp := Real.rpow_le_rpow_of_exponent_le h.1.le (by norm_num only : (-9 / 16 : ℝ) ≤ -1 / 2)
  have he : x ^ (-1 / 2 : ℝ) = (Real.sqrt x)⁻¹ := by
    rw [neg_div, Real.rpow_neg (zero_lt_one.trans h.1).le, ← Real.sqrt_eq_rpow]
  rw [he] at hp
  have hb := mul_le_mul_of_nonneg_left hp hm
  have hR : 4000000000000 * (L + 284) / Real.sqrt x ≤ 10000000000000 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith only [h.2.1, hL]
  have ht : 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) ≤ 10000000000000 := by
    exact hb.trans (by simpa only [div_eq_mul_inv] using hR)
  have hC :
    1350000000000000 + 55000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) ≤ L / 1000 := by
    linarith only [ht, hL]
  have hd : 0 < Real.sqrt x - 1 := by linarith only [h.2.1, hL]
  have hB : 36 * L / (Real.sqrt x - 1) ≤ 100 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [h.2.1, hL]
  exact ⟨hC, hB⟩

/-- For L >= 10^20 at the quadratic scale, (677/10)sqrt x exceeds (3601/100)L.
The rational coefficient-0.283 squared margin supplies the strict inequality. -/
theorem triangular18_large_scale_main_margin {L : ℝ} (hL : (100000000000000000000 : ℝ) ≤ L) :
    (3601 / 100 : ℝ) * L < (677 / 10 : ℝ) * Real.sqrt ((283 / 1000 : ℝ) * L ^ 2) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hxp : 0 < (283 / 1000 : ℝ) * L ^ 2 := mul_pos (by norm_num only) (sq_pos_of_pos hLp)
  have hs := Real.sq_sqrt hxp.le
  have hn := Real.sqrt_nonneg ((283 / 1000 : ℝ) * L ^ 2)
  have hnum : (3601 / 100 : ℝ) ^ 2 < (283 / 1000 : ℝ) * (677 / 10 : ℝ) ^ 2 := by norm_num only
  have hscale := mul_lt_mul_of_pos_right hnum (sq_pos_of_pos hLp)
  nlinarith only [hscale, hs, hn, hLp]

/-- For L >= 10^20 and real subgroup index h >= 10^9, the actual explicit
alpha-18 large-factor budget has a strict numerical gap at x=(283/1000)L^2.
Absorb the principal term using the index, then apply the power and cost bounds.
This certificate removes the numerical-gap assumption from the large-index witness interface. -/
theorem triangular18_large_index_gap {L h : ℝ} (hL : (100000000000000000000 : ℝ) ≤ L)
    (hh : 1000000000 ≤ h) :
    let x := (283 / 1000 : ℝ) * L ^ 2;
    300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) +
        (h - 1) *
          (36 * L + 1350000000000000 + 55000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)) <
      h *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * L / (Real.sqrt x - 1)) := by
  let x := (283 / 1000 : ℝ) * L ^ 2
  let C := 1350000000000000 + 55000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hhp : 0 < h := lt_of_lt_of_le (by norm_num only) hh
  have hb := triangular18_large_scale_bounds hL
  change 1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 at hb
  have hc := triangular18_large_scale_costs hL
  change C ≤ L / 1000 ∧ 36 * L / (Real.sqrt x - 1) ≤ 100 at hc
  have hm := triangular18_large_scale_main_margin hL
  change (3601 / 100 : ℝ) * L < (677 / 10 : ℝ) * Real.sqrt x at hm
  have hn := Real.sqrt_nonneg x
  have ht := Real.rpow_nonneg (zero_lt_one.trans hb.1).le (1 / 4)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      add_nonneg (by norm_num only : (0 : ℝ) ≤ 1350000000000000 + 55000)
        (mul_nonneg
          (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4000000000000)
            (by linarith only [hLp] : 0 ≤ L + 284))
          (Real.rpow_nonneg (zero_lt_one.trans hb.1).le _))
  have hC : 0 ≤ 36 * L + C := add_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 36) hLp.le) hC0
  have hpr := mul_le_mul_of_nonneg_right hh hn
  have hpt := mul_le_mul_of_nonneg_right hh ht
  have hcost0 := mul_le_mul_of_nonneg_right (by linarith only : h - 1 ≤ h) hC
  have hcost1 := mul_le_mul_of_nonneg_left (add_le_add_left hc.1 (36 * L)) hhp.le
  have hu :
    300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + (h - 1) * (36 * L + C) ≤
      h *
        ((3 / 10 : ℝ) * Real.sqrt x + (13 / 10000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L + L / 1000) := by
    nlinarith only [hpr, hpt, hcost0, hcost1]
  have hE := mul_nonneg hn (Real.exp_pos (-18)).le
  have hg :
    (3 / 10 : ℝ) * Real.sqrt x + (13 / 10000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L + L / 1000 <
      Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
        36 * L / (Real.sqrt x - 1) := by
    nlinarith only [hm, hb.2.2.2, hc.2, hL, hE]
  have hfinal := hu.trans_lt (mul_lt_mul_of_pos_left hg hhp)
  simpa only [C, add_assoc] using hfinal

end PseudoPrime.Analysis
