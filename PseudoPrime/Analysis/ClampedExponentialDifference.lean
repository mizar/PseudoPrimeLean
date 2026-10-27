/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

/-! # One-sided differences of a clamped exponential ramp -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For h>0 and nonnegative v,u, the clamped exponential ramp drops by at most h*u
when its argument decreases from v to v-u. Split whether the shifted argument remains
positive and use 1-exp(-z)<=z. This is the one-sided logarithmic-scale bound for compact
rational Mellin profiles, without a differentiability assumption at the clamp. -/
theorem clamped_exponential_drop_le {h v u : ℝ} (hh : 0 < h) (hv : 0 ≤ v) (hu : 0 ≤ u) :
    max (1 - Real.exp (-h * v)) 0 - max (1 - Real.exp (-h * (v - u))) 0 ≤ h * u := by
  have h1 : 0 ≤ 1 - Real.exp (-h * v) :=
    sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hh.le) hv))
  rw [max_eq_left h1]
  by_cases huv : v ≤ u
  · have he := Real.add_one_le_exp (-h * v)
    have hm := le_max_right (1 - Real.exp (-h * (v - u))) 0
    have hmul := mul_le_mul_of_nonneg_left huv hh.le
    linarith only [he, hm, hmul]
  · have hvu : 0 ≤ v - u := sub_nonneg.mpr (le_of_not_ge huv)
    have ha : Real.exp (-h * (v - u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hh.le) hvu)
    have hb : 0 ≤ 1 - Real.exp (-h * u) :=
      sub_nonneg.mpr
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hh.le) hu))
    have he := Real.add_one_le_exp (-h * u)
    have heq : Real.exp (-h * v) = Real.exp (-h * (v - u)) * Real.exp (-h * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hm := le_max_left (1 - Real.exp (-h * (v - u))) 0
    have hprod := mul_le_mul_of_nonneg_right ha hb
    rw [heq]
    nlinarith only [he, hm, hprod]

end PseudoPrime.Analysis
