/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalLogTwo

/-! # Certified nonbinary logarithm cache seed -/

public section

namespace PseudoPrime.Analysis

-- Forty rational terms require deeper recursive reduction.
set_option maxRecDepth 4096 in
/-- The logarithm of three lies in the displayed rational interval, certified
by the mantissa `3/2` and the internal log-two theorem. No external table is used. -/
theorem log_three_35_bounds :
    (109861228866810969139524523692252569 / 100000000000000000000000000000000000 : ℝ) ≤ Real.log 3 ∧
      Real.log 3 ≤
        (109861228866810969139524523692252571 / 100000000000000000000000000000000000 : ℝ) := by
  have hc :
    mantissaLog40Check (3 / 2)
        (40546510810816438197801311546434913 / 100000000000000000000000000000000000)
        (40546510810816438197801311546434914 / 100000000000000000000000000000000000) =
      true := by
    unfold mantissaLog40Check rationalMantissaLog40
    decide_cbv
  have hl :
    (69314718055994530941723212145817656 / 100000000000000000000000000000000000 : ℚ) ≤
      Real.log 2 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using log_two_35_bounds.1
  have hu :
    Real.log 2 ≤
      (69314718055994530941723212145817657 / 100000000000000000000000000000000000 : ℚ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using log_two_35_bounds.2
  have h := log_binary_rational_bounds 1 hc hl hu
  norm_num only [Int.cast_one, Rat.cast_div, Rat.cast_ofNat, Rat.cast_add, Rat.cast_mul,
    Rat.cast_one, pow_one, ite_true] at h ⊢
  exact h

end PseudoPrime.Analysis
