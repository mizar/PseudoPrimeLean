/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformWitnessBounds
public import PseudoPrime.Analysis.QuadraticGammaDecimalRefinement

/-! # A smaller uniform Gamma starting value

The same analytic budgets close from log q ≥ 45731. The certified decimal
logarithm then gives q ≥ 10^19861 for subgroup, character and least-prime witnesses.
Existing wrappers at 10^20000 remain available.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a natural n ≥ 10^19861, log n > 45731. Take logs of the decimal
power and use the certified lower bound log 10 > 115129/50000.
This converts the reduced uniform Gamma budget to a concrete decimal start. -/
theorem log_nat_gt_45731_of_decimal_19861 {n : ℕ} (hn : 10 ^ 19861 ≤ n) :
    (45731 : ℝ) < Real.log n := by
  have h :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) 19861)
      (by exact_mod_cast hn : (10 : ℝ) ^ 19861 ≤ n)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, log_ten_gt_230258]

end PseudoPrime.Analysis
