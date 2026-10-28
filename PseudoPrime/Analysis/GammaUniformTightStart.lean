/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformReducedStart
public import PseudoPrime.LLS.GammaUniformLocalBudgetParameters

/-! # Tighter uniform coefficient-four-fifths starting value

Refined rational square-root and logarithmic-ratio certificates lower the common
logarithmic start to 45561. The decimal logarithm gives 10^19787 for subgroup,
general-character and least-prime witnesses, with the same analytic kernel.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a natural n ≥ 10 ^ 19787, log n > 45561. Take logs of the decimal
power and use the certified lower bound log 10 > 115129 / 50000.
This converts the reduced uniform Gamma budget to a concrete decimal start. -/
theorem log_nat_gt_45561_of_decimal_19787 {n : ℕ} (hn : 10 ^ 19787 ≤ n) :
    (45561 : ℝ) < Real.log n := by
  have h :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) 19787)
      (by exact_mod_cast hn : (10 : ℝ) ^ 19787 ≤ n)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, log_ten_gt_230258]

end PseudoPrime.Analysis
