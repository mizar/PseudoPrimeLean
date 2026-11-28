/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186CompInteger
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186CompInteger

/-! # Zero compensation on the nine merged K186 cells -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first merged cell contributes no compensation ticks. -/
private theorem k186_comp_zero_1 (a : ℤ × ℤ) : compIntegerStep (0, a) 3983 = (3983, a) := by
  exact comp_step_of_sign 0 3983 a (by decide +kernel)

/-- The second merged cell contributes no compensation ticks. -/
private theorem k186_comp_zero_2 (a : ℤ × ℤ) : compIntegerStep (8713, a) 5686 = (14399, a) := by
  exact comp_step_of_sign 8713 5686 a (by decide +kernel)

/-- The third merged cell contributes no compensation ticks. -/
private theorem k186_comp_zero_3 (a : ℤ × ℤ) : compIntegerStep (20784, a) 8048 = (28832, a) := by
  exact comp_step_of_sign 20784 8048 a (by decide +kernel)

/-- The fourth merged cell contributes no compensation ticks. -/
private theorem k186_comp_zero_4 (a : ℤ × ℤ) : compIntegerStep (36788, a) 21455 = (58243, a) := by
  exact comp_step_of_sign 36788 21455 a (by decide +kernel)

/-- The fifth merged cell contributes no compensation ticks. -/
private theorem k186_comp_zero_5 (a : ℤ × ℤ) : compIntegerStep (67446, a) 38399 = (105845, a) := by
  exact comp_step_of_sign 67446 38399 a (by decide +kernel)

/-- The sixth merged cell contributes no compensation ticks. -/
private theorem k186_comp_zero_6 (a : ℤ × ℤ) : compIntegerStep (115339, a) 27589 = (142928, a) := by
  exact comp_step_of_sign 115339 27589 a (by decide +kernel)

/-- The seventh merged cell contributes no compensation ticks. -/
private theorem k186_comp_zero_7 (a : ℤ × ℤ) : compIntegerStep (155113, a) 39522 = (194635, a) := by
  exact comp_step_of_sign 155113 39522 a (by decide +kernel)

/-- The eighth merged cell contributes no compensation ticks. -/
private theorem k186_comp_zero_8 (a : ℤ × ℤ) : compIntegerStep (204693, a) 59016 = (263709, a) := by
  exact comp_step_of_sign 204693 59016 a (by decide +kernel)

/-- On the last merged cell, the uncut profile has nonnegative Bernstein
coefficients, so both compensation charges vanish. -/
public theorem k186_last_comp_zero : k186CompCellInteger 300387 223901 = (0, 0) := by
  have hs : k186CompSign 300387 223901 = true := by decide +kernel
  apply k186_comp_cell_zero
  intro j hj
  exact of_decide_eq_true (List.all_eq_true.mp hs j (List.mem_range.mpr (Nat.lt_succ_of_le hj)))

end PseudoPrime.PrimeTestBounds.MillerRabin
