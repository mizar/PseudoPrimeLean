/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalHorner16

/-! # Horner evaluation of the certified 25-term phase polynomial -/

public section

namespace PseudoPrime.Analysis

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Expand the fixed 25-term polynomial once, before concrete arithmetic checks.
/-- For every rational phase v, the depth-24 Horner recurrence equals the
existing 25-term rational Taylor polynomial. Expanding this fixed identity once
permits concrete phase certificates to avoid recomputing all monomial powers. -/
theorem rational_horner25_poly (v : ℚ) :
    rationalExpHorner (0, v) 24 0 = rationalPhaseTaylor v 25 := by
  apply Prod.ext <;>
    simp only [rationalExpHorner, rationalPhaseTaylor, rationalComplexAdd, rationalComplexScale,
      rationalComplexMul, rationalComplexPow, Finset.sum_range_succ, Finset.sum_range_zero,
      Prod.fst_add, Prod.snd_add, zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub] <;>
    norm_num only [Nat.factorial] <;>
    ring

end PseudoPrime.Analysis
