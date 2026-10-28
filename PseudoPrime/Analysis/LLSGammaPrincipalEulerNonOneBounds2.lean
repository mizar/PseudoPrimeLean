/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.LLS.GammaPrincipalEulerCharacterBounds
public import PseudoPrime.LLS.GammaRetainedCommonCostBounds
public import PseudoPrime.LLS.PaperStatements.GammaPrincipalEulerNonOneBounds2

/-! # Non-one witnesses from retained real-axis Euler budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L ≥ 22221, log L ≤ L/2000. Bound the anchor by 2^15 and extend
with the logarithm tangent. This supplies the error condition for the even-character bound. -/
theorem nonOne_log_ratio_of_ge_22221 {L : ℝ} (hL : 22221 ≤ L) : Real.log L ≤ L / 2000 := by
  have hanchor :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 22221) (by norm_num only : (22221 : ℝ) ≤ 2 ^ 15)
  rw [Real.log_pow] at hanchor
  norm_num only [Nat.cast_ofNat] at hanchor
  have h :=
    log_le_mul_of_anchor (a := 22221) (b := 1 / 2000) (by norm_num only) hL
      (by linarith only [hanchor, Real.log_two_lt_d9]) (by norm_num only)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

end PseudoPrime.Analysis
