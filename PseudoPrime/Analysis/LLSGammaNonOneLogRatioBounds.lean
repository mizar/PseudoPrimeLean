/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.LLS.GammaNonOneLogRatioBounds2

/-! # Non-one Gamma witnesses with explicit logarithmic and prefix budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L ≥ 29121, log L ≤ L/2800. Bound the anchor by 2^15, use the
certified logarithm of two, and extend by the logarithm tangent inequality.
This closes the logarithmic hypothesis on a full half-line. -/
theorem nonOne_log_ratio_of_ge_29121 {L : ℝ} (hL : 29121 ≤ L) : Real.log L ≤ L / 2800 := by
  have hanchor :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 29121) (by norm_num only : (29121 : ℝ) ≤ 2 ^ 15)
  rw [Real.log_pow] at hanchor
  norm_num only [Nat.cast_ofNat] at hanchor
  have h :=
    log_le_mul_of_anchor (a := 29121) (b := 1 / 2800) (by norm_num only) hL
      (by linarith only [hanchor, Real.log_two_lt_d9]) (by norm_num only)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

end PseudoPrime.Analysis
