/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds

/-! # Shared near-square Gamma comparison numerics -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For every L ≥ 1000, log L ≤ (7/1000)L. Bound the anchor by log(2^10)
and the certified log two upper value, then apply the generic real-anchor
tangent theorem. This controls every larger near-square witness scale. -/
theorem nearSquare_gamma_log_bound {L : ℝ} (hL : 1000 ≤ L) : Real.log L ≤ (7 / 1000 : ℝ) * L := by
  have ha :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 1000) (by norm_num only : (1000 : ℝ) ≤ 2 ^ 10)
  rw [Real.log_pow] at ha
  norm_num only [Nat.cast_ofNat] at ha
  exact
    log_le_mul_of_anchor (a := 1000) (by norm_num only) hL
      (by linarith only [ha, Real.log_two_lt_d9]) (by norm_num only)

end PseudoPrime.Analysis
