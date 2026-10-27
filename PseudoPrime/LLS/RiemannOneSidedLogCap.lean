/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannOneSidedCheckpoint

/-! # One-sided Chebyshev lower bounds with certified logarithm caps -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: positive ordered cutoffs, one-sided smoothed errors, a nonnegative target
and an upper bound for the logarithm of the cutoff ratio.
Claim: P is a lower bound for psi(y) if its rational log-cap comparison holds.
Proof: retain the actual logarithm in the positive finite difference and cancel it.
Role: sharpen small-cutoff certificates without symmetrizing the two errors. -/
theorem psi_lower_of_one_sided_log_cap {x y U V P R : ℝ} (hx : 0 < x) (hxy : x < y)
    (hU : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x ≤ x + U)
    (hV : y - V ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum y) (hP : 0 ≤ P)
    (hR : Real.log (y / x) ≤ R) (hc : P * R ≤ y - x - U - V) : P ≤ Chebyshev.psi y := by
  have hl := Real.log_pos ((lt_div_iff₀ hx).mpr (show 1 * x < y by simpa only [one_mul] using hxy))
  exact
    (mul_le_mul_iff_left₀ hl).mp
      ((mul_le_mul_of_nonneg_left hR hP).trans
        (hc.trans (psi_mul_log_lower_of_one_sided_errors hx hxy hU hV)))

end PseudoPrime.LLS
