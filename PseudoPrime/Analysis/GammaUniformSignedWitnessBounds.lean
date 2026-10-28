/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedProfiles
public import PseudoPrime.LLS.GammaUniformTightStart
public import PseudoPrime.Analysis.LogarithmicShiftBounds

/-! # Decimal and character interfaces for rational signed Gamma profiles

The concrete rational triples (4/5,0,29), (4/5,0,-2) and (4/5,-1,0)
have decimal entrances 15188, 20121 and 22097. General characters and least
outside primes use the same cutoffs. A rational-parameter interface retains
the actual analytic budget for further coefficient optimization.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For n ≥ 10^d with d > 0, any t < d*(115129/50000) satisfies t < log n.
Take logarithms of the power and use the certified lower bound for log 10.
This gives a common exact decimal conversion for the signed profiles. -/
theorem log_nat_gt_of_decimal_lower {n d : ℕ} {t : ℝ} (hd : 0 < d) (hn : 10 ^ d ≤ n)
    (ht : t < (d : ℝ) * (115129 / 50000)) : t < Real.log n := by
  have h :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) d)
      (by exact_mod_cast hn : (10 : ℝ) ^ d ≤ n)
  rw [Real.log_pow] at h
  have hlo := mul_lt_mul_of_pos_left log_ten_gt_230258 (Nat.cast_pos.mpr hd : (0 : ℝ) < d)
  exact ht.trans (hlo.trans_le h)

end PseudoPrime.Analysis
