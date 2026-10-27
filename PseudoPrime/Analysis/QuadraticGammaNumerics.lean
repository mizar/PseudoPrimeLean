/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption

/-! # Small-denominator Gamma margins for the direct quadratic coefficient 4/5 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Ten positive Taylor terms at 99/40 certify exp(−99/40)≤8/95.
Bound the positive exponential below by 95/8 and take reciprocals.
This small-denominator input preserves the direct quadratic coefficient 4/5. -/
theorem gamma_quadratic_exp_bound : Real.exp (-(99 / 40 : ℝ)) ≤ 8 / 95 := by
  have ht : (95 / 8 : ℝ) ≤ ∑ i ∈ Finset.range 10, (99 / 40 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  have he := ht.trans (Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) 10)
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 95 / 8) he
  rw [Real.exp_neg, ← one_div]
  norm_num only at hi
  exact hi

/-- The index-two Gamma main term with denominator 79/95 has a strict squared
margin over mass 11783423/25000000 plus allowance 7/5000 at scale 32/99.
Check the rational inequality exactly. This reserves an explicit remainder allowance. -/
theorem gamma_quadratic_direct_gap :
    ((11783423 / 25000000 : ℝ) + 7 / 5000) ^ 2 < (79 / 95 : ℝ) ^ 2 * (32 / 99) := by norm_num only

/-- For L>0 and error at most half of (7/5000)L, the Gamma main term
(79/95)sqrt((32/99)L²) strictly exceeds the mass term and error.
Use the rational squared gap. This supplies the final direct coefficient 4/5 contradiction. -/
theorem gamma_quadratic_direct_main_term_lt {L E : ℝ} (hL : 0 < L)
    (hE : E ≤ (7 / 5000 : ℝ) * L / 2) :
    (11783423 / 25000000 : ℝ) * L + E < (79 / 95 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  exact
    main_term_lt_of_sq_gap_and_error (by norm_num only) (by norm_num only) hL (by norm_num only)
      gamma_quadratic_direct_gap hE

end PseudoPrime.Analysis
