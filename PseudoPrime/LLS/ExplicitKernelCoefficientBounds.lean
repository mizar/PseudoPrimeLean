/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption

/-! # Rational main-term margins for explicit least-prime bounds

The four profiles certify arithmetic margins and their use after error absorption.
They do not assert the zero-mass estimates, kernel exponential bounds, or remainders.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Exact rational main-term margin for index two, target coefficient 159/200.
This arithmetic certificate supplies no zero-mass or remainder estimate. -/
theorem gamma_quadratic_coefficient_gap :
    ((11783423 / 25000000 : ℝ) + (1 / 100000 : ℝ)) ^ 2 <
      (1 - 2 * (84163 / 1000000 : ℝ)) ^ 2 * ((159 / 200 : ℝ) / (99 / 40)) := by
  norm_num only

/-- For positive L and error at most half the certified allowance, the index two, target
coefficient 159/200
main term strictly dominates the mass term and error. Apply the rational squared gap.
The zero-mass and analytic remainder estimates remain separate inputs. -/
theorem gamma_quadratic_main_term_lt {L E : ℝ} (hL : 0 < L) (hE : E ≤ (1 / 100000 : ℝ) * L / 2) :
    (11783423 / 25000000 : ℝ) * L + E <
      (1 - 2 * (84163 / 1000000 : ℝ)) * Real.sqrt (((159 / 200 : ℝ) / (99 / 40)) * L ^ 2) := by
  exact
    Analysis.main_term_lt_of_sq_gap_and_error (by norm_num only) (by norm_num only) hL
      (by norm_num only) gamma_quadratic_coefficient_gap hE

/-- Exact rational main-term margin for normalized index at least four, target coefficient
33/50.
This arithmetic certificate supplies no zero-mass or remainder estimate. -/
theorem gamma_index_four_coefficient_gap :
    ((11783423 / 25000000 : ℝ) + (1 / 2000 : ℝ)) ^ 2 <
      (1 - (4 / 3 : ℝ) * (55 / 344)) ^ 2 * ((33 / 50 : ℝ) / (11 / 6)) := by
  norm_num only

/-- For positive L and error at most half the certified allowance, the normalized index at
least four, target coefficient 33/50
main term strictly dominates the mass term and error. Apply the rational squared gap.
The zero-mass and analytic remainder estimates remain separate inputs. -/
theorem gamma_index_four_main_term_lt {L E : ℝ} (hL : 0 < L) (hE : E ≤ (1 / 2000 : ℝ) * L / 2) :
    (11783423 / 25000000 : ℝ) * L + E <
      (1 - (4 / 3 : ℝ) * (55 / 344)) * Real.sqrt (((33 / 50 : ℝ) / (11 / 6)) * L ^ 2) := by
  exact
    Analysis.main_term_lt_of_sq_gap_and_error (by norm_num only) (by norm_num only) hL
      (by norm_num only) gamma_index_four_coefficient_gap hE

/-- Exact rational main-term margin for three nonprincipal characters, target coefficient
293/1000.
This arithmetic certificate supplies no zero-mass or remainder estimate. -/
theorem gamma_three_character_coefficient_gap :
    ((2 * (943 / 2000 : ℝ)) + (1 / 2000 : ℝ)) ^ 2 <
      (3 - 4 * (55 / 344 : ℝ)) ^ 2 * ((293 / 1000 : ℝ) / (11 / 6)) := by
  norm_num only

/-- For positive L and error at most half the certified allowance, the three nonprincipal
characters, target coefficient 293/1000
main term strictly dominates the mass term and error. Apply the rational squared gap.
The zero-mass and analytic remainder estimates remain separate inputs. -/
theorem gamma_three_character_main_term_lt {L E : ℝ} (hL : 0 < L)
    (hE : E ≤ (1 / 2000 : ℝ) * L / 2) :
    (2 * (943 / 2000 : ℝ)) * L + E <
      (3 - 4 * (55 / 344 : ℝ)) * Real.sqrt (((293 / 1000 : ℝ) / (11 / 6)) * L ^ 2) := by
  exact
    Analysis.main_term_lt_of_sq_gap_and_error (by norm_num only) (by norm_num only) hL
      (by norm_num only) gamma_three_character_coefficient_gap hE

/-- Exact rational main-term margin for fixed triangular kernel, target coefficient 29/100.
This arithmetic certificate supplies no zero-mass or remainder estimate. -/
theorem triangular_large_index_coefficient_gap :
    ((32 : ℝ) + (1 / 10 : ℝ)) ^ 2 < (299 / 5 : ℝ) ^ 2 * (29 / 100 : ℝ) := by norm_num only

/-- For positive L and error at most half the certified allowance, the fixed triangular kernel,
target coefficient 29/100
main term strictly dominates the mass term and error. Apply the rational squared gap.
The zero-mass and analytic remainder estimates remain separate inputs. -/
theorem triangular_large_index_main_term_lt {L E : ℝ} (hL : 0 < L) (hE : E ≤ (1 / 10 : ℝ) * L / 2) :
    (32 : ℝ) * L + E < (299 / 5 : ℝ) * Real.sqrt ((29 / 100 : ℝ) * L ^ 2) := by
  exact
    Analysis.main_term_lt_of_sq_gap_and_error (by norm_num only) (by norm_num only) hL
      (by norm_num only) triangular_large_index_coefficient_gap hE

end PseudoPrime.LLS
