/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.NextIntervalSelection
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularRefinedBounds

/-! # Strict improvements of the two refined triangular candidates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an input n>1 with logarithm between 1.1 and 1.5 trillion, the earlier
coefficient-0.284 candidate is strictly below the baseline selected bound.
Use the baseline seeded selection and its uniform quadratic lower bound. -/
theorem triangularEarlier_lt_nextSelected {n : ℕ} (hn : 1 < n)
    (hL : (1100000000000 : ℝ) ≤ Real.log n) (hU : Real.log n < 1500000000000) :
    (71 / 250 : ℝ) * Real.log n ^ 2 < nextSelectedEnvelope n := by
  rw [← next_eq_selected hn, next_eq_seeded hn (by linarith only [hL]) hU]
  have h := Analysis.gaussianSeededSelected_lower (by linarith only [hL] : (63 : ℝ) ≤ Real.log n)
  have hp := sq_pos_of_pos (show (0 : ℝ) < Real.log n by linarith only [hL])
  nlinarith only [h, hp]

/-- For n>1 with logarithm at least two trillion, coefficient 0.28237 is strictly
below the baseline coefficient 0.2827. The logarithm is positive, so comparison
of the rational coefficients gives strict improvement on the entire half-line. -/
theorem triangularRefined_lt_nextSelected {n : ℕ} (hn : 1 < n)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    (28237 / 100000 : ℝ) * Real.log n ^ 2 < nextSelectedEnvelope n := by
  rw [← next_eq_selected hn, next_eq_triangular hn hL]
  have hp := sq_pos_of_pos (show (0 : ℝ) < Real.log n by linarith only [hL])
  nlinarith only [hp]

end PseudoPrime.PrimeTestBounds.MillerRabin
