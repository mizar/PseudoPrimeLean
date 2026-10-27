/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointPolynomial
public import PseudoPrime.LLS.OddEndpointTwoCostWitness

/-! # Polynomial certificate target retaining both odd-prime arithmetic costs -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Polynomial numerator for the equal-cutoff two-cost endpoint condition.
Inputs are conductor logarithm L, pi-log endpoint P, radius y, logarithm z,
reciprocal cost c and logarithmic cost D. It subtracts both cost numerators
from the full endpoint polynomial, preparing rational scalar certificates. -/
noncomputable def oddEndpointTwoCostPolynomial (L P y z c D : ℝ) : ℝ :=
  fullEndpointPolynomial L P y z - (2 * y + 2 * z + 2) * c * y ^ 2 - (y - 1) ^ 2 * D

/-- For y>1 and arbitrary costs, multiplying the two-cost endpoint limit by
-y*(y-1)^2 gives the stated polynomial. Normalize square roots and logarithms,
clear nonzero denominators, and reuse the full endpoint identity. -/
theorem oddEndpointTwoCostPolynomial_eq_neg_limit (q : ℕ) {y : ℝ} (hy : 1 < y) (c D : ℝ) :
    -(y * (y - 1) ^ 2) * oddEndpointTwoCostLimit q (y ^ 2) (y ^ 2) c D =
      oddEndpointTwoCostPolynomial (Real.log q) (Real.log Real.pi) y (Real.log y) c D := by
  have hy0 : y ≠ 0 := (zero_lt_one.trans hy).ne'
  have hy1 : y - 1 ≠ 0 := (sub_pos.mpr hy).ne'
  have he := fullEndpointPolynomial_eq_neg_limit q hy
  unfold oddEndpointTwoCostLimit oddEndpointCostLimit oddEndpointTwoCostPolynomial
  rw [Real.sqrt_sq (zero_lt_one.trans hy).le, Real.log_pow]
  rw [← he]
  field_simp [hy0, hy1]
  ring

/-- For y>=1,z>=0, the polynomial increases with its pi-log parameter.
Both arithmetic costs are unchanged, so full-polynomial monotonicity suffices.
This permits a certified rational lower endpoint for log pi. -/
theorem oddEndpointTwoCostPolynomial_mono_pi {L P Q y z c D : ℝ} (hy : 1 ≤ y) (hz : 0 ≤ z)
    (hPQ : P ≤ Q) :
    oddEndpointTwoCostPolynomial L P y z c D ≤ oddEndpointTwoCostPolynomial L Q y z c D := by
  exact sub_le_sub_right (sub_le_sub_right (fullEndpointPolynomial_mono_pi hy hz hPQ) _) _

/-- At y>1, positive polynomial value with P=2096/1831 implies a negative
two-cost endpoint limit at x=Y=y^2. Use the certified pi-log lower bound and
the positive denominator multiplier. The result feeds the odd-prime criterion. -/
theorem oddEndpointTwoCostLimit_neg_of_rational_polynomial_pos (q : ℕ) {y c D : ℝ} (hy : 1 < y)
    (hP : 0 < oddEndpointTwoCostPolynomial (Real.log q) (2096 / 1831) y (Real.log y) c D) :
    oddEndpointTwoCostLimit q (y ^ 2) (y ^ 2) c D < 0 := by
  have hm :=
    oddEndpointTwoCostPolynomial_mono_pi (L := Real.log q) (c := c) (D := D) hy.le
      (Real.log_pos hy).le PseudoPrime.Analysis.log_pi_ge_2096_div_1831
  have hc : 0 < y * (y - 1) ^ 2 := mul_pos (zero_lt_one.trans hy) (sq_pos_of_pos (sub_pos.mpr hy))
  have he := oddEndpointTwoCostPolynomial_eq_neg_limit q hy c D
  apply (mul_lt_mul_iff_right₀ hc).mp
  rw [mul_zero]
  linarith only [he, lt_of_lt_of_le hP hm]

end PseudoPrime.LLS.PaperStatements
