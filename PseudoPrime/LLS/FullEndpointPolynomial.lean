/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEndpointLimit
public import PseudoPrime.Analysis.PrecisePiLogBound

/-! # Polynomial positivity criterion for the full endpoint limit -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Explicit polynomial in conductor logarithm L, pi-log lower endpoint P,
radius y and radius logarithm z. It is the negative endpoint-limit numerator after
clearing y*(y-1)^2. Inputs are totalized; positivity at y>1 supplies a sufficient
witness criterion. Rational P removes pi from subsequent scalar certification. -/
noncomputable def fullEndpointPolynomial (L P y z : ℝ) : ℝ :=
  (y - 1) ^ 2 * (y ^ 2 - y / 20 - L * z - (1089 / 500 : ℝ) * z - 111 / 20) -
    (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1) * (L - P) + (26551 / 20000 - 2 * z) * y ^ 2)

/-- At radius y>1 with equal cutoffs y^2, the polynomial at L=log q,P=log pi,
z=log y equals -y*(y-1)^2 times the endpoint limit. Normalize square roots and
logarithms and clear the nonzero denominators. This provides an exact algebraic
certificate target without real powers or a gap parameter. -/
theorem fullEndpointPolynomial_eq_neg_limit (q : ℕ) {y : ℝ} (hy : 1 < y) :
    -(y * (y - 1) ^ 2) * reciprocalGapFullEndpointLimit q (y ^ 2) (y ^ 2) =
      fullEndpointPolynomial (Real.log q) (Real.log Real.pi) y (Real.log y) := by
  have hy0 : y ≠ 0 := (zero_lt_one.trans hy).ne'
  have hy1 : y - 1 ≠ 0 := (sub_pos.mpr hy).ne'
  unfold reciprocalGapFullEndpointLimit reciprocalGapReciprocalMassCap fullEndpointPolynomial
  rw [Real.sqrt_inv, Real.sqrt_sq (zero_lt_one.trans hy).le, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  field_simp [hy0, hy1]
  ring

/-- At y>1, strict positivity of the exact endpoint polynomial implies negativity
of the endpoint limit at the equal squared cutoffs. The multiplier y*(y-1)^2 is
positive. This transfers algebraic separation to the existing witness criterion. -/
theorem fullEndpointLimit_neg_of_polynomial_pos (q : ℕ) {y : ℝ} (hy : 1 < y)
    (hP : 0 < fullEndpointPolynomial (Real.log q) (Real.log Real.pi) y (Real.log y)) :
    reciprocalGapFullEndpointLimit q (y ^ 2) (y ^ 2) < 0 := by
  have hc : 0 < y * (y - 1) ^ 2 := mul_pos (zero_lt_one.trans hy) (sq_pos_of_pos (sub_pos.mpr hy))
  have he := fullEndpointPolynomial_eq_neg_limit q hy
  apply (mul_lt_mul_iff_right₀ hc).mp
  rw [mul_zero]
  linarith only [he, hP]

/-- For y>=1,z>=0 and P<=Q, the endpoint polynomial is monotone in its pi-log
parameter. Factor the difference into nonnegative factors. This permits certified
rational lower endpoints in place of log pi. -/
theorem fullEndpointPolynomial_mono_pi {L P Q y z : ℝ} (hy : 1 ≤ y) (hz : 0 ≤ z) (hPQ : P ≤ Q) :
    fullEndpointPolynomial L P y z ≤ fullEndpointPolynomial L Q y z := by
  have hc : 0 ≤ 2 * y + 2 * z + 2 := by linarith only [hy, hz]
  have hs : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy]
  have hm :=
    mul_nonneg (mul_nonneg hc (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hs))
      (sub_nonneg.mpr hPQ)
  unfold fullEndpointPolynomial
  nlinarith only [hm]

/-- At y>1, positivity of the polynomial with P=2096/1831 implies a negative
endpoint limit at y^2. Apply monotonicity and the certified lower bound for log pi.
Only log q and log y remain transcendental inputs to the polynomial certificate. -/
theorem fullEndpointLimit_neg_of_rational_polynomial_pos (q : ℕ) {y : ℝ} (hy : 1 < y)
    (hP : 0 < fullEndpointPolynomial (Real.log q) (2096 / 1831) y (Real.log y)) :
    reciprocalGapFullEndpointLimit q (y ^ 2) (y ^ 2) < 0 := by
  have hm :=
    fullEndpointPolynomial_mono_pi (L := Real.log q) hy.le (Real.log_pos hy).le
      PseudoPrime.Analysis.log_pi_ge_2096_div_1831
  exact fullEndpointLimit_neg_of_polynomial_pos q hy (lt_of_lt_of_le hP hm)

end PseudoPrime.LLS.PaperStatements
