/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianOppositePolePolynomial
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighEulerSign
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassTransform
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianOppositePolePolynomial

/-! # Rational coefficients and binomial translation of the high Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The coefficient of degree `j` in the mixed-pole Fourier polynomial,
computed by the same lowering recurrence over rational scalars. -/
public def oppositePoleCoeff (a : ℚ) (p q j : ℕ) : ℚ :=
  match p, q with
  | 0, _ => 0
  | n + 1, 0 => if n = j then 2 / (n.factorial : ℚ) else 0
  | 1, 1 => if j = 0 then 1 / a else 0
  | p + 1, q + 1 =>
    (1 / (2 * a)) * (oppositePoleCoeff a p (q + 1) j + oppositePoleCoeff a (p + 1) q j)
termination_by p + q
decreasing_by
  · exact Nat.add_lt_add_right (Nat.lt_succ_self _) _
  · exact Nat.add_lt_add_left (Nat.lt_succ_self _) _

/-- Coefficient extraction commutes with the mixed-pole lowering recurrence. -/
public theorem opposite_pole_coeff_eq (a : ℚ) (p q j : ℕ) :
    (oppositePolePolynomial a p q).coeff j = oppositePoleCoeff a p q j := by
  induction p, q using oppositePolePolynomial.induct with
  | case1 q => simp only [oppositePolePolynomial, oppositePoleCoeff, Polynomial.coeff_zero]
  | case2 n =>
    simp only [oppositePolePolynomial, oppositePoleCoeff, Polynomial.coeff_C_mul_X_pow, eq_comm]
  | case3 => simp only [oppositePolePolynomial, oppositePoleCoeff, Polynomial.coeff_C]
  | case4 p q hne hp hq =>
    rw [oppositePolePolynomial.eq_4 a p q hne, oppositePoleCoeff.eq_4 a j p q hne,
      Polynomial.coeff_C_mul, Polynomial.coeff_add, hp, hq]

/-- The high mass coefficients are linear combinations of rational mixed-pole coefficients. -/
public theorem high_mass_coeff_sum (K : HighGaussianKernel) (i : ℕ) :
    (highGaussianMassPolynomial K).coeff i =
      ∑ j ∈ Finset.range (K.degree + 1),
        (K.normalization * (normSqPolynomial K.pole K.polynomial).coeff j) *
          oppositePoleCoeff K.pole (K.degree + 2 - j) (K.degree + 2 - j) i := by
  simp only [highGaussianMassPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    opposite_pole_coeff_eq]

/-- Translation of the mass polynomial is a finite binomial transform. -/
public theorem high_mass_shifted_coeff_sum (K : HighGaussianKernel) (b : ℚ) (i : ℕ) :
    ((highGaussianMassPolynomial K).comp (Polynomial.X + Polynomial.C b)).coeff i =
      ∑ j ∈ Finset.range (K.degree + 2),
        (highGaussianMassPolynomial K).coeff j * ((j.choose i : ℚ) * b ^ (j - i)) := by
  have hd : (highGaussianMassPolynomial K).natDegree ≤ K.degree + 1 := by
    simpa only [Polynomial.C_0, add_zero, Polynomial.comp_X] using high_mass_shifted_degree K 0
  unfold Polynomial.comp
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hd)]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (b ^ (j - i))]

end PseudoPrime.PrimeTestBounds.MillerRabin
