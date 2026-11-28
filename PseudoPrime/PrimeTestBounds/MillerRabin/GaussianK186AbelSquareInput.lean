/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms

/-! # Integer coefficients of the K186 second Abel derivative -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Construct the second Abel derivative numerator from three adjacent entries
of the certified K186 profile. Its denominator is sixteen times the source denominator. -/
private def abelNumerator (i : ℕ) : ℤ :=
  81 * baseRow.num i - 72 * (i + 1) * baseRow.num (i + 1) +
    16 * (i + 1) * (i + 2) * baseRow.num (i + 2)

/-- Cache the 84 integer numerators of the second Abel derivative. -/
private def abelRow : MiddleIntRow :=
  ⟨16 * baseRow.den, Array.ofFn (fun i : Fin 84 ↦ abelNumerator i.val)⟩

/-- The rational polynomial represented by the K186 Abel derivative row. -/
public noncomputable def k186AbelRat : Polynomial ℚ :=
  abelRow.poly 83

/-- The cached row represents the twice-applied operator (9/4 - \partial). -/
public theorem k186_abel_rat_eq :
    let B := HighGaussianKernel.k186.ratProfile
    k186AbelRat =
      Polynomial.C ((9 / 4 : ℚ) ^ 2) * B - Polynomial.C (2 * (9 / 4 : ℚ)) * B.derivative +
        B.derivative.derivative := by
  have h :=
    MiddleIntRow.poly_of_secondMatches (N := 83) (a := 9) (b := 4) (p := baseRow) (q := abelRow)
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by
        simp only [abelRow, Array.size_ofFn]; decide)
      (by decide +kernel)
  dsimp only at h ⊢
  rw [base_row_poly] at h
  simpa only [k186AbelRat, Int.cast_ofNat] using h

/-- The Abel derivative polynomial has the same degree bound as the source row. -/
public theorem k186_abel_rat_degree : k186AbelRat.natDegree ≤ 83 := by
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos 83) _)

/-- The scalar denominator shared by all coefficients of the Abel derivative. -/
public def k186AbelDen : ℤ :=
  abelRow.den

/-- Read one signed integer coefficient of the Abel derivative row. -/
public def k186AbelNum (i : ℕ) : ℤ :=
  abelRow.num i

/-- Recover a rational coefficient by a single division. Beyond degree 83
both the stored numerator and the coefficient are zero. -/
public theorem k186_abel_rat_coeff (i : ℕ) :
    k186AbelRat.coeff i = (k186AbelNum i : ℚ) / k186AbelDen := by
  exact
    abelRow.poly_coeff_all 83
      (by
        simp only [abelRow, Array.size_ofFn]; decide)
      i

/-- The common denominator of the second derivative row is positive. -/
public theorem k186_abel_den_pos : 0 < k186AbelDen := by decide +kernel

/-- The numerator at degree `i` of the square, using the convolution
of the integer row with itself. The denominator is the square of the row denominator. -/
public def k186AbelSqNum (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.antidiagonal i, k186AbelNum j.1 * k186AbelNum j.2

/-- The integer convolution represents the square's rational coefficients. -/
public theorem k186_abel_sq_coeff (i : ℕ) :
    (k186AbelRat ^ 2).coeff i = (k186AbelSqNum i : ℚ) / (k186AbelDen : ℚ) ^ 2 := by
  rw [pow_two k186AbelRat, Polynomial.coeff_mul]
  simp only [k186_abel_rat_coeff, div_mul_div_comm, ← pow_two, k186AbelSqNum, Int.cast_sum,
    Int.cast_mul, Finset.sum_div]

end PseudoPrime.PrimeTestBounds.MillerRabin
