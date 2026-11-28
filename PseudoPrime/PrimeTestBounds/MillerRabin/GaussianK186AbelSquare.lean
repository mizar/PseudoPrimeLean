/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186AbelBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186AbelSquareInput

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186AbelBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186AbelSquareInput

/-! # Finite scalar formula for the squared K186 Abel derivative -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real Abel derivative is the cast of its rational coefficient polynomial. -/
theorem k186_abel_poly_map : k186AbelRat.map (Rat.castHom ℝ) = k186AbelPoly := by
  rw [k186_abel_rat_eq]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    ← Polynomial.derivative_map, high_comp_profile_map, Rat.coe_castHom, Rat.cast_pow, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat, k186AbelPoly]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_C_mul, pow_two, two_mul,
    Polynomial.C_mul, Polynomial.C_add]
  ring

/-- The Abel square integral is the rate-five moment of a polynomial of
degree at most 166. Extend the moment sum by zero coefficients to length 167. -/
theorem k186_abel_square_sum :
    k186AbelSquare =
      ∑ i ∈ Finset.range 167, (k186AbelPoly ^ 2).coeff i * ((i.factorial : ℝ) / 5 ^ (i + 1)) := by
  have hd : k186AbelPoly.natDegree ≤ 83 := by
    rw [← k186_abel_poly_map]
    exact Polynomial.natDegree_map_le.trans k186_abel_rat_degree
  have hs := Polynomial.natDegree_pow_le_of_le 2 hd
  unfold k186AbelSquare
  simp only [← Polynomial.eval_pow]
  rw [polynomial_laplace_moment _ (by norm_num only : (0 : ℝ) < 5)]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hs))
  intro i _ hi
  have hn := Nat.le_of_not_gt (fun h ↦ hi (Finset.mem_range.mpr h))
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hn), zero_mul]

/-- The fixed integer numerator of the full rate-five square moment. -/
def k186AbelMomentNum : ℤ :=
  ∑ i ∈ Finset.range 167, k186AbelSqNum i * (i.factorial : ℤ) * 5 ^ (166 - i)

/-- The real moment has one common positive denominator. The arithmetic
certificate can therefore use one integer comparison. -/
theorem k186_abel_square_ratio :
    k186AbelSquare = (k186AbelMomentNum : ℝ) / ((k186AbelDen : ℝ) ^ 2 * 5 ^ 167) := by
  rw [k186_abel_square_sum]
  simp only [k186AbelMomentNum, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ 166 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hp : i + 1 + (166 - i) = 167 := by rw [Nat.add_right_comm, Nat.add_sub_of_le hi']
  have hd : (k186AbelDen : ℝ) ≠ 0 := Int.cast_ne_zero.mpr k186_abel_den_pos.ne'
  rw [← k186_abel_poly_map, ← Polynomial.map_pow, Polynomial.coeff_map, Rat.coe_castHom,
    k186_abel_sq_coeff, ← hp, pow_add]
  push_cast only [Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Int.cast_mul, Int.cast_natCast,
    Int.cast_pow, Int.cast_ofNat]
  field_simp
  simp only [pow_add, pow_one]
  ring

/-- The common-denominator integer comparison implies the analytic moment cap. -/
theorem k186_abel_square_le_of_int (h : 50 * k186AbelMomentNum ≤ 11 * k186AbelDen ^ 2 * 5 ^ 167) :
    k186AbelSquare ≤ 11 / 50 := by
  have hd : (0 : ℝ) < k186AbelDen := Int.cast_pos.mpr k186_abel_den_pos
  rw [k186_abel_square_ratio]
  apply (div_le_iff₀ (mul_pos (pow_pos hd 2) (by norm_num only))).mpr
  have hc : ((50 * k186AbelMomentNum : ℤ) : ℝ) ≤ ((11 * k186AbelDen ^ 2 * 5 ^ 167 : ℤ) : ℝ) :=
    Int.cast_le.mpr h
  push_cast only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hc
  linarith only [hc]

/-- The single kernel-checked moment bound used throughout the finite range. -/
theorem k186_abel_square_le : k186AbelSquare ≤ 11 / 50 := by
  apply k186_abel_square_le_of_int
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
