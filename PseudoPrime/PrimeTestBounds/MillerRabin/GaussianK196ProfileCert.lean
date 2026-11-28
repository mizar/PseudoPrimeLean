/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAffineHorner
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighIntProfile
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileGrid
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighIntProfile
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAffineHorner
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileGrid

/-! # Integer profile sign certificate for K196 -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The shifted physical row certifies the same signs as the original rational checker. -/
private theorem high_profile_check_of_row (K : HighGaussianKernel) (a : ℤ) (r : MiddleIntRow)
    (hD : 0 < r.den)
    (hp : r.poly (2 * K.degree + 3) = K.ratProfile.comp (Polynomial.X + Polynomial.C (a : ℚ)))
    (h : ∀ i ≤ 2 * K.degree + 3, 0 ≤ r.num i) : highIntProfileSignCheck K a = true := by
  apply high_profile_check_of_coeffs K a
  intro i hi
  have hi' := Nat.le_of_lt_succ hi
  apply (Int.cast_nonneg_iff (R := ℚ)).mp
  change 0 ≤ ((highGammaShiftedProfile K a)[i]?.getD 0 : ℚ)
  rw [high_gamma_shifted_cast K a hi, high_cell_power_coeff K (a : ℚ) 1 hi, Polynomial.C_1, one_mul,
    ← hp, r.poly_coeff hi']
  exact
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Int.cast_nonneg (h i hi')) (Int.cast_pos.mpr hD).le)

/-- Generate the integer profile and shift it using Horner substitution. -/
private def integerShift (K : HighGaussianKernel) (a : ℤ) : MiddleIntRow :=
  let row := highProfileIntRow K
  ⟨row.den, gaussianFastAffineRatio (2 * K.degree + 3) a 1 1 row.num⟩

/-- The Horner shift agrees with the usual integer affine transform. -/
private theorem integer_shift_eq (K : HighGaussianKernel) (a : ℤ) :
    integerShift K a = (highProfileIntRow K).shift (2 * K.degree + 3) a 1 := by
  simp only [integerShift, MiddleIntRow.shift, MiddleIntRow.affine, gaussian_fast_ratio_eq, one_pow,
    mul_one]

/-- The shifted row has one entry for each coefficient through the physical degree. -/
private theorem integer_shift_size (K : HighGaussianKernel) (a : ℤ) :
    (integerShift K a).nums.size = 2 * K.degree + 4 := by
  simp only [integer_shift_eq, MiddleIntRow.shift, MiddleIntRow.affine, gaussianAffineRatioRow,
    gaussianAffineIntRow, Array.size_ofFn]

/-- Nonnegative coefficients of the generated row certify the original profile check. -/
private theorem integer_shift_check (K : HighGaussianKernel) (a : ℤ)
    (h : (integerShift K a).nums.toList.all (fun z ↦ decide (0 ≤ z)) = true) :
    highIntProfileSignCheck K a = true := by
  apply high_profile_check_of_row K a (integerShift K a) (high_profile_int_den_pos K)
  · have hp :=
      (highProfileIntRow K).poly_shift (2 * K.degree + 3) a 1 (high_profile_int_den_pos K).ne'
        (by decide)
    rw [integer_shift_eq, hp, high_profile_int_poly, Int.cast_one, div_one]
  · rw [Array.all_toList] at h
    intro i hi
    have hlt : i < (integerShift K a).nums.size := by
      rw [integer_shift_size]
      exact Nat.lt_succ_of_le hi
    have hn := of_decide_eq_true (Array.all_eq_true.mp h i hlt)
    simpa only [MiddleIntRow.num, Array.getElem?_eq_getElem hlt, Option.getD_some] using hn

/-- The K196 profile has nonnegative shifted coefficients at the H28 boundary 80. -/
public theorem k196_profile_grid_check : highIntProfileSignCheck .k196 80 = true := by
  apply integer_shift_check
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
