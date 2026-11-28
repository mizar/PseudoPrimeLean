/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaPowers
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaZero

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaExpansion
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaZero

/-! # Rational enclosures for the high Gaussian gamma coefficients -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The shared rational zeroth coefficient bounds for a high kernel. -/
def highGammaZeroBounds (K : HighGaussianKernel) : ℚ × ℚ :=
  gammaZeroBounds K.pole

/-- The rational zero-order enclosure is valid for both high kernels. -/
theorem high_gamma_zero_bounds (K : HighGaussianKernel) :
    ((highGammaZeroBounds K).1 : ℝ) ≤ highGammaCoeff K 0 ∧
      highGammaCoeff K 0 ≤ ((highGammaZeroBounds K).2 : ℝ) := by
  have h₀ : 1 / 2 ≤ K.pole := by cases K <;> norm_num only [HighGaussianKernel.pole]
  have h₁ : K.pole ≤ 7 / 2 := by cases K <;> norm_num only [HighGaussianKernel.pole]
  simpa only [highGammaZeroBounds, highGammaCoeff, gammaZeroCoeff, Rat.cast_sub, Rat.cast_div,
    Rat.cast_add, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_ratCast] using
    gamma_zero_bounds h₀ h₁

/-- The rational enclosures for all orders, with a configurable prefix
length for the positive-order reciprocal power series. -/
def highGammaBounds (K : HighGaussianKernel) (N : ℕ) : ℕ → ℚ × ℚ
  | 0 => highGammaZeroBounds K
  | j + 1 => highGammaHigherBounds K j N

/-- These two rational endpoints bound every coefficient used in H33–H35. -/
theorem high_gamma_bounds (K : HighGaussianKernel) (N j : ℕ) :
    ((highGammaBounds K N j).1 : ℝ) ≤ highGammaCoeff K j ∧
      highGammaCoeff K j ≤ ((highGammaBounds K N j).2 : ℝ) := by
  cases j with
  | zero => exact high_gamma_zero_bounds K
  | succ j => exact high_gamma_higher_bounds K j N

/-- The H34 upper polynomial, including the conductor offset of four thirds.
Its coefficients are rational and can be used for Bernstein enclosures. -/
noncomputable def highGammaUpperPoly (K : HighGaussianKernel) (N : ℕ) : Polynomial ℚ :=
  Polynomial.C (4 / 3 : ℚ) * K.ratProfile +
    ∑ j ∈ Finset.range (2 * K.degree + 4),
      Polynomial.C (highGammaBounds K N j).2 * ((Polynomial.derivative^[j]) K.ratProfile)

/-- The polynomial evaluates to the real H34 upper derivative sum plus the
conductor offset. Orders above the profile degree contribute zero. -/
theorem high_gamma_upper_poly_eval (K : HighGaussianKernel) (N : ℕ) (z : ℝ) :
    ((highGammaUpperPoly K N).map (Rat.castHom ℝ)).eval z =
      (4 / 3 : ℝ) * K.realProfile.eval z +
        ∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
          ((highGammaBounds K N j).2 : ℝ) * ((Polynomial.derivative^[j]) K.realProfile).eval z := by
  have hdeg : K.realProfile.natDegree ≤ 2 * K.degree + 3 := by
    rw [← high_comp_profile_map,
      Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective (α := ℝ))]
    exact high_rat_profile_degree K
  simp only [highGammaUpperPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sum, ← Polynomial.iterate_derivative_map, high_comp_profile_map,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Rat.coe_castHom, Rat.cast_div, Rat.cast_ofNat]
  congr 1
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hdeg))
  intro j _ hj
  have hj' : K.realProfile.natDegree < j :=
    Nat.lt_of_not_ge (fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
  rw [Polynomial.iterate_derivative_eq_zero hj', Polynomial.eval_zero, mul_zero]

/-- Compute the gamma upper polynomial's coefficients with one shared
profile row and one rational enclosure per derivative order. -/
def highGammaUpperRow (K : HighGaussianKernel) (N : ℕ) : Array ℚ :=
  let m := 2 * K.degree + 4
  let B := K.cellPowerRow 0 1
  let U := Array.ofFn (fun j : Fin m ↦ (highGammaBounds K N j.val).2)
  Array.ofFn
    (fun k : Fin m ↦
      (4 / 3 : ℚ) * B[k.val]?.getD 0 +
        ∑ j ∈ Finset.range m,
          U[j]?.getD 0 * ((k.val + j).descFactorial j : ℚ) * B[k.val + j]?.getD 0)

/-- Each in-range entry of the shared coefficient row is a coefficient
of the H34 upper polynomial. -/
theorem high_gamma_upper_row_coeff (K : HighGaussianKernel) (N : ℕ) {k : ℕ}
    (hk : k < 2 * K.degree + 4) :
    (highGammaUpperRow K N)[k]?.getD 0 = (highGammaUpperPoly K N).coeff k := by
  have hb (i : ℕ) : (K.cellPowerRow 0 1)[i]?.getD 0 = K.ratProfile.coeff i := by
    by_cases hi : i < 2 * K.degree + 4
    · simpa only [Polynomial.C_1, one_mul, Polynomial.C_0, add_zero, Polynomial.comp_X] using
        high_cell_power_coeff K 0 1 hi
    · have hz : K.ratProfile.natDegree < i :=
        (high_rat_profile_degree K).trans_lt (Nat.lt_of_succ_le (Nat.le_of_not_gt hi))
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hz]
      simp only [HighGaussianKernel.cellPowerRow, Array.getElem?_ofFn, dite_eq_right hi,
        Option.getD_none]
  simp only [highGammaUpperRow, Array.getElem?_ofFn, dite_eq_left hk, Option.getD_some,
    highGammaUpperPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff,
    Polynomial.coeff_iterate_derivative]
  rw [hb]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp only [dite_eq_left hj', Option.getD_some, hb, nsmul_eq_mul, mul_assoc]

/-- Bound every H33 gamma coefficient by integer endpoints over a
common denominator, using the digamma bounds at order zero. -/
def highGammaGrid (K : HighGaussianKernel) (N D : ℕ) : ℕ → ℤ × ℤ
  | 0 => (⌊(D : ℚ) * (highGammaZeroBounds K).1⌋, ⌈(D : ℚ) * (highGammaZeroBounds K).2⌉)
  | j + 1 => highGammaHigherGrid K j N D

/-- The integer grid encloses the real gamma coefficients at every order. -/
theorem high_gamma_grid (K : HighGaussianKernel) (N D j : ℕ) (hD : 0 < D) :
    (↑(highGammaGrid K N D j).1 : ℝ) / D ≤ highGammaCoeff K j ∧
      highGammaCoeff K j ≤ (↑(highGammaGrid K N D j).2 : ℝ) / D := by
  cases j with
  | succ j => exact high_gamma_higher_grid K j N D hD
  | zero =>
    have hd : (0 : ℝ) < D := Nat.cast_pos.mpr hD
    have hl := (Rat.cast_le (K := ℝ)).mpr (Int.floor_le ((D : ℚ) * (highGammaZeroBounds K).1))
    have hu := (Rat.cast_le (K := ℝ)).mpr (Int.le_ceil ((D : ℚ) * (highGammaZeroBounds K).2))
    simp only [Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast, mul_comm (D : ℝ)] at hl hu
    have h := high_gamma_zero_bounds K
    exact ⟨((div_le_iff₀ hd).mpr hl).trans h.1, h.2.trans ((le_div_iff₀ hd).mpr hu)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
