/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ConductorCert
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleResidualInputs
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ConductorCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ProfileCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileGrid
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget

/-! # Fixed signed K186 reflection coefficients -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The translated integer profile and its common denominator have already
been checked in the conductor certificate. -/
private def shiftedRow : MiddleIntRow :=
  ⟨k186GammaDen, conductorRow⟩

/-- The unshifted integer profile used to identify the reflected moment. -/
private def baseRow : MiddleIntRow :=
  ⟨k186GammaDen, k186GridBase⟩

/-- The common denominator is positive. -/
private theorem row_den_pos : 0 < shiftedRow.den := by decide +kernel

/-- The integer source row represents the rational physical profile. -/
private theorem base_row_poly : baseRow.poly 83 = HighGaussianKernel.k186.ratProfile := by
  have hbase : highGammaProfileInt 84 (highGammaBaseFrom 40 k186GammaExpanded) = k186GridBase :=
    high_gamma_profile_int_of_den 84 40 _ conductor_den rfl _ base_num_ok
  have hrow : highGammaShiftedProfile .k186 0 = highGammaShiftInt 84 0 k186GridBase :=
    high_gamma_profile_of_stages .k186 0 conductor_expanded hbase rfl
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i ≤ 83
  · have hh : i < 84 := Nat.lt_succ_of_le hi
    have he := high_gamma_shifted_cast .k186 0 hh
    simp only [hrow, Int.cast_zero] at he
    rw [high_cell_power_coeff .k186 (0 : ℚ) 1 hh, Polynomial.C_1, Polynomial.C_0, one_mul, add_zero,
      Polynomial.comp_X] at he
    have hz : highGammaShiftInt 84 0 k186GridBase = k186GridBase := by decide +kernel
    have hd :
      highGammaProfileDen (2 * HighGaussianKernel.k186.degree + 4) (highGammaBaseRow .k186) =
        k186GammaDen := by
      change
        highGammaProfileDen 84 (highGammaBaseFrom 40 HighGaussianKernel.k186.expandedCoeffRow) =
          k186GammaDen
      rw [conductor_expanded]
      exact conductor_den
    rw [hz, hd] at he
    rw [baseRow.poly_coeff hi]
    change (k186GridBase[i]?.getD 0 : ℚ) / k186GammaDen = _
    rw [he, mul_comm, mul_div_cancel_right₀ _ (by decide +kernel)]
  · have hdeg := high_rat_profile_degree .k186
    exact
      (baseRow.poly_coeff_all 83 (by decide +kernel) i).trans
        (by
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (Nat.lt_of_not_ge hi))]
          simp only [baseRow, MiddleIntRow.num,
            Array.getElem?_eq_none
                (show k186GridBase.size ≤ i from Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)),
            Option.getD_none, Int.cast_zero, zero_div])

/-- The certificate gives the translated profile, including zero padding. -/
private theorem shifted_row_poly :
    shiftedRow.poly 83 = (baseRow.poly 83).comp (Polynomial.X + Polynomial.C 58) := by
  rw [base_row_poly]
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i ≤ 83
  · rw [shiftedRow.poly_coeff hi]
    change (conductorRow[i]?.getD 0 : ℚ) / k186GammaDen = _
    rw [conductor_entry i (Nat.lt_succ_of_le hi), mul_comm,
      mul_div_cancel_right₀ _ (by decide +kernel)]
  · have ht := Nat.lt_of_not_ge hi
    have hd :
      ((HighGaussianKernel.k186.ratProfile).comp (Polynomial.X + Polynomial.C 58)).natDegree ≤
        83 := by
      simpa only [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one,
        HighGaussianKernel.degree, show 2 * 40 + 3 = 83 by decide] using
        high_rat_profile_degree .k186
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt ht)]
    exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_of_lt ht)

/-- Compute the one shifted reflection moment by the integer recurrence. -/
private def reflectionRow : MiddleIntRow :=
  (middleReflectionSource 83 (13 / 4) shiftedRow).moment 83 9 4

/-- The computed moment agrees with the rational analytic reflected profile. -/
private theorem reflection_row_poly :
    reflectionRow.poly 83 =
      middleReflectionPoly HighGaussianKernel.k186.ratProfile (13 / 4) 58 := by
  have h :=
    middle_shifted_reflection_poly baseRow shiftedRow 83 9 4 58 row_den_pos (by decide) (by decide)
      (by decide +kernel) shifted_row_poly
  rw [base_row_poly] at h
  simpa only [reflectionRow, Int.cast_ofNat, show (9 / 4 : ℚ) + 1 = 13 / 4 by decide +kernel] using
    h

/-- Sum the positive reflected-moment coefficients with rational monomial weights. -/
private def reflectionSum : ℚ :=
  let row := reflectionRow
  ∑ i ∈ Finset.range 84, (max 0 (row.num i) : ℤ) * ((3 / 22 : ℚ) * i) ^ i

/-- The fixed signed moment fits the allocated rational budget. -/
private theorem reflection_sum_check :
    6 * (reflectionSum / (reflectionRow.den : ℚ)) ≤
      ((gaussianMidExpGrid 12760).lower : ℤ) / 100000000 / 10 ^ 6 := by
  decide +kernel

/-- The signed reflected moment at the far anchor has budget at most one
millionth, after applying the decay factor and the three-character weight. -/
public theorem k186_reflection_coeff_cap :
    let P := middleReflectionPoly HighGaussianKernel.k186.realProfile (13 / 4) 58
    6 *
        (Real.exp (-(11 / 4 : ℝ) * 58) *
          ∑ i ∈ Finset.range (P.natDegree + 1), max 0 (P.coeff i) * ((3 / 22 : ℝ) * i) ^ i) ≤
      1 / 10 ^ 6 := by
  intro P
  have hd : 0 < reflectionRow.den := by
    exact
      mul_pos (mul_pos (shiftedRow.scaleRat_pos row_den_pos _) row_den_pos)
        (pow_pos (by decide : (0 : ℤ) < 9) _)
  have hdR : (0 : ℝ) < reflectionRow.den := Int.cast_pos.mpr hd
  have hP : (reflectionRow.poly 83).map (Rat.castHom ℝ) = P := by
    rw [reflection_row_poly, middle_reflection_poly_map]
    simp only [high_comp_profile_map, Rat.cast_div, Rat.cast_ofNat, P]
  have hdeg : P.natDegree ≤ 83 := by
    rw [← hP, Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective]
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos 83) _)
  have hcoeff (i : ℕ) (hi : i < 84) :
    (reflectionRow.num i : ℝ) / reflectionRow.den = P.coeff i := by
    rw [← hP, Polynomial.coeff_map, Rat.coe_castHom,
      reflectionRow.poly_coeff (Nat.le_of_lt_succ hi), Rat.cast_div, Rat.cast_intCast,
      Rat.cast_intCast]
  have hs :
    (reflectionSum : ℝ) / reflectionRow.den =
      ∑ i ∈ Finset.range 84, max 0 (P.coeff i) * ((3 / 22 : ℝ) * i) ^ i := by
    simp only [reflectionSum, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_pow,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Int.cast_max, Int.cast_zero, mul_div_right_comm, div_eq_mul_inv (max _ _),
      mul_comm (max _ _), mul_max_of_nonneg _ _ (inv_nonneg.mpr hdR.le), mul_zero,
      mul_comm (↑reflectionRow.den : ℝ)⁻¹, ← div_eq_mul_inv, hcoeff i (Finset.mem_range.mp hi)]
  have hshort :
    (∑ i ∈ Finset.range (P.natDegree + 1), max 0 (P.coeff i) * ((3 / 22 : ℝ) * i) ^ i) ≤
      ∑ i ∈ Finset.range 84, max 0 (P.coeff i) * ((3 / 22 : ℝ) * i) ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hdeg))
      (fun i _ _ ↦
        mul_nonneg (le_max_left _ _)
          (pow_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg i)) i))
  have hraw := (Rat.cast_le (K := ℝ)).mpr reflection_sum_check
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat] at hraw
  rw [hs] at hraw
  have hexp := (gaussian_mid_exp_grid 12760).1
  norm_num only [Nat.cast_ofNat, Int.cast_ofNat] at hexp
  have hb :=
    (mul_le_mul_of_nonneg_left hshort (by norm_num only : (0 : ℝ) ≤ 6)).trans
      (hraw.trans (div_le_div_of_nonneg_right hexp (by norm_num only)))
  rw [neg_mul, Real.exp_neg]
  norm_num only at hb ⊢
  have he := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.exp_pos (319 / 2 : ℝ)).le)
  rw [div_eq_mul_inv (Real.exp _), ← mul_assoc (Real.exp (319 / 2 : ℝ))⁻¹ (Real.exp (319 / 2 : ℝ)),
    inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul] at he
  simpa only [← mul_assoc, mul_comm (Real.exp (319 / 2 : ℝ))⁻¹ 6, one_div] using he

end PseudoPrime.PrimeTestBounds.MillerRabin
