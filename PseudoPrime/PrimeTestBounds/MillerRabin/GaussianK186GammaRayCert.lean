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

/-! # One fixed K186 Gamma moment on the far ray -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Reuse the verified profile at the Gamma correction boundary. -/
private def shiftedRow : MiddleIntRow :=
  ⟨k186GammaDen, k186GridShift⟩

/-- Its common denominator is positive. -/
private theorem row_den_pos : 0 < shiftedRow.den := by decide +kernel

/-- The integer row represents the analytic polynomial shifted to 65. -/
private theorem shifted_row_poly :
    shiftedRow.poly 83 =
      HighGaussianKernel.k186.ratProfile.comp (Polynomial.X + Polynomial.C 65) := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i ≤ 83
  · have h := k186_cached_shift 65 (Nat.lt_succ_of_le hi)
    simp only [k186_shifted_ok, Int.cast_ofNat] at h
    rw [shiftedRow.poly_coeff hi]
    change (k186GridShift[i]?.getD 0 : ℚ) / k186GammaDen = _
    rw [h, mul_comm, mul_div_cancel_right₀ _ (by decide +kernel)]
  · have ht := Nat.lt_of_not_ge hi
    have hd :
      (HighGaussianKernel.k186.ratProfile.comp (Polynomial.X + Polynomial.C 65)).natDegree ≤
        83 := by
      simpa only [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one,
        HighGaussianKernel.degree, show 2 * 40 + 3 = 83 by decide] using
        high_rat_profile_degree .k186
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt ht)]
    exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_of_lt ht)

/-- The geometric derivative weights are represented by one shifted moment. -/
private def gammaRow : MiddleIntRow :=
  shiftedRow.moment 83 7 4

/-- Identify the computed integer moment with the real moment after casting. -/
private theorem gamma_row_map :
    (gammaRow.poly 83).map (Rat.castHom ℝ) =
      middleMomentPoly HighGaussianKernel.k186.realProfile (7 / 4) 65 := by
  have h := shiftedRow.poly_moment 83 7 4 row_den_pos.ne' (by decide) (by decide +kernel)
  rw [shifted_row_poly] at h
  simp only [Int.cast_ofNat] at h
  rw [gammaRow, h, ← middle_moment_translate _ (by decide +kernel : (7 / 4 : ℚ) ≠ 0)]
  have hdeg :=
    Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective (p :=
      HighGaussianKernel.k186.ratProfile)
  rw [high_comp_profile_map] at hdeg
  simp only [middleMomentPoly, Polynomial.map_comp, Polynomial.map_sum, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul, Rat.coe_castHom,
    ← Polynomial.hasseDeriv_map, hdeg, high_comp_profile_map, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_natCast, Rat.cast_pow]

/-- Sum the positive Gamma-moment coefficients with rational monomial weights. -/
private def gammaSum : ℚ :=
  let row := gammaRow
  ∑ i ∈ Finset.range 84, (max 0 (row.num i) : ℤ) * ((3 / 22 : ℚ) * i) ^ i

/-- The fixed Gamma moment fits the allocated rational budget. -/
private theorem gamma_sum_check :
    (7 / 2) * (gammaSum / (gammaRow.den : ℚ)) ≤
      ((gaussianMidExpGrid 14300).lower : ℤ) / 100000000 / 10 ^ 6 := by
  decide +kernel

/-- The Gamma moment at the far anchor has budget at most one
millionth, after applying the decay factor and the geometric weight. -/
public theorem k186_gamma_ray_coeff_cap :
    let P := middleMomentPoly HighGaussianKernel.k186.realProfile (7 / 4) 65
    (7 / 2) *
        (Real.exp (-(11 / 4 : ℝ) * 65) *
          ∑ i ∈ Finset.range (P.natDegree + 1), max 0 (P.coeff i) * ((3 / 22 : ℝ) * i) ^ i) ≤
      1 / 10 ^ 6 := by
  intro P
  have hd : 0 < gammaRow.den := by exact mul_pos row_den_pos (pow_pos (by decide : (0 : ℤ) < 7) _)
  have hdR : (0 : ℝ) < gammaRow.den := Int.cast_pos.mpr hd
  have hP : (gammaRow.poly 83).map (Rat.castHom ℝ) = P := by exact gamma_row_map
  have hdeg : P.natDegree ≤ 83 := by
    rw [← hP, Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective]
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos 83) _)
  have hcoeff (i : ℕ) (hi : i < 84) : (gammaRow.num i : ℝ) / gammaRow.den = P.coeff i := by
    rw [← hP, Polynomial.coeff_map, Rat.coe_castHom, gammaRow.poly_coeff (Nat.le_of_lt_succ hi),
      Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
  have hs :
    (gammaSum : ℝ) / gammaRow.den =
      ∑ i ∈ Finset.range 84, max 0 (P.coeff i) * ((3 / 22 : ℝ) * i) ^ i := by
    simp only [gammaSum, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_pow, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Int.cast_max, Int.cast_zero, mul_div_right_comm, div_eq_mul_inv (max _ _),
      mul_comm (max _ _), mul_max_of_nonneg _ _ (inv_nonneg.mpr hdR.le), mul_zero,
      mul_comm (↑gammaRow.den : ℝ)⁻¹, ← div_eq_mul_inv, hcoeff i (Finset.mem_range.mp hi)]
  have hshort :
    (∑ i ∈ Finset.range (P.natDegree + 1), max 0 (P.coeff i) * ((3 / 22 : ℝ) * i) ^ i) ≤
      ∑ i ∈ Finset.range 84, max 0 (P.coeff i) * ((3 / 22 : ℝ) * i) ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hdeg))
      (fun i _ _ ↦
        mul_nonneg (le_max_left _ _)
          (pow_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg i)) i))
  have hraw := (Rat.cast_le (K := ℝ)).mpr gamma_sum_check
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat] at hraw
  rw [hs] at hraw
  have hexp := (gaussian_mid_exp_grid 14300).1
  norm_num only [Nat.cast_ofNat, Int.cast_ofNat] at hexp
  have hb :=
    (mul_le_mul_of_nonneg_left hshort (by norm_num only : (0 : ℝ) ≤ 7 / 2)).trans
      (hraw.trans (div_le_div_of_nonneg_right hexp (by norm_num only)))
  rw [neg_mul, Real.exp_neg]
  norm_num only at hb ⊢
  have he := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.exp_pos (715 / 4 : ℝ)).le)
  rw [div_eq_mul_inv (Real.exp _), ← mul_assoc (Real.exp (715 / 4 : ℝ))⁻¹ (Real.exp (715 / 4 : ℝ)),
    inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul] at he
  simpa only [← mul_assoc, mul_comm (Real.exp (715 / 4 : ℝ))⁻¹ (7 / 2 : ℝ), one_div] using he

end PseudoPrime.PrimeTestBounds.MillerRabin
