/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ProfileCert
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleExp
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ProfileCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileGrid

/-! # A fixed K186 one-sided conductor coefficient sum -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Translate the checked unshifted K186 coefficients once to 58. -/
private def conductorRow : Array ℤ :=
  highGammaShiftInt 84 58 k186GridBase

/-- The normalized expanded input is already verified by the profile certificate. -/
private theorem conductor_expanded : HighGaussianKernel.k186.expandedCoeffRow = k186GammaExpanded :=
  (high_gamma_expanded_of_compact .k186 _ compact_ok).trans expanded_ok

/-- The unshifted coefficient denominator is the checked common denominator. -/
private theorem conductor_den :
    highGammaProfileDen 84 (highGammaBaseFrom 40 k186GammaExpanded) = k186GammaDen :=
  (high_gamma_den_of_row 40 _ den_row_ok).trans denLCM

/-- Relate the translated integer row to the analytic power basis. -/
private theorem conductor_entry (i : ℕ) (hi : i < 84) :
    (conductorRow[i]?.getD 0 : ℚ) =
      (k186GammaDen : ℚ) *
        (HighGaussianKernel.k186.ratProfile.comp (Polynomial.X + Polynomial.C 58)).coeff i := by
  have hbase : highGammaProfileInt 84 (highGammaBaseFrom 40 k186GammaExpanded) = k186GridBase :=
    high_gamma_profile_int_of_den 84 40 _ conductor_den rfl _ base_num_ok
  have hrow : highGammaShiftedProfile .k186 58 = conductorRow :=
    high_gamma_profile_of_stages .k186 58 conductor_expanded hbase rfl
  have h := high_gamma_shifted_cast .k186 58 hi
  simp only [hrow, Int.cast_ofNat] at h
  rw [high_cell_power_coeff .k186 (58 : ℚ) 1 hi, Polynomial.C_1, one_mul] at h
  have hd :
    highGammaProfileDen (2 * HighGaussianKernel.k186.degree + 4) (highGammaBaseRow .k186) =
      k186GammaDen := by
    change
      highGammaProfileDen 84 (highGammaBaseFrom 40 HighGaussianKernel.k186.expandedCoeffRow) =
        k186GammaDen
    rw [conductor_expanded]
    exact conductor_den
  rw [hd] at h
  exact h

/-- Sum the positive translated numerators with the monomial bound weights.
The exponential is checked separately, so the shift is evaluated once. -/
private def conductorSum : ℚ :=
  let row := conductorRow
  ∑ i ∈ Finset.range 84, (max 0 (row[i]?.getD 0) : ℤ) * ((i : ℚ) / 6) ^ i

/-- The exponential lower grid endpoint bounds the rational coefficient sum
after combining the two exponentials in the conductor prefactor. -/
private theorem conductor_sum_check :
    2 / (5196744155 / 10000000000 : ℚ) * (conductorSum / k186GammaDen) ≤
      200 * ((gaussianMidExpGrid 10640).lower : ℤ) / 100000000 := by
  decide +kernel

/-- The checked translated K186 row bounds the one-sided conductor
coefficient sum after its fixed exponential and radius normalization. -/
public theorem k186_conductor_coeff_cap :
    let P := HighGaussianKernel.k186.realProfile.comp (Polynomial.X + Polynomial.C 58)
    (2 / (5196744155 / 10000000000 : ℝ)) * Real.exp (-133) *
        (∑ i ∈ Finset.range (P.natDegree + 1), max 0 (P.coeff i) * ((i : ℝ) / 6) ^ i) ≤
      200 := by
  intro P
  have hp : 0 < (k186GammaDen : ℝ) := Nat.cast_pos.mpr (by decide)
  have hmap :
    (HighGaussianKernel.k186.ratProfile.comp (Polynomial.X + Polynomial.C (58 : ℚ))).map
        (Rat.castHom ℝ) =
      P := by
    simp only [P, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Rat.coe_castHom, Rat.cast_ofNat, high_comp_profile_map]
  have hdeg : P.natDegree ≤ 83 := by
    rw [← hmap, Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective,
      Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    exact high_rat_profile_degree .k186
  have hcoeff (i : ℕ) (hi : i < 84) :
    (conductorRow[i]?.getD 0 : ℝ) = (k186GammaDen : ℝ) * P.coeff i := by
    have h := congrArg (fun q : ℚ ↦ (q : ℝ)) (conductor_entry i hi)
    simpa only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_natCast, ← hmap, Polynomial.coeff_map,
      Rat.coe_castHom] using h
  have hsum :
    (conductorSum : ℝ) =
      (k186GammaDen : ℝ) * ∑ i ∈ Finset.range 84, max 0 (P.coeff i) * ((i : ℝ) / 6) ^ i := by
    simp only [conductorSum, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_pow,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show ((max 0 (conductorRow[i]?.getD 0) : ℤ) : ℝ) = max 0 (conductorRow[i]?.getD 0 : ℝ) by
        simp only [Int.cast_max, Int.cast_zero],
      hcoeff i (Finset.mem_range.mp hi)]
    have hm := mul_max_of_nonneg (0 : ℝ) (P.coeff i) hp.le
    rw [mul_zero] at hm
    rw [← hm, mul_assoc]
  have hshort :
    (∑ i ∈ Finset.range (P.natDegree + 1), max 0 (P.coeff i) * ((i : ℝ) / 6) ^ i) ≤
      ∑ i ∈ Finset.range 84, max 0 (P.coeff i) * ((i : ℝ) / 6) ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hdeg))
      (fun i _ _ ↦
        mul_nonneg (le_max_left _ _)
          (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num only)) _))
  have hraw := (Rat.cast_le (K := ℝ)).mpr conductor_sum_check
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_ofNat] at hraw
  rw [hsum, mul_comm (k186GammaDen : ℝ), mul_div_cancel_right₀ _ hp.ne'] at hraw
  have hexp := (gaussian_mid_exp_grid 10640).1
  norm_num only [Nat.cast_ofNat, Int.cast_ofNat] at hexp
  rw [mul_div_assoc] at hraw
  have hgrid := mul_le_mul_of_nonneg_left hexp (by norm_num only : (0 : ℝ) ≤ 200)
  have hle :=
    (mul_le_mul_of_nonneg_left hshort
          (by norm_num only : (0 : ℝ) ≤ 2 / (5196744155 / 10000000000))).trans
      (hraw.trans hgrid)
  rw [Real.exp_neg]
  have he := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (Real.exp_pos 133).le)
  rw [mul_left_comm _ (200 : ℝ), inv_mul_cancel₀ (Real.exp_pos 133).ne', mul_one] at he
  simpa only [mul_left_comm, ← mul_assoc] using he

end PseudoPrime.PrimeTestBounds.MillerRabin
