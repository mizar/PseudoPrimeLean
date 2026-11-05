/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusCertificates
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusWitness

/-! # Gaussian surplus residual bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A clipped Gaussian budget and a rational eighth-root certificate bound the exact
prefix residual below R. Keep the negative inverse-radius contribution from the budget,
bound the two tails, and apply the certified quadratic completion. -/
theorem jointSurplus_residual_lt {n : ℕ} {P R rho t r : ℝ} (hrho : 0 < rho) (hr : rho ≤ r)
    (ht : 0 ≤ t) (ht8 : 1 ≤ rho * t ^ 8)
    (hbudget :
      (20115621 / 25000000 : ℝ) * Real.log n + R + (28794111 / 12500000 : ℝ) * Real.sqrt r ≤
        (10971611 / 5000000 : ℝ) * r)
    (hH : 0 < jointSurplusH rho R t)
    (hcert : jointSurplusB1 ^ 2 < 4 * jointSurplusH rho R t * (R - jointSurplusB0 P)) :
    4 *
          (21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * Real.sqrt r) +
            1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError P n (r ^ 2) <
      R := by
  have hrpos : 0 < r := hrho.trans_le hr
  let s := Real.sqrt r
  let z := s⁻¹
  let w := r⁻¹
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hs2 : s ^ 2 = r := Real.sq_sqrt hrpos.le
  have hw : 0 ≤ w := inv_nonneg.mpr hrpos.le
  have hunit : r * w = 1 := mul_inv_cancel₀ hrpos.ne'
  have hsz : s * w = z := by
    dsimp only [z, w]
    rw [← hs2, pow_two, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ hspos.ne', one_mul]
  have hz2 : z ^ 2 = w := by
    dsimp only [z, w]
    rw [inv_pow, hs2]
  have h8 : 1 ≤ r * t ^ 8 := by
    have hh := mul_le_mul_of_nonneg_right hr (pow_nonneg ht 8)
    linarith only [ht8, hh]
  have htbound := jointSurplus_invEighth_le hrpos ht h8
  have htail := mul_le_mul_of_nonneg_left htbound hw
  have hwrho : w ≤ rho⁻¹ := (inv_le_inv₀ hrpos hrho).2 hr
  have hw2 := mul_le_mul_of_nonneg_left hwrho hw
  have hb := mul_le_mul_of_nonneg_right hbudget hw
  have hbl :
    ((20115621 / 25000000 : ℝ) * Real.log n + R + (28794111 / 12500000 : ℝ) * s) * w =
      (20115621 / 25000000 : ℝ) * (Real.log n * w) + R * w + (28794111 / 12500000 : ℝ) * z := by
    calc
      _ =
          (20115621 / 25000000 : ℝ) * (Real.log n * w) + R * w +
            (28794111 / 12500000 : ℝ) * (s * w) :=
        by ring
      _ = _ := by rw [hsz]
  have hbr : ((10971611 / 5000000 : ℝ) * r) * w = 10971611 / 5000000 := by
    rw [mul_assoc, hunit, mul_one]
  rw [hbl, hbr] at hb
  have hquad := jointSurplus_quadratic_lt hH hcert (z := z)
  have hres :
    4 * (21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * s) + 1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError P n (r ^ 2) ≤
      jointSurplusB0 P + jointSurplusB1 * z - jointSurplusH rho R t * z ^ 2 := by
    dsimp only [LLS.PaperStatements.gaussianPrefixError]
    rw [Real.sqrt_sq hrpos.le, jointSurplus_tail_eq hrpos, hz2]
    dsimp only [jointSurplusB0, jointSurplusB1, jointSurplusH, jointSurplusB2]
    dsimp only [z, w] at *
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow] at *
    norm_num only at hb htail hw2 ⊢
    rw [← inv_pow, pow_two]
    nlinarith only [hb, htail, hw2]
  exact hres.trans_lt hquad

end PseudoPrime.PrimeTestBounds.MillerRabin
