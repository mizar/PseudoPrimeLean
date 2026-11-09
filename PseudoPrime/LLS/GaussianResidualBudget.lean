/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GaussianPrefixComparison
public import PseudoPrime.LLS.GaussianQuadraticBounds

/-! Gaussian prefix residual bound from a quadratic certificate. -/

@[expose] public section

namespace PseudoPrime.LLS

/-- If r times t^8 is at least one, t bounds the inverse eighth root of r.
This transfers a rational endpoint certificate to every larger radius. -/
private theorem rpow_neg_one_eighth_le {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t)
    (hbound : 1 ≤ r * t ^ 8) : r ^ (-(1 / 8 : ℝ)) ≤ t := by
  have hinv : r⁻¹ ≤ t ^ 8 := by
    rw [← one_div]
    exact (div_le_iff₀ hr).2 (by nlinarith only [hbound])
  have hp := Real.rpow_le_rpow (inv_nonneg.mpr hr.le) hinv (by norm_num only : (0 : ℝ) ≤ 1 / 8)
  have hl : (r⁻¹) ^ (1 / 8 : ℝ) = r ^ (-(1 / 8 : ℝ)) := by
    rw [Real.inv_rpow hr.le, Real.rpow_neg hr.le]
  have ht8 : (t ^ 8) ^ (1 / 8 : ℝ) = t := by
    rw [← Real.rpow_natCast t 8, ← Real.rpow_mul ht]
    norm_num only [Real.rpow_one]
  simpa only [hl, ht8] using hp

/-- Rewrite the Gaussian ninth-eighth tail as an inverse radius times an inverse
eighth root. This form permits a rational endpoint bound. -/
private theorem sq_rpow_neg_nine_sixteenths {r : ℝ} (hr : 0 < r) :
    (r ^ 2) ^ (-9 / 16 : ℝ) = r⁻¹ * r ^ (-(1 / 8 : ℝ)) := by
  have h : (r ^ 2) ^ (-9 / 16 : ℝ) = r ^ (-(9 / 8 : ℝ)) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num only
  rw [h, show (-(9 / 8 : ℝ)) = -1 + (-(1 / 8 : ℝ)) by norm_num only, Real.rpow_add hr,
    Real.rpow_neg_one]

/-- Constant term in the Gaussian residual bound for prefix mass P. -/
noncomputable def gaussianResidualConstant (P : ℝ) : ℝ :=
  13 + 3 * (12871 / 1000 - 2 * P) +
    (7 / 2) * (2129 / 2000) * (10971611 / 5000000) / (20115621 / 25000000)

/-- Inverse-square-root coefficient in the Gaussian residual bound. -/
noncomputable def gaussianResidualSqrtCoeff : ℝ :=
  21 * (2129 / 2000) - (7 / 2) * (2129 / 2000) * (28794111 / 12500000) / (20115621 / 25000000)

/-- Inverse-radius coefficient after applying the root budget. -/
noncomputable def gaussianResidualInverseCoeff (R : ℝ) : ℝ :=
  12 * (2129 / 2000) + 4 * (1839 / 1000) * (2129 / 2000) -
    (7 / 2) * (2129 / 2000) * R / (20115621 / 25000000)

/-- The quadratic coefficient after bounding both reciprocal tails. Its positivity is
checked separately for each residual certificate. -/
noncomputable def gaussianResidualQuadraticCoeff (rho R t : ℝ) : ℝ :=
  -gaussianResidualInverseCoeff R - (1419 / 10) * t - (512 / 9) / rho

/-- A clipped Gaussian budget and a rational eighth-root certificate bound the exact
prefix residual below R. Keep the negative inverse-radius contribution from the budget,
bound the two tails, and apply the certified quadratic completion. -/
theorem gaussianResidual_lt_of_certificate {n : ℕ} {P R rho t r : ℝ} (hrho : 0 < rho) (hr : rho ≤ r)
    (ht : 0 ≤ t) (ht8 : 1 ≤ rho * t ^ 8)
    (hbudget :
      (20115621 / 25000000 : ℝ) * Real.log n + R + (28794111 / 12500000 : ℝ) * Real.sqrt r ≤
        (10971611 / 5000000 : ℝ) * r)
    (hH : 0 < gaussianResidualQuadraticCoeff rho R t)
    (hcert :
      gaussianResidualSqrtCoeff ^ 2 <
        4 * gaussianResidualQuadraticCoeff rho R t * (R - gaussianResidualConstant P)) :
    4 *
          (21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * Real.sqrt r) +
            1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
        13 +
        3 * PaperStatements.gaussianPrefixError P n (r ^ 2) <
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
  have htbound := rpow_neg_one_eighth_le hrpos ht h8
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
  have hquad := quadratic_lt_of_discriminant hH hcert (z := z)
  have hres :
    4 * (21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * s) + 1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
        13 +
        3 * PaperStatements.gaussianPrefixError P n (r ^ 2) ≤
      gaussianResidualConstant P + gaussianResidualSqrtCoeff * z -
        gaussianResidualQuadraticCoeff rho R t * z ^ 2 := by
    dsimp only [PaperStatements.gaussianPrefixError]
    rw [Real.sqrt_sq hrpos.le, sq_rpow_neg_nine_sixteenths hrpos, hz2]
    dsimp only [gaussianResidualConstant, gaussianResidualSqrtCoeff, gaussianResidualQuadraticCoeff,
      gaussianResidualInverseCoeff]
    dsimp only [z, w] at *
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow] at *
    norm_num only at hb htail hw2 ⊢
    rw [← inv_pow, pow_two]
    nlinarith only [hb, htail, hw2]
  exact hres.trans_lt hquad

end PseudoPrime.LLS
