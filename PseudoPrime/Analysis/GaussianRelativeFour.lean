/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMR1000Numerics

/-! # Relative Gaussian comparison with independently scaled radius -/

@[expose] public section

namespace PseudoPrime.Analysis

/--
Inputs: positive root s, radius r=s squared, scale a, width k/s, certified mass and
endpoint estimates, and an index-four comparison with conductor at most 2L.
Claim: the comparison implies the scalar budget at the independently scaled radius a*r.
Proof: bound the mass and endpoint independently, then clear the positive denominators.
Role: shares the exponent-four comparison between single-root and high-range bounds.
-/
theorem gaussianRelativeFour_scalar {s r a M I E Ec C L c h k A : ℝ} (hs : 0 < s) (hr : r = s ^ 2)
    (ha : 0 < a) (hk : 0 < k) (hh : h = k / s) (hh1 : h ≤ 1 / 2) (hI : M ≤ I) (hE : E ≤ Ec)
    (hC : C ≤ 2 * L) (hc : 0 ≤ c)
    (hcmp :
      (4 * (1 - h) * I - E) * (a * r) ≤
        c * C + 4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / (a * r)) * E) + 13 + 3 * A) :
    a * (4 * M - Ec) * r ≤
      2 * c * L + 4 * (a * M * k + 1 / (10 * k)) * s +
        4 * (21 * Ec / (10 * k * a * s) + 1839 * Ec / (1000 * a * r)) +
        13 +
        3 * A := by
  have hrpos : 0 < r := by
    rw [hr]; exact sq_pos_of_pos hs
  have hscale : 0 < a * r := mul_pos ha hrpos
  have hhpos : 0 < h := by
    rw [hh]; exact div_pos hk hs
  have hmass := mul_le_mul_of_nonneg_left hI (by linarith only [hh1] : 0 ≤ 4 * (1 - h))
  have hleft : (4 * (1 - h) * M - Ec) * (a * r) ≤ (4 * (1 - h) * I - E) * (a * r) := by
    exact mul_le_mul_of_nonneg_right (by linarith only [hmass, hE]) hscale.le
  have hweight : 0 ≤ (21 / (10 * h) + 1839 / 1000) / (a * r) := by
    exact
      div_nonneg
        (add_nonneg
          (div_nonneg (by norm_num only) (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 10) hhpos.le))
          (by norm_num only))
        hscale.le
  have hendpoint := mul_le_mul_of_nonneg_left hE hweight
  have hcond := mul_le_mul_of_nonneg_left hC hc
  have hid :
    (4 * (1 - h) * M - Ec) * (a * r) + 4 * (a * M * k + 1 / (10 * k)) * s +
        4 * (21 * Ec / (10 * k * a * s) + 1839 * Ec / (1000 * a * r)) =
      a * (4 * M - Ec) * r +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / (a * r)) * Ec) := by
    have hcancel := mul_inv_cancel₀ hs.ne'
    rw [hh, hr]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring_nf
    linear_combination -(4 * k * s * M * a + (42 / 5) * s⁻¹ * Ec * k⁻¹ * a⁻¹) * hcancel
  nlinarith only [hleft, hcmp, hendpoint, hcond, hid]

end PseudoPrime.Analysis
