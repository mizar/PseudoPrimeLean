/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMain570

/-! # Signed principal boundary bounds for the sixth-pole kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a nonpositive signed lower bound, use the left radius and the upper weight. -/
theorem signed_boundary_neg_570 {w l r m s : ℝ} (hl : 0 < l) (hr : l ≤ r) (hm : m ≤ 0) (hs : m ≤ s)
    (hw : 0 ≤ w) (hu : w ≤ 0.09105) : 4 * 0.09105 * m / l ≤ 4 * w * s / r := by
  apply
    le_trans _
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num only) hw))
        (hl.trans_le hr).le)
  apply (div_le_div_iff₀ hl (hl.trans_le hr)).mpr
  have h₁ := mul_le_mul_of_nonpos_right hu hm
  have h₂ := mul_le_mul_of_nonpos_left hr (mul_nonpos_of_nonneg_of_nonpos hw hm)
  linarith only [mul_le_mul_of_nonneg_right h₁ (hl.trans_le hr).le, h₂]

/-- For a nonnegative signed lower bound, use the right radius and the lower weight. -/
theorem signed_boundary_pos_570 {w u r m s : ℝ} (hr : 0 < r) (hu : r ≤ u) (hm : 0 ≤ m) (hs : m ≤ s)
    (hw : 0.09104 ≤ w) : 4 * 0.09104 * m / u ≤ 4 * w * s / r := by
  apply (div_le_div_iff₀ (hr.trans_le hu) hr).mpr
  have h₁ := mul_le_mul_of_nonneg_right hw hm
  have h₂ := mul_le_mul_of_nonneg_left hs (le_trans (by norm_num only) hw)
  have h₃ := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 0.09104) hm)
  linarith only [h₃, mul_le_mul_of_nonneg_right (h₁.trans h₂) (hr.trans_le hu).le]

/-- A nonpositive local psi lower bound transfers to the signed cutoff term
by using the left endpoint of the radius interval. -/
theorem cutoff_boundary_neg_570 {l r m : ℝ} (hl : 0 < l) (hr : l ≤ r) (hm : m ≤ 0)
    (hs : m ≤ Chebyshev.psi (r ^ 2) - r ^ 2) :
    4 * 0.09105 * m / l ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  have hp := hl.trans_le hr
  rw [quarter_cutoff_weight_570 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  have hb :=
    signed_boundary_neg_570 (w := (quarterKernel570.transform 1).re) hl hr hm hs
      (by linarith only [quarter_unit_weight_570.1]) (by linarith only [quarter_unit_weight_570.2])
  convert hb using 1
  ring

/-- A nonnegative local psi lower bound transfers to the signed cutoff term
by using the right endpoint of the radius interval. -/
theorem cutoff_boundary_pos_570 {r u m : ℝ} (hr : 0 < r) (hu : r ≤ u) (hm : 0 ≤ m)
    (hs : m ≤ Chebyshev.psi (r ^ 2) - r ^ 2) :
    4 * 0.09104 * m / u ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  rw [quarter_cutoff_weight_570 (sq_pos_of_pos hr), Real.sqrt_sq hr.le]
  have hb :=
    signed_boundary_pos_570 (w := (quarterKernel570.transform 1).re) hr hu hm hs
      (by linarith only [quarter_unit_weight_570.1])
  convert hb using 1
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
