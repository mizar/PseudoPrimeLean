/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Gaussian030AbstractGap
public import PseudoPrime.PrimeTestBounds.MillerRabin.Gaussian030AnalyticBounds

/-! # Scalar comparison for the explicit Gaussian witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The explicit Gaussian witness scalar inequality follows from the high-range
radius, root, logarithm, and remainder bounds. The square-root cutoff and
exponential moment are bounded only on the loss side; the algebra identifies
the normalized principal gap with the proved rational high-range inequality. -/
theorem gaussian030_scalar_algebra {L r t z q e w : ℝ} (hL : 1000 ≤ L)
    (hr : r = (377 / 1000 : ℝ) * L) (ht : 19 ≤ t) (htL : t ≤ L / 50) (ht2 : t ^ 2 = r)
    (hz : z ≤ r / 20) (hq : q ≤ 1 / r) (he : e ≤ 2129 / 2000) (hw : w ≤ (29 / 20 : ℝ) * r) :
    (20115621 / 25000000 : ℝ) * L + 683 / 50 - 108 / 25 - 4 * (1129059 / 200000 : ℝ) +
        (1536 / 27 : ℝ) / r ^ 2 +
        (2129 / 2000 : ℝ) * (((7 / 3 : ℝ) * L + 12) / r) +
        (1419 / 10 : ℝ) * q <
      4 *
          (r * (81470555 / 100000000 : ℝ) -
            (7 / 50 : ℝ) / r *
              ((32 / 63 : ℝ) * ((7 / 20 : ℝ) / t) * ((21 / 10 : ℝ) * r ^ 2) +
                (231 / 2500 : ℝ) * (w + 1) / ((7 / 20 : ℝ) / t) +
                1839 / 1000) -
            ((231 / 5000 : ℝ) * w + (1839 / 1000 : ℝ) * z + 2) / r) -
        (r * e + 13) := by
  have hrL : 377 ≤ r := by
    rw [hr]; linarith only [hL]
  have hr0 : 0 < r := by linarith only [hrL]
  have ht0 : 0 < t := by linarith only [ht]
  have hA := gaussian030_abstract_gap hL hr ht htL hz hq
  let budget : ℝ :=
    (20115621 / 25000000 : ℝ) * L + 683 / 50 - 108 / 25 - 4 * (1129059 / 200000 : ℝ) +
      (1536 / 27 : ℝ) / r ^ 2 +
      (2129 / 2000 : ℝ) * (((7 / 3 : ℝ) * L + 12) / r) +
      (1419 / 10 : ℝ) * q
  let target : ℝ :=
    4 *
        (r * (81470555 / 100000000 : ℝ) -
          (7 / 50 : ℝ) / r *
            ((32 / 63 : ℝ) * ((7 / 20 : ℝ) / t) * ((21 / 10 : ℝ) * r ^ 2) +
              (231 / 2500 : ℝ) * (w + 1) / ((7 / 20 : ℝ) / t) +
              1839 / 1000) -
          ((231 / 5000 : ℝ) * w + (1839 / 1000 : ℝ) * z + 2) / r) -
      (r * e + 13)
  let upper : ℝ :=
    4 *
        (r * (81470555 / 100000000 : ℝ) -
          (7 / 50 : ℝ) / r *
            ((32 / 63 : ℝ) * ((7 / 20 : ℝ) / t) * ((21 / 10 : ℝ) * r ^ 2) +
              (231 / 2500 : ℝ) * ((29 / 20 : ℝ) * r + 1) / ((7 / 20 : ℝ) / t) +
              1839 / 1000) -
          ((231 / 5000 : ℝ) * ((29 / 20 : ℝ) * r) + (1839 / 1000 : ℝ) * z + 2) / r) -
      (r * (2129 / 2000 : ℝ) + 13)
  have hid :
    upper - budget =
      ((4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) * r) -
        ((20115621 / 25000000 : ℝ) * L +
          (4 * (7 / 50) *
              ((32 / 63) * (21 / 10) * (7 / 20) + (231 / 2500) * (29 / 20) / (7 / 20))) *
            t +
          1339 / 50000 +
          (4 * (7 / 50) * (231 / 2500) / (7 / 20)) / t +
          (12 * (2129 / 2000) + (7 / 3) * (2129 / 2000) * L + 4 * (7 / 50) * (1839 / 1000) +
              4 * (1839 / 1000) * z +
              8) /
            r +
          (512 / 9) / r ^ 2 +
          (1419 / 10) * q) := by
    dsimp only [upper, budget]
    field_simp [hr0.ne', ht0.ne']
    rw [← ht2]
    ring
  have hmax : budget < upper := by linarith only [hA, hid]
  have hwidth :
    (231 / 2500 : ℝ) * (w + 1) / ((7 / 20 : ℝ) / t) ≤
      (231 / 2500 : ℝ) * ((29 / 20 : ℝ) * r + 1) / ((7 / 20 : ℝ) / t) := by
    apply div_le_div_of_nonneg_right _ (div_nonneg (by norm_num only) ht0.le)
    linarith only [hw]
  have hcost :=
    mul_le_mul_of_nonneg_left hwidth (div_nonneg (by norm_num only : (0 : ℝ) ≤ 7 / 50) hr0.le)
  have herror :
    ((231 / 5000 : ℝ) * w + (1839 / 1000 : ℝ) * z + 2) / r ≤
      ((231 / 5000 : ℝ) * ((29 / 20 : ℝ) * r) + (1839 / 1000 : ℝ) * z + 2) / r := by
    apply div_le_div_of_nonneg_right _ hr0.le
    linarith only [hw]
  have he' := mul_le_mul_of_nonneg_left he hr0.le
  have hcomp : upper ≤ target := by
    dsimp only [upper, target]
    linarith only [hcost, herror, he']
  change budget < target
  exact hmax.trans_le hcomp

end PseudoPrime.PrimeTestBounds.MillerRabin
