/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Gaussian030ScalarAlgebra
public import PseudoPrime.PrimeTestBounds.MillerRabin.Gaussian030AnalyticBounds

/-! # Explicit Gaussian scalar gap for L at least 1000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At logarithmic scale at least 1000, the explicit Gaussian parameters satisfy
the strict scalar comparison required for the rejecting-prime witness. The
logarithm, square root, negative power, and exponential are bounded explicitly. -/
theorem gaussian030_scalar_gap {L : ℝ} (hL : 1000 ≤ L) :
    (20115621 / 25000000 : ℝ) * L + 683 / 50 - 108 / 25 - 4 * (1129059 / 200000 : ℝ) +
        (1536 / 27 : ℝ) / (gaussian030Scale L) +
        (2129 / 2000 : ℝ) * (((7 / 3 : ℝ) * L + 12) / Real.sqrt (gaussian030Scale L)) +
        (1419 / 10 : ℝ) * (gaussian030Scale L) ^ (-9 / 16 : ℝ) <
      4 *
          (Real.sqrt (gaussian030Scale L) * (81470555 / 100000000 : ℝ) -
            (7 / 50 : ℝ) / Real.sqrt (gaussian030Scale L) *
              ((32 / 63 : ℝ) * (gaussian030Width L) * ((21 / 10 : ℝ) * (gaussian030Scale L)) +
                (231 / 2500 : ℝ) * (Real.sqrt ((21 / 10 : ℝ) * (gaussian030Scale L)) + 1) /
                  (gaussian030Width L) +
                1839 / 1000) -
            ((231 / 5000 : ℝ) * Real.sqrt ((21 / 10 : ℝ) * (gaussian030Scale L)) +
                (1839 / 1000 : ℝ) * Real.log ((21 / 10 : ℝ) * (gaussian030Scale L)) +
                2) /
              Real.sqrt (gaussian030Scale L)) -
        (Real.sqrt (gaussian030Scale L) * Real.exp (1 / 16 : ℝ) + 13) := by
  let r : ℝ := gaussian030Radius L
  have hr : r = (377 / 1000 : ℝ) * L := rfl
  have hrL : 377 ≤ r := by
    rw [hr]; linarith only [hL]
  have hr0 : 0 < r := by linarith only [hrL]
  have ht : (19 : ℝ) ≤ Real.sqrt r := by
    apply (Real.le_sqrt (by norm_num only) hr0.le).2
    nlinarith only [hrL]
  have htL : Real.sqrt r ≤ L / 50 := gaussian030_sqrt_radius_le hL
  have ht2 : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr0.le
  have hz : Real.log ((21 / 10 : ℝ) * r ^ 2) ≤ r / 20 := gaussian030_log_cutoff_le hrL
  have hq : (r ^ 2) ^ (-9 / 16 : ℝ) ≤ 1 / r := gaussian030_negative_power_le hrL
  have he : Real.exp (1 / 16 : ℝ) ≤ 2129 / 2000 := Analysis.gaussian_endpoint_exp_le
  have hw : Real.sqrt ((21 / 10 : ℝ) * r ^ 2) ≤ (29 / 20 : ℝ) * r := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · nlinarith only [hr0]
    · nlinarith only [sq_nonneg r]
  have hA := gaussian030_scalar_algebra hL hr ht htL ht2 hz hq he hw
  have hscale : gaussian030Scale L = r ^ 2 := rfl
  have hwidth : gaussian030Width L = (7 / 20 : ℝ) / Real.sqrt r := by
    dsimp only [gaussian030Width, r]
    ring
  rw [hwidth, hscale, Real.sqrt_sq hr0.le]
  exact hA

end PseudoPrime.PrimeTestBounds.MillerRabin
