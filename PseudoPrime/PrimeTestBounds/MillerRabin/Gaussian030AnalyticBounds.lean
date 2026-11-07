/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Gaussian030Parameters
public import PseudoPrime.Analysis.RealLog

/-! # Elementary analytic bounds for the Gaussian 0.30 entrance -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For radius at least 377, the logarithm of the Gaussian cutoff is at most
one twentieth of the radius. Apply a logarithmic tangent at 100 and rational
bounds for the two fixed logarithms. -/
theorem gaussian030_log_cutoff_le {r : ℝ} (hr : 377 ≤ r) :
    Real.log ((21 / 10 : ℝ) * r ^ 2) ≤ r / 20 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hlog100 : Real.log (100 : ℝ) ≤ 5 := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 100) (by norm_num only : (100 : ℝ) ≤ 128)
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num only, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, Real.log_two_lt_d9]
  have hloglam : Real.log (21 / 10 : ℝ) ≤ 11 / 10 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 21 / 10)
    linarith only [h]
  have ht := Analysis.log_le_log_add_sub_div (a := (100 : ℝ)) (y := r) (by norm_num only) hr0
  rw [Real.log_mul (by norm_num only : (21 / 10 : ℝ) ≠ 0) (pow_ne_zero _ hr0.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [hlog100, hloglam, ht, hr]

/-- At logarithmic scale at least 1000, the square root of the chosen radius
is at most `L/50`. Square the comparison and use the scale threshold. -/
theorem gaussian030_sqrt_radius_le {L : ℝ} (hL : 1000 ≤ L) :
    Real.sqrt (gaussian030Radius L) ≤ L / 50 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hr0 : 0 ≤ gaussian030Radius L := by
    dsimp only [gaussian030Radius]
    exact mul_nonneg (by norm_num only) hL0
  apply Real.sqrt_le_iff.mpr
  refine ⟨by linarith only [hL], ?_⟩
  dsimp only [gaussian030Radius]
  have hm := mul_nonneg (by linarith only [hL] : 0 ≤ L - 1000) hL0
  nlinarith only [hm, hL]

/-- For radius at least 377, the negative 9/16 power of its square is at most
its reciprocal. Monotonicity in the exponent and the square-root identity give
the remainder estimate required by the Gaussian scalar comparison. -/
theorem gaussian030_negative_power_le {r : ℝ} (hr : 377 ≤ r) : (r ^ 2) ^ (-9 / 16 : ℝ) ≤ 1 / r := by
  have hr0 : 0 < r := by linarith only [hr]
  have hx1 : 1 ≤ r ^ 2 := by nlinarith only [hr]
  have hpw := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num only : (-9 / 16 : ℝ) ≤ -1 / 2)
  have he : (r ^ 2) ^ (-1 / 2 : ℝ) = 1 / r := by
    rw [neg_div, Real.rpow_neg (zero_le_one.trans hx1), ← Real.sqrt_eq_rpow, Real.sqrt_sq hr0.le,
      one_div]
  rw [he] at hpw
  exact hpw

end PseudoPrime.PrimeTestBounds.MillerRabin
