/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGeneral
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Chebyshev psi certificate on the interval from 11 to 17 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound

/-- Squaring certifies a nonnegative rational lower bound for the envelope. -/
private theorem envelope94 {n : ℕ} {z : ℝ} (_hz : 0 ≤ z) (h : z ^ 2 ≤ (47 / 50 : ℝ) ^ 2 * n) :
    z ≤ (47 / 50 : ℝ) * Real.sqrt n := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  nlinarith only [hs, hs0, _hz, h]

/-- Power-of-two LCM bounds and rational envelope bounds cover this half-open cell. -/
private theorem cell11 {x : ℝ} (ha : 11 ≤ x) (hb : x < 13) :
    |Chebyshev.psi x - x| ≤ (47 / 50 : ℝ) * Real.sqrt x := by
  have hl := Arithmetic.psi_bounds_of_lcm_pow_two (n := 11) (k := 14) (by decide) (by decide)
  have hu := Arithmetic.psi_bounds_of_lcm_pow_two (n := 12) (k := 14) (by decide) (by decide)
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hl hu
  exact
    Arithmetic.psi_sqrt_cross_cell (a := 11) (b := 13) (lo := 9704 / 1000) (hi := 10398 / 1000)
      (ca := 3117 / 1000) (cb := 3389 / 1000) (by norm_num only) (by norm_num only)
      (by norm_num only) ha hb (by linarith only [hl.1, Real.log_two_gt_d9])
      (by linarith only [hu.2, Real.log_two_lt_d9])
      (envelope94 (by norm_num only) (by norm_num only))
      (envelope94 (by norm_num only) (by norm_num only)) (by norm_num only) (by norm_num only)

/-- Power-of-two LCM bounds and rational envelope bounds cover this half-open cell. -/
private theorem cell13 {x : ℝ} (ha : 13 ≤ x) (hb : x < 16) :
    |Chebyshev.psi x - x| ≤ (47 / 50 : ℝ) * Real.sqrt x := by
  have hl := Arithmetic.psi_bounds_of_lcm_pow_two (n := 13) (k := 18) (by decide) (by decide)
  have hu := Arithmetic.psi_bounds_of_lcm_pow_two (n := 15) (k := 18) (by decide) (by decide)
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hl hu
  exact
    Arithmetic.psi_sqrt_cross_cell (a := 13) (b := 16) (lo := 12476 / 1000) (hi := 13170 / 1000)
      (ca := 3389 / 1000) (cb := 3760 / 1000) (by norm_num only) (by norm_num only)
      (by norm_num only) ha hb (by linarith only [hl.1, Real.log_two_gt_d9])
      (by linarith only [hu.2, Real.log_two_lt_d9])
      (envelope94 (by norm_num only) (by norm_num only))
      (envelope94 (by norm_num only) (by norm_num only)) (by norm_num only) (by norm_num only)

/-- Power-of-two LCM bounds and rational envelope bounds cover this half-open cell. -/
private theorem cell16 {x : ℝ} (ha : 16 ≤ x) (hb : x < 17) :
    |Chebyshev.psi x - x| ≤ (47 / 50 : ℝ) * Real.sqrt x := by
  have hl := Arithmetic.psi_bounds_of_lcm_pow_two (n := 16) (k := 19) (by decide) (by decide)
  have hu := Arithmetic.psi_bounds_of_lcm_pow_two (n := 16) (k := 19) (by decide) (by decide)
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hl hu
  exact
    Arithmetic.psi_sqrt_cross_cell (a := 16) (b := 17) (lo := 13169 / 1000) (hi := 13863 / 1000)
      (ca := 3760 / 1000) (cb := 3875 / 1000) (by norm_num only) (by norm_num only)
      (by norm_num only) ha hb (by linarith only [hl.1, Real.log_two_gt_d9])
      (by linarith only [hu.2, Real.log_two_lt_d9])
      (envelope94 (by norm_num only) (by norm_num only))
      (envelope94 (by norm_num only) (by norm_num only)) (by norm_num only) (by norm_num only)

/-- The three LCM cells prove the normalized error bound for all real points in [11, 17). -/
theorem psi94_on_11_17 {x : ℝ} (ha : 11 ≤ x) (hb : x < 17) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (47 / 50 : ℝ) := by
  have hx : 0 < x := by linarith only [ha]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
  by_cases h13 : x < 13
  · exact cell11 ha h13
  by_cases h16 : x < 16
  · exact cell13 (le_of_not_gt h13) h16
  exact cell16 (le_of_not_gt h16) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound
