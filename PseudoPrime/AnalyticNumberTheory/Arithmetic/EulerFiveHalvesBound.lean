/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A uniform bound for the Euler series beyond five halves -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Rational upper endpoints for the logarithms of the integers from one to four.
The finite checker verifies these endpoints before they bound the Euler prefix. -/
private def logUpper : ℕ → ℚ
  | 0 => 1 / 1000
  | 1 => 7 / 10
  | 2 => 11 / 10
  | 3 => 139 / 100
  | _ => 0

/-- Rational lower endpoints for the four powers in the Euler prefix.
The checker verifies their relation to the exponent `-5 / 2`. -/
private def powerLower : ℕ → ℚ
  | 0 => 1
  | 1 => 176 / 1000
  | 2 => 64 / 1000
  | 3 => 31 / 1000
  | _ => 0

/-- Rational upper endpoints for the four powers in the Euler prefix.
The checker verifies their relation to the exponent `-5 / 2`. -/
private def powerUpper : ℕ → ℚ
  | 0 => 1
  | 1 => 177 / 1000
  | 2 => 65 / 1000
  | 3 => 32 / 1000
  | _ => 0

/-- Exact rational verification of the Euler prefix and integral-tail bounds at gap `3 / 2`.
The certificate gives a uniform scalar cap of `1 / 2` for the Mangoldt series. -/
private theorem eulerFiveHalves_check :
    rationalEulerIntervalCheck 3 2 4 32 logUpper powerLower powerUpper (139 / 100) (126 / 1000)
        (89 / 1000) (1 / 2) =
      true := by
  decide +kernel

/-- For every `σ ≥ 5 / 2`, the von Mangoldt Dirichlet series is at most `1 / 2`.
A four-term rational certificate bounds the series at `5 / 2`; termwise monotonicity
extends the bound to the right. This supplies the Euler term in zero-tail estimates. -/
theorem tsum_vonMangoldt_le_half {σ : ℝ} (hσ : (5 / 2 : ℝ) ≤ σ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) ≤ (1 / 2 : ℝ) := by
  have h := rationalEulerIntervalCheck_sound eulerFiveHalves_check
  norm_num only [Nat.cast_ofNat, Rat.cast_div, Rat.cast_ofNat,
    show (1 : ℝ) + 3 / 2 = 5 / 2 by norm_num only] at h
  exact (tsum_vonMangoldt_div_rpow_antitone (by norm_num only : (1 : ℝ) < 5 / 2) hσ).trans h

end PseudoPrime.AnalyticNumberTheory.Arithmetic
