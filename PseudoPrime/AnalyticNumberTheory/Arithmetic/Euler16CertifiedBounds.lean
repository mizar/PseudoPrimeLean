/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates

/-! # Certified sixteen-term Euler bounds at three rational exponents -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Rational endpoints for the sixteen-term Euler certificate.
Inputs index the bases 1 through 16; out-of-range indices return zero.
Soundness is checked below before these data are used analytically. -/
private def euler16LogUpper (i : ℕ) : ℚ :=
  ([1 / 1000000, 693148 / 1000000, 1098613 / 1000000, 1386295 / 1000000, 1609438 / 1000000,
          1791760 / 1000000, 1945911 / 1000000, 2079442 / 1000000, 2197225 / 1000000,
          2302586 / 1000000, 2397896 / 1000000, 2484907 / 1000000, 2564950 / 1000000,
          2639058 / 1000000, 2708051 / 1000000, 2772589 / 1000000] :
        List ℚ).getD
    i 0

/-- Rational endpoints for the sixteen-term Euler certificate.
Inputs index the bases 1 through 16; out-of-range indices return zero.
Soundness is checked below before these data are used analytically. -/
private def euler16FifthLower (i : ℕ) : ℚ :=
  ([100000000 / 100000000, 43527528 / 100000000, 26758052 / 100000000, 18946457 / 100000000,
          14495593 / 100000000, 11647118 / 100000000, 9680155 / 100000000, 8246924 / 100000000,
          7159933 / 100000000, 6309573 / 100000000, 5627672 / 100000000, 5069702 / 100000000,
          4605406 / 100000000, 4213532 / 100000000, 3878738 / 100000000, 3589682 / 100000000] :
        List ℚ).getD
    i 0

/-- Rational endpoints for the sixteen-term Euler certificate.
Inputs index the bases 1 through 16; out-of-range indices return zero.
Soundness is checked below before these data are used analytically. -/
private def euler16FifthUpper (i : ℕ) : ℚ :=
  ([100000000 / 100000000, 43527529 / 100000000, 26758053 / 100000000, 18946458 / 100000000,
          14495594 / 100000000, 11647119 / 100000000, 9680156 / 100000000, 8246925 / 100000000,
          7159934 / 100000000, 6309574 / 100000000, 5627673 / 100000000, 5069703 / 100000000,
          4605407 / 100000000, 4213533 / 100000000, 3878739 / 100000000, 3589683 / 100000000] :
        List ℚ).getD
    i 0

/-- Exact kernel check of the finite logarithm, power and integral-tail endpoints.
All inputs are rational. A true result supports the unconditional Euler-series cap. -/
private theorem euler16_fifth_check :
    rationalEulerIntervalCheck 1 5 16 32 euler16LogUpper euler16FifthLower euler16FifthUpper
        (2772589 / 1000000) (57434918 / 100000000) (56742728 / 100000000) (4481 / 1000) =
      true := by
  decide +kernel

/-- Rational endpoints for the sixteen-term Euler certificate.
Inputs index the bases 1 through 16; out-of-range indices return zero.
Soundness is checked below before these data are used analytically. -/
private def euler16TwentySevenHundredthsLower (i : ℕ) : ℚ :=
  ([100000000 / 100000000, 41465977 / 100000000, 24777415 / 100000000, 17194272 / 100000000,
          12951142 / 100000000, 10274197 / 100000000, 8447447 / 100000000, 7129773 / 100000000,
          6139203 / 100000000, 5370317 / 100000000, 4758075 / 100000000, 4260296 / 100000000,
          3848504 / 100000000, 3502816 / 100000000, 3208958 / 100000000, 2956430 / 100000000] :
        List ℚ).getD
    i 0

/-- Rational endpoints for the sixteen-term Euler certificate.
Inputs index the bases 1 through 16; out-of-range indices return zero.
Soundness is checked below before these data are used analytically. -/
private def euler16TwentySevenHundredthsUpper (i : ℕ) : ℚ :=
  ([100000000 / 100000000, 41465978 / 100000000, 24777416 / 100000000, 17194273 / 100000000,
          12951143 / 100000000, 10274198 / 100000000, 8447448 / 100000000, 7129774 / 100000000,
          6139204 / 100000000, 5370318 / 100000000, 4758076 / 100000000, 4260297 / 100000000,
          3848505 / 100000000, 3502817 / 100000000, 3208959 / 100000000, 2956431 / 100000000] :
        List ℚ).getD
    i 0

/-- Exact kernel check of the finite logarithm, power and integral-tail endpoints.
All inputs are rational. A true result supports the unconditional Euler-series cap. -/
private theorem euler16_twentySevenHundredths_check :
    rationalEulerIntervalCheck 27 100 16 32 euler16LogUpper euler16TwentySevenHundredthsLower
        euler16TwentySevenHundredthsUpper (2772589 / 1000000) (47302883 / 100000000)
        (46534900 / 100000000) (1597 / 500) =
      true := by
  decide +kernel

/-- Rational endpoints for the sixteen-term Euler certificate.
Inputs index the bases 1 through 16; out-of-range indices return zero.
Soundness is checked below before these data are used analytically. -/
private def euler16SevenTenthsLower (i : ℕ) : ℚ :=
  ([100000000 / 100000000, 30778610 / 100000000, 15448768 / 100000000, 9473228 / 100000000,
          6482626 / 100000000, 4754916 / 100000000, 3658755 / 100000000, 2915728 / 100000000,
          2386644 / 100000000, 1995262 / 100000000, 1696806 / 100000000, 1463497 / 100000000,
          1277309 / 100000000, 1126113 / 100000000, 1001485 / 100000000, 897420 / 100000000] :
        List ℚ).getD
    i 0

/-- Rational endpoints for the sixteen-term Euler certificate.
Inputs index the bases 1 through 16; out-of-range indices return zero.
Soundness is checked below before these data are used analytically. -/
private def euler16SevenTenthsUpper (i : ℕ) : ℚ :=
  ([100000000 / 100000000, 30778611 / 100000000, 15448769 / 100000000, 9473229 / 100000000,
          6482627 / 100000000, 4754917 / 100000000, 3658756 / 100000000, 2915729 / 100000000,
          2386645 / 100000000, 1995263 / 100000000, 1696807 / 100000000, 1463498 / 100000000,
          1277310 / 100000000, 1126114 / 100000000, 1001486 / 100000000, 897421 / 100000000] :
        List ℚ).getD
    i 0

/-- Exact kernel check of the finite logarithm, power and integral-tail endpoints.
All inputs are rational. A true result supports the unconditional Euler-series cap. -/
private theorem euler16_sevenTenths_check :
    rationalEulerIntervalCheck 7 10 16 32 euler16LogUpper euler16SevenTenthsLower
        euler16SevenTenthsUpper (2772589 / 1000000) (14358730 / 100000000) (13762133 / 100000000)
        (97 / 100) =
      true := by
  decide +kernel

/-- For real exponent sigma>=6 / 5, the Mangoldt Euler series is at most 4481 / 1000.
Certify sixteen prefix terms and the integral tails, then use exponent monotonicity.
No GRH, modulus or character assumptions are needed. -/
theorem tsum_vonMangoldt_le_six_fifths_certified {σ : ℝ} (hσ : (6 / 5 : ℝ) ≤ σ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) ≤ (4481 / 1000 : ℝ) := by
  have hc := rationalEulerIntervalCheck_sound euler16_fifth_check
  norm_num only [Nat.cast_ofNat, Rat.cast_div, Rat.cast_ofNat] at hc
  exact (tsum_vonMangoldt_div_rpow_antitone (by norm_num only) hσ).trans hc

/-- For real exponent sigma>=127 / 100, the Mangoldt Euler series is at most 1597 / 500.
Certify sixteen prefix terms and the integral tails, then use exponent monotonicity.
No GRH, modulus or character assumptions are needed. -/
theorem tsum_vonMangoldt_le_hundredTwentySeven_hundredths_certified {σ : ℝ}
    (hσ : (127 / 100 : ℝ) ≤ σ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) ≤ (1597 / 500 : ℝ) := by
  have hc := rationalEulerIntervalCheck_sound euler16_twentySevenHundredths_check
  norm_num only [Nat.cast_ofNat, Rat.cast_div, Rat.cast_ofNat] at hc
  exact (tsum_vonMangoldt_div_rpow_antitone (by norm_num only) hσ).trans hc

/-- For real exponent sigma>=17 / 10, the Mangoldt Euler series is at most 97 / 100.
Certify sixteen prefix terms and the integral tails, then use exponent monotonicity.
No GRH, modulus or character assumptions are needed. -/
theorem tsum_vonMangoldt_le_seventeen_tenths_certified {σ : ℝ} (hσ : (17 / 10 : ℝ) ≤ σ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) ≤ (97 / 100 : ℝ) := by
  have hc := rationalEulerIntervalCheck_sound euler16_sevenTenths_check
  norm_num only [Nat.cast_ofNat, Rat.cast_div, Rat.cast_ofNat] at hc
  exact (tsum_vonMangoldt_div_rpow_antitone (by norm_num only) hσ).trans hc

end PseudoPrime.AnalyticNumberTheory.Arithmetic
