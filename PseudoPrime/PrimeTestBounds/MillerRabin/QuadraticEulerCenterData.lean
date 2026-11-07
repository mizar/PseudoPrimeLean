/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaFiniteCenterScalarCertificate

/-! # Refined node intervals at the Euler center cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Thirty-decimal rational intervals for all resolvent powers at 50000.
Integer twentieth-root bisection generates endpoints; the next theorem
certifies them in Lean. These refine the center's signed scalar bounds. -/
def center50000Ratios (a : ℚ) : ℚ × ℚ :=
  if a = 11 / 20 then
    (11643444983920920836769674 / 1000000000000000000000000000000,
      11643444983920920836769675 / 1000000000000000000000000000000)
  else
    if a = 13 / 20 then
      (3946249092372012907350058 / 1000000000000000000000000000000,
        3946249092372012907350059 / 1000000000000000000000000000000)
    else
      if a = 16 / 20 then
        (778644094952346782991164 / 1000000000000000000000000000000,
          778644094952346782991165 / 1000000000000000000000000000000)
      else
        if a = 20 / 20 then
          (89442719099991587856366 / 1000000000000000000000000000000,
            89442719099991587856367 / 1000000000000000000000000000000)
        else
          if a = 26 / 20 then
            (3482202253184496556545 / 1000000000000000000000000000000,
              3482202253184496556546 / 1000000000000000000000000000000)
          else
            if a = 34 / 20 then
              (45947934199881400271 / 1000000000000000000000000000000,
                45947934199881400272 / 1000000000000000000000000000000)
            else
              if a = 46 / 20 then
                (69644045063689931 / 1000000000000000000000000000000,
                  69644045063689932 / 1000000000000000000000000000000)
              else
                if a = 64 / 20 then
                  (4109708171864 / 1000000000000000000000000000000,
                    4109708171865 / 1000000000000000000000000000000)
                else
                  if a = 90 / 20 then
                    (3200000 / 1000000000000000000000000000000,
                      3200001 / 1000000000000000000000000000000)
                  else
                    if a = 140 / 20 then
                      (0 / 1000000000000000000000000000000, 1 / 1000000000000000000000000000000)
                    else (0, 0)

/-- Every refined cutoff power interval passes exact rational root checks.
Kernel evaluation certifies each endpoint. This supplies real-power bounds
for the finite Euler center without a floating-point oracle. -/
theorem center50000_ratios_check :
    Analysis.gammaFiniteEulerRatioCheck 50000 center50000Ratios = true := by decide +kernel

/-- The checked cutoff intervals enclose the actual signed Euler weight at
50000. Apply the ratio-check soundness theorem. These endpoints bound the
Chebyshev boundary term of the finite Euler center. -/
theorem center50000_weight_bounds :
    (Analysis.gammaFiniteEulerLower center50000Ratios : ℝ) ≤
        Analysis.gammaResolventEulerWeight 50000 ∧
      Analysis.gammaResolventEulerWeight 50000 ≤
        (Analysis.gammaFiniteEulerUpper center50000Ratios : ℝ) :=
  Analysis.gamma_finite_ratio_check_euler_bounds center50000_ratios_check

/-- Signed rational node sums enclose the actual logarithmic Euler slope at
50000. Apply the weighted interval theorem and the exact slope identity.
These endpoints control the logarithmically weighted boundary term. -/
theorem center50000_slope_bounds :
    (LLS.gammaFiniteWeightedLower LLS.gammaSlopeRationalCoefficient center50000Ratios : ℝ) ≤
        LLS.gammaEulerLogSlope 50000 ∧
      LLS.gammaEulerLogSlope 50000 ≤
        (LLS.gammaFiniteWeightedUpper LLS.gammaSlopeRationalCoefficient center50000Ratios : ℝ) := by
  have h :=
    LLS.gamma_finite_weighted_bounds center50000_ratios_check LLS.gammaSlopeRationalCoefficient
  rw [← LLS.gamma_slope_eq_weighted] at h
  exact h

/-- Signed rational node sums enclose the actual integrated Euler main term
at cutoff 50000. Use the rational tail coefficients and the exact power
identity. This supplies the final scalar component of the finite center. -/
theorem center50000_tail_main_bounds :
    (LLS.gammaFiniteWeightedLower (LLS.gammaTailRationalCoefficient 50000) center50000Ratios : ℝ) ≤
        LLS.gammaEulerTailMain 50000 ∧
      LLS.gammaEulerTailMain 50000 ≤
        (LLS.gammaFiniteWeightedUpper (LLS.gammaTailRationalCoefficient 50000) center50000Ratios :
          ℝ) := by
  have h :=
    LLS.gamma_finite_weighted_bounds center50000_ratios_check
      (LLS.gammaTailRationalCoefficient 50000)
  rw [← LLS.gamma_tail_main_eq_weighted (by norm_num only : (0 : ℚ) < 50000)] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
