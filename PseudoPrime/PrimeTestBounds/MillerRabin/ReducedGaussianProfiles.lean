/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientTriple

/-! # Rational Gaussian profile for reduced-contour triple witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational data for an index-four Gaussian witness at coefficient `C` from `T`.
The gamma and square-root floors, upper cutoff and strict comparison margin
control the Gaussian error budget for uniform three-prime Korselt moduli. -/
structure ReducedGaussianProfile where
  C : ℝ
  T : ℝ
  gamma : ℝ
  v : ℝ
  entry : 80000 ≤ T
  gammaLower : 367 / 1000 ≤ gamma
  lower : gamma ^ 2 ≤ (10 / 21) * C
  upper : (10 / 21) * C ≤ (289 / 625) ^ 2
  fourth : 0 < v ∧ v ^ 2 ≤ T
  margin : 90 < ((21943 / 10000) * gamma - 161 / 200 - (70 * (17 / 25)) / v) * T
/-- The first Gaussian certificate matches coefficient `39 / 100` at scale
`2 * 10 ^ 8`; its rational fields certify the three-factor comparison budget. -/
noncomputable def reducedGaussian039 : ReducedGaussianProfile where
  C := 39 / 100
  T := 200000000
  gamma := 86189 / 200000
  v := 14142
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- The squared-radius certificate at `80000` supports the short mean-counting
bridge with radius coefficient `3251 / 5000`. Its rational fields certify the
Gaussian triple budget independently of the contour profile. -/
noncomputable def reducedGaussian04228 : ReducedGaussianProfile where
  C := (3251 / 5000 : ℝ) ^ 2
  T := 80000
  gamma := 56 / 125
  v := 282
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- The Gaussian triple certificate for coefficient `161 / 500` from scale five hundred million. -/
noncomputable def reducedGaussian0322 : ReducedGaussianProfile where
  C := 161 / 500
  T := 500000000
  gamma := 195789 / 500000
  v := 22360
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- The Gaussian triple certificate for coefficient `3 / 10` from scale one billion. -/
noncomputable def reducedGaussian030 : ReducedGaussianProfile where
  C := 3 / 10
  T := 1000000000
  gamma := 94491 / 250000
  v := 31622
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- The Gaussian triple certificate for coefficient `71 / 250` from scale five billion. -/
noncomputable def reducedGaussian0284 : ReducedGaussianProfile where
  C := 71 / 250
  T := 5000000000
  gamma := 367747 / 1000000
  v := 70710
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
