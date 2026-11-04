/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeProfiles

/-! # Scale-dependent coefficients for the relative Gaussian comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The radius slope for the index-four Gaussian comparison at logarithmic scale `L`.
The inverse-square-root term pays the relative error and `39 / L` leaves a strict
margin over the residual budget of 38. It will define a scale-dependent profile. -/
noncomputable def adaptiveGaussianA (L : ℝ) : ℝ :=
  (2 * (20115621 / 50000000) + (61 / 100) * (28794111 / 12500000) / Real.sqrt L + 39 / L) /
    (10971611 / 5000000)

/-- Above logarithmic scale two trillion, the adaptive Gaussian slope is at least
`36 / 100`. Nonnegativity of the two correction terms supplies the profile's
lower-radius condition. -/
theorem adaptiveGaussianA_lower (L : ℝ) (hL : 2000000000000 ≤ L) :
    (36 / 100 : ℝ) ≤ adaptiveGaussianA L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have h1 : 0 ≤ (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L :=
    div_nonneg (by norm_num only) hs
  have h2 : 0 ≤ (39 : ℝ) / L := div_nonneg (by norm_num only) hL0
  dsimp only [adaptiveGaussianA]
  apply (le_div_iff₀ (by norm_num only)).2
  linarith only [h1, h2]

/-- Above logarithmic scale two trillion, the adaptive Gaussian slope is at most
`3666854 / 10000000`. Bounds for the two decreasing correction terms reduce the
claim to rational arithmetic and will certify a strict coefficient improvement. -/
theorem adaptiveGaussianA_upper (L : ℝ) (hL : 2000000000000 ≤ L) :
    adaptiveGaussianA L ≤ (3666854 / 10000000 : ℝ) := by
  have hs : (1414213 : ℝ) ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num only) (by linarith only [hL])).2
    nlinarith only [hL]
  have hd :
    (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L ≤
      (61 / 100 : ℝ) * (28794111 / 12500000) / 1414213 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hs
  have he : (39 : ℝ) / L ≤ 39 / 2000000000000 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hL
  dsimp only [adaptiveGaussianA]
  apply (div_le_iff₀ (by norm_num only)).2
  linarith only [hd, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
