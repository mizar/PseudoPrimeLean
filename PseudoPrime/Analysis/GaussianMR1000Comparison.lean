/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMR1000WitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedIntervalSelection
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaReflectedComparison

/-! # Continuous comparisons for the sharp 1000-prefix Gaussian bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L>=132, the raw large-index root exceeds ten. Compare its exact
quadratic equation with the rational anchor; this controls the linear radius cap. -/
theorem gaussian1000_large_anchor {L : ℝ} (hL : 132 ≤ L) : (10 : ℝ) < gaussian1000LargeRoot L := by
  have hp := gaussian1000_large_pos L
  have he := gaussian1000_large_equation (by linarith only [hL] : (0 : ℝ) ≤ L)
  by_contra hn
  have ht : gaussian1000LargeRoot L ≤ 10 := le_of_not_gt hn
  have hs : gaussian1000LargeRoot L ^ 2 ≤ 10 * gaussian1000LargeRoot L := by
    nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr ht)]
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
    gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsIndex,
    gaussianMR6FifthsEndpoint] at he
  nlinarith only [he, hs, ht, hL]

/-- For L>=132, the raw index-four root exceeds 52/5. Its exact quadratic
equation excludes every smaller positive root by rational arithmetic. -/
theorem gaussian1000_four_anchor {L : ℝ} (hL : 132 ≤ L) :
    (52 / 5 : ℝ) < gaussian1000FourRoot L := by
  have hp := gaussian1000_four_pos L
  have he := gaussian1000_four_equation (by linarith only [hL] : (0 : ℝ) ≤ L)
  by_contra hn
  have ht : gaussian1000FourRoot L ≤ 52 / 5 := le_of_not_gt hn
  have hs : gaussian1000FourRoot L ^ 2 ≤ (52 / 5 : ℝ) * gaussian1000FourRoot L := by
    nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr ht)]
  norm_num only [gaussian1000FourD, gaussian1000FourBeta, gaussianMRRefinedConductor,
    gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint] at he
  nlinarith only [he, hs, ht, hL]

/-- For L>=132, the large-index radius is at most 69L/100+39/2.
Use the root anchor ten to absorb beta*t into a multiple of t squared. -/
theorem gaussian1000_large_square_upper {L : ℝ} (hL : 132 ≤ L) :
    gaussian1000LargeRoot L ^ 2 ≤ (69 / 100 : ℝ) * L + 39 / 2 := by
  have ht := gaussian1000_large_anchor hL
  have hp := gaussian1000_large_pos L
  have he := gaussian1000_large_equation (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hprod := mul_nonneg (by linarith only [ht] : 0 ≤ gaussian1000LargeRoot L - 10) hp.le
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedConductor,
    gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsIndex,
    gaussianMR6FifthsEndpoint] at he
  nlinarith only [he, hprod, hL]

/-- For L>=132, the index-four radius is at most 69L/100+39/2.
Use the sharper anchor 52/5 in its independent conductor-saving equation. -/
theorem gaussian1000_four_square_upper {L : ℝ} (hL : 132 ≤ L) :
    gaussian1000FourRoot L ^ 2 ≤ (69 / 100 : ℝ) * L + 39 / 2 := by
  have ht := gaussian1000_four_anchor hL
  have hp := gaussian1000_four_pos L
  have he := gaussian1000_four_equation (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hprod := mul_nonneg (by linarith only [ht] : 0 ≤ gaussian1000FourRoot L - 52 / 5) hp.le
  norm_num only [gaussian1000FourD, gaussian1000FourBeta, gaussianMRRefinedConductor,
    gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint] at he
  nlinarith only [he, hprod, hL]

/-- For L>=132, the combined radius is at most 69L/100+39/2.
Both raw radii and the floor one hundred satisfy this cap; square-root
monotonicity transfers the bound through the root maximum. -/
theorem gaussian1000_radius_upper {L : ℝ} (hL : 132 ≤ L) :
    gaussian1000Radius L ≤ (69 / 100 : ℝ) * L + 39 / 2 := by
  have hR : (0 : ℝ) ≤ (69 / 100) * L + 39 / 2 := by linarith only [hL]
  have hten : (10 : ℝ) ≤ Real.sqrt ((69 / 100) * L + 39 / 2) :=
    (Real.le_sqrt (by norm_num only) hR).mpr (by linarith only [hL])
  have hlarge :=
    (Real.le_sqrt (gaussian1000_large_pos L).le hR).mpr (gaussian1000_large_square_upper hL)
  have hfour :=
    (Real.le_sqrt (gaussian1000_four_pos L).le hR).mpr (gaussian1000_four_square_upper hL)
  exact (Real.le_sqrt (gaussian1000_root_pos L).le hR).mp (max_le hten (max_le hlarge hfour))

/-- For L>=132, the 1000-prefix cutoff is at most six fifths of the square
of 69L/100+39/2. Square the nonnegative radius bound for Gamma comparisons. -/
theorem gaussian1000_cutoff_upper {L : ℝ} (hL : 132 ≤ L) :
    gaussian1000Bound L ≤ (6 / 5 : ℝ) * ((69 / 100) * L + 39 / 2) ^ 2 := by
  have hr := gaussian1000_radius_upper hL
  have hp := (by norm_num only : (0 : ℝ) ≤ 100).trans (gaussian1000_radius_hundred L)
  have hs := (sq_le_sq₀ hp (hp.trans hr)).mpr hr
  exact mul_le_mul_of_nonneg_left hs (by norm_num only)

/-- For 0<=L<=235, the combined Gaussian cutoff is strictly below 35000.
Both raw roots are at most 653/50 by exact budget certificates, and the
rescaled fourth power of this anchor is strictly below the fixed bound. -/
theorem gaussian1000_lt_fixed {L : ℝ} (hL : 0 ≤ L) (hU : L ≤ 235) :
    gaussian1000Bound L < 35000 := by
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hlarge : gaussian1000LargeRoot L ≤ (653 / 50 : ℝ) := by
    apply
      gaussianBudgetRoot_le_of_budget gaussianMRRefined_coefficients.1
        gaussianMRRefined_coefficients.2
        (add_nonneg (mul_nonneg hc hL) (by norm_num only : (0 : ℝ) ≤ 163 / 20))
    · norm_num only [gaussianMRRefinedBeta, gaussianMRRefinedD, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    · norm_num only [gaussianMRRefinedBeta, gaussianMRRefinedD, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint,
        gaussianMRRefinedConductor]
      linarith only [hU]
  have hfour : gaussian1000FourRoot L ≤ (653 / 50 : ℝ) := by
    apply
      gaussianBudgetRoot_le_of_budget gaussian1000_coefficients.1 gaussian1000_coefficients.2
        (add_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hc) hL)
          (by norm_num only : (0 : ℝ) ≤ 127 / 10))
    · norm_num only [gaussian1000FourBeta, gaussian1000FourD, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint]
    · norm_num only [gaussian1000FourBeta, gaussian1000FourD, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor]
      linarith only [hU]
  have hs : gaussian1000Root L ≤ (653 / 50 : ℝ) := max_le (by norm_num only) (max_le hlarge hfour)
  have hs2 := (sq_le_sq₀ (gaussian1000_root_pos L).le (by norm_num only)).mpr hs
  have hs4 := (sq_le_sq₀ (sq_nonneg (gaussian1000Root L)) (sq_nonneg (653 / 50 : ℝ))).mpr hs2
  dsimp only [gaussian1000Bound, gaussian1000Radius]
  nlinarith only [hs4]

end PseudoPrime.Analysis
