/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSingleRoot
public import PseudoPrime.Analysis.GaussianRecoveredRoot
public import PseudoPrime.LLS.PaperStatements.EndpointPointwiseNinth

/-! # Continuous strict comparisons for single-root Gaussian cutoffs -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For levels at least 132, the original raw large-index root exceeds ten.
The budget at ten contradicts its completed positive-root equation; clipping is inactive. -/
theorem gaussianLargeRoot_gt_ten {L : ℝ} (hL : 132 ≤ L) : (10 : ℝ) < gaussian1000LargeRoot L := by
  have hC : 0 ≤ gaussianMRRefinedConductor * L + 163 / 20 := by
    have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
    nlinarith only [hc, hL]
  have hb : gaussianMRRefinedBeta < gaussianMRRefinedD * 10 := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  by_contra ht
  have hbudget :=
    gaussianBudget_of_root_le gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2 hC
      hb (le_of_not_gt ht)
  change
    gaussianMRRefinedConductor * L + 163 / 20 + gaussianMRRefinedBeta * 10 ≤
      gaussianMRRefinedD * 10 ^ 2 at hbudget
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex,
    gaussianMRRefinedConductor] at hbudget
  linarith only [hbudget, hL]

/-- On the real interval [132,215], the raw large-index root is at most 251/20.
Evaluate the quadratic at that rational cap and use the exact root comparison theorem. -/
theorem gaussianLargeRoot_le_cap {L : ℝ} (hL : 132 ≤ L) (hU : L ≤ 215) :
    gaussian1000LargeRoot L ≤ 251 / 20 := by
  have hC : 0 ≤ gaussianMRRefinedConductor * L + 163 / 20 := by
    have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
    nlinarith only [hc, hL]
  apply
    gaussianBudgetRoot_le_of_budget gaussianMRRefined_coefficients.1
      gaussianMRRefined_coefficients.2 hC
  · norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  · norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex,
      gaussianMRRefinedConductor]
    linarith only [hU]

/-- For levels at least 132, the single-root radius is at most four fifths of
the level. Absorb its linear root term using the floor-ten lower bound and evaluate
the remaining rational margin at 132. -/
theorem gaussianSingle_radius_upper {L : ℝ} (hL : 132 ≤ L) :
    gaussianSingleRadius L ≤ (4 / 5 : ℝ) * L := by
  have ht := gaussianLargeRoot_gt_ten hL
  have he := gaussian1000_large_equation (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hbeta := gaussianMRRefined_coefficients.2
  have hscale :
    gaussianMRRefinedBeta * gaussian1000LargeRoot L ≤
      (gaussianMRRefinedBeta / 10) * gaussian1000LargeRoot L ^ 2 := by
    have hh : 0 ≤ gaussian1000LargeRoot L * (gaussian1000LargeRoot L - 10) :=
      mul_nonneg (by linarith only [ht]) (by linarith only [ht])
    have hm := mul_nonneg hbeta.le hh
    nlinarith only [hm]
  have hd : 0 < gaussianMRRefinedD - gaussianMRRefinedBeta / 10 := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hc :
    0 <
      (4 / 5 : ℝ) * (gaussianMRRefinedD - gaussianMRRefinedBeta / 10) -
        gaussianMRRefinedConductor := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex,
      gaussianMRRefinedConductor]
  have ha :
    (163 / 20 : ℝ) <
      ((4 / 5) * (gaussianMRRefinedD - gaussianMRRefinedBeta / 10) - gaussianMRRefinedConductor) *
        132 := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex,
      gaussianMRRefinedConductor]
  have hm := mul_le_mul_of_nonneg_left hL hc.le
  have hr : gaussian1000LargeRoot L ^ 2 ≤ (4 / 5 : ℝ) * L := by
    nlinarith only [he, hscale, ha, hm, hd]
  simpa only [gaussianSingleRadius, gaussianSingleRoot, max_eq_right ht.le] using hr

/-- For levels at least 132, the single-root cutoff is strictly below the
pointwise cutoff. Compare 96/125 times the level square with its 81/100 lower bound. -/
theorem gaussianSingle_lt_pointwise {L : ℝ} (hL : 132 ≤ L) :
    gaussianSingleBound L < LLS.PaperStatements.pointwiseCutoff L := by
  have hr := gaussianSingle_radius_upper hL
  have hs :=
    (sq_le_sq₀
          (by linarith only [gaussianSingle_radius_hundred L] : (0 : ℝ) ≤ gaussianSingleRadius L)
          (by linarith only [hL] : (0 : ℝ) ≤ (4 / 5) * L)).mpr
      hr
  have hc := LLS.PaperStatements.pointwiseCutoff_lower81 (by linarith only [hL] : (100 : ℝ) ≤ L)
  have hpos : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [gaussianSingleBound]
  nlinarith only [hs, hc, hpos]

/-- On [132,215], the single-root cutoff is strictly below the original two-root
cutoff. Eliminate the large-root equation, evaluate the increasing separation
polynomial at 251/20, and show the old index-four root is strictly larger. -/
theorem gaussianSingle_lt_original {L : ℝ} (hL : 132 ≤ L) (hU : L ≤ 215) :
    gaussianSingleBound L < gaussian1000Bound L := by
  let t := gaussian1000LargeRoot L
  let A := gaussian1000FourD - (2 / 3 : ℝ) * gaussianMRRefinedD
  let B := gaussian1000FourBeta - (2 / 3 : ℝ) * gaussianMRRefinedBeta
  let C : ℝ := (2 / 3) * (163 / 20) - 127 / 10
  have ht : (10 : ℝ) < t := gaussianLargeRoot_gt_ten hL
  have hq : t ≤ 251 / 20 := gaussianLargeRoot_le_cap hL hU
  have hA : 0 < A := by
    norm_num only [A, gaussian1000FourD, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hAB : B < 20 * A := by
    norm_num only [A, B, gaussian1000FourD, gaussian1000FourBeta, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hcap : A * (251 / 20 : ℝ) ^ 2 - B * (251 / 20) + C < 0 := by
    norm_num only [A, B, C, gaussian1000FourD, gaussian1000FourBeta, gaussianMRRefinedD,
      gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hsum : (20 : ℝ) ≤ 251 / 20 + t := by linarith only [ht]
  have hmul := mul_le_mul_of_nonneg_left hsum hA.le
  have hfac : 0 ≤ A * (251 / 20 + t) - B := by linarith only [hmul, hAB]
  have hp := mul_nonneg (sub_nonneg.mpr hq) hfac
  have hpoly : A * t ^ 2 - B * t + C < 0 := by
    calc
      A * t ^ 2 - B * t + C =
          (A * (251 / 20 : ℝ) ^ 2 - B * (251 / 20) + C) -
            (251 / 20 - t) * (A * (251 / 20 + t) - B) :=
        by ring
      _ ≤ A * (251 / 20 : ℝ) ^ 2 - B * (251 / 20) + C := sub_le_self _ hp
      _ < 0 := hcap
  have he := gaussian1000_large_equation (by linarith only [hL] : (0 : ℝ) ≤ L)
  change
    gaussianMRRefinedD * t ^ 2 =
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * t + 163 / 20 at he
  have hneg :
    gaussian1000FourD * t ^ 2 <
      (2 / 3 : ℝ) * gaussianMRRefinedConductor * L + gaussian1000FourBeta * t + 127 / 10 := by
    dsimp only [A, B, C] at hpoly
    nlinarith only [hpoly, he]
  have hcoef : gaussian1000FourBeta < gaussian1000FourD * t := by
    have hb : gaussian1000FourBeta < gaussian1000FourD * 10 := by
      norm_num only [gaussian1000FourBeta, gaussian1000FourD, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsEndpoint]
    have hm := mul_le_mul_of_nonneg_left ht.le gaussian1000_coefficients.1.le
    linarith only [hb, hm]
  have hC4 : 0 ≤ (2 / 3 : ℝ) * gaussianMRRefinedConductor * L + 127 / 10 := by
    have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
    nlinarith only [hc, hL]
  have hfour : t < gaussian1000FourRoot L := by
    by_contra hh
    have hg :=
      gaussianBudget_of_root_le gaussian1000_coefficients.1 gaussian1000_coefficients.2 hC4 hcoef
        (le_of_not_gt hh)
    change
      (2 / 3 : ℝ) * gaussianMRRefinedConductor * L + 127 / 10 + gaussian1000FourBeta * t ≤
        gaussian1000FourD * t ^ 2 at hg
    linarith only [hg, hneg]
  have hlarge : gaussianSingleRoot L = t := max_eq_right ht.le
  have htwo : gaussianSingleRoot L < gaussian1000Root L := by
    rw [hlarge]
    exact hfour.trans_le ((le_max_right _ _).trans (le_max_right _ _))
  have hs := (sq_lt_sq₀ (gaussianSingle_root_pos L).le (gaussian1000_root_pos L).le).mpr htwo
  have hss := (sq_lt_sq₀ (sq_nonneg (gaussianSingleRoot L)) (sq_nonneg (gaussian1000Root L))).mpr hs
  dsimp only [gaussianSingleBound, gaussianSingleRadius, gaussian1000Bound, gaussian1000Radius]
  nlinarith only [hss]

/-- For levels at least 132, recovering the prefix strictly decreases the
single-root cutoff. The raw budget allowance decreases from 8.15 to 8.14, and
the old raw root is above the clipping floor. -/
theorem gaussianRecovered_lt_single {L : ℝ} (hL : 132 ≤ L) :
    gaussianRecoveredBound L < gaussianSingleBound L := by
  have ht := gaussianLargeRoot_gt_ten hL
  have hC : 0 ≤ gaussianMRRefinedConductor * L + 407 / 50 := by
    have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
    nlinarith only [hc, hL]
  have hraw : gaussianRecoveredLargeRoot L < gaussian1000LargeRoot L := by
    exact
      gaussianBudgetRoot_strictMono gaussianMRRefined_coefficients.1 hC
        (by linarith only [] :
          gaussianMRRefinedConductor * L + 407 / 50 < gaussianMRRefinedConductor * L + 163 / 20)
  have hroot : gaussianRecoveredRoot L < gaussianSingleRoot L := by
    rw [gaussianSingleRoot, max_eq_right ht.le]
    exact max_lt ht hraw
  have hs := (sq_lt_sq₀ (gaussianRecovered_root_pos L).le (gaussianSingle_root_pos L).le).mpr hroot
  have hss :=
    (sq_lt_sq₀ (sq_nonneg (gaussianRecoveredRoot L)) (sq_nonneg (gaussianSingleRoot L))).mpr hs
  dsimp only [gaussianRecoveredBound, gaussianRecoveredRadius, gaussianSingleBound,
    gaussianSingleRadius]
  nlinarith only [hss]

/-- For levels at least 132, the recovered cutoff is strictly below the
pointwise cutoff. Compose the strict root improvement with the continuous comparison. -/
theorem gaussianRecovered_lt_pointwise {L : ℝ} (hL : 132 ≤ L) :
    gaussianRecoveredBound L < LLS.PaperStatements.pointwiseCutoff L := by
  exact (gaussianRecovered_lt_single hL).trans (gaussianSingle_lt_pointwise hL)

/-- For levels at least 132, the recovered cutoff is strictly below the
original two-root cutoff. Strict improvement over the single root suffices,
without requiring the old index-four root to dominate. -/
theorem gaussianRecovered_lt_original {L : ℝ} (hL : 132 ≤ L) :
    gaussianRecoveredBound L < gaussian1000Bound L := by
  exact (gaussianRecovered_lt_single hL).trans_le (gaussianSingle_bound_le L)

end PseudoPrime.Analysis
