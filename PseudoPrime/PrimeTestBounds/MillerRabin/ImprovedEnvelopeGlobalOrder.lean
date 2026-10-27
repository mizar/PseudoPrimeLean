/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRClippedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedEnvelopeOrder
/-! # Global comparisons for the clipped Gaussian envelope -/
@[expose] public section

namespace PseudoPrime.Analysis
/-- For L>=240, the constant-six Gaussian radius is at most 73L/100. Its exact
budget equation and root>=13 absorb the square-root term. This gives a global quadratic cap. -/
theorem six_radius_linear_upper {L : ℝ} (hL : 240 ≤ L) :
    gaussianMR6Radius L ≤ (73 / 100 : ℝ) * L := by
  have he := gaussianMR6_equation (by linarith only [hL] : (0 : ℝ) ≤ L)
  have ht := gaussianMR6_root_lower hL
  have hp := gaussianMR6_root_pos L
  have hs : 13 * gaussianMR6Root L ≤ gaussianMR6Radius L := by
    dsimp only [gaussianMR6Radius]
    nlinarith only [ht, mul_nonneg hp.le (by linarith only [ht] :
      (0 : ℝ) ≤ gaussianMR6Root L - 13)]
  norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsConductor,
    gaussianMR6FifthsIndex, gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint] at he
  linarith only [he, hs, hL]
/-- For L>=240, B6<=15987 L squared/25000. Square the nonnegative linear
radius bound. This cap separates the Gaussian envelope from the Gamma and endpoint candidates. -/
theorem six_quadratic_upper {L : ℝ} (hL : 240 ≤ L) :
    gaussianMR6Bound L ≤ (15987 / 25000 : ℝ) * L ^ 2 := by
  have hr := six_radius_linear_upper hL
  have hp : 0 ≤ gaussianMR6Radius L := sq_nonneg _
  have hq : 0 ≤ (73 / 100 : ℝ) * L := by linarith only [hL]
  have hs := (sq_le_sq₀ hp hq).mpr hr
  dsimp only [gaussianMR6Bound]
  nlinarith only [hs]

/-- For L>=240, the selected clipped Gaussian envelope is strictly below B6.
Use the exact selection equality and the strict 35000-profile comparison. -/
theorem floorSelected_lt_six {L : ℝ} (hL : 240 ≤ L) :
    gaussianFloorSelected L < gaussianMR6Bound L := by
  rw [← gaussianFloor_min_eq_selected (by linarith only [hL] : (63 : ℝ) ≤ L)]
  exact (min_le_left _ _).trans_lt (gaussianFloor35_lt_six hL)

end PseudoPrime.Analysis
namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- For L>=100, the sharper Gamma root exceeds 13L/25. The gap at this
positive test radius is negative, so root monotonicity excludes every smaller root. -/
theorem sharp_root_linear_lower {L : ℝ} (hL : 100 ≤ L) : (13 / 25 : ℝ) * L < gammaSharpRoot L := by
  have hp : 0 < (13 / 25 : ℝ) * L := by linarith only [hL]
  have hnum : 0 < (7 / 6 : ℝ) * L + 20475759 / 494000 := by linarith only [hL]
  have hr := div_pos hnum hp
  have hg : gammaSharpGap L ((13 / 25) * L) < 0 := by
    dsimp only [gammaSharpGap]
    nlinarith only [hr, hL]
  by_contra hn
  have hnonneg := gammaSharpGap_nonneg_of_root_le hL (le_of_not_gt hn)
  linarith only [hg, hnonneg]
/-- For L>=100, G1>16731 L squared/25000. Square the positive root lower
bound and retain the cutoff coefficient. This separates G1 from the high Gaussian branch. -/
theorem sharp_quadratic_lower {L : ℝ} (hL : 100 ≤ L) :
    (16731 / 25000 : ℝ) * L ^ 2 < gammaSharpBound L := by
  have hr := sharp_root_linear_lower hL
  have hp : 0 ≤ (13 / 25 : ℝ) * L := by linarith only [hL]
  have hs := (sq_lt_sq₀ hp (gammaSharpRoot_pos hL).le).mpr hr
  dsimp only [gammaSharpBound]
  nlinarith only [hs]

/-- For L>=240, the selected clipped Gaussian bound is strictly below G1.
Compare the constant-six quadratic cap with the sharper Gamma quadratic lower bound. -/
theorem gaussianSelected_lt_sharp {L : ℝ} (hL : 240 ≤ L) :
    Analysis.gaussianFloorSelected L < gammaSharpBound L := by
  have hu := Analysis.six_quadratic_upper hL
  have hl := sharp_quadratic_lower (by linarith only [hL] : (100 : ℝ) ≤ L)
  have hg := Analysis.floorSelected_lt_six hL
  nlinarith only [hu, hl, hg, sq_nonneg L]

/-- For L>=240, the selected clipped Gaussian bound is strictly below C4.
Compare the constant-six quadratic cap with the global fourth-radius lower bound. -/
theorem gaussianSelected_lt_fourStep {L : ℝ} (hL : 240 ≤ L) :
    Analysis.gaussianFloorSelected L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hu := Analysis.six_quadratic_upper hL
  have hl := LLS.PaperStatements.fourStep_quadratic_lower hL
  have hg := Analysis.floorSelected_lt_six hL
  nlinarith only [hu, hl, hg, sq_nonneg L]

end PseudoPrime.PrimeTestBounds.MillerRabin
