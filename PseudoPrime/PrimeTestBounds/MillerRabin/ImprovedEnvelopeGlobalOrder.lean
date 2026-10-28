/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRClippedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedEnvelopeOrder
public import PseudoPrime.Analysis.ImprovedEnvelopeGlobalOrder

/-! # Global comparisons for the clipped Gaussian envelope -/

@[expose] public section

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
