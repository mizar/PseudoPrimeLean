/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaCutoffNumerics

/-! # Proven Gaussian cutoff integral lower bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The actual Gaussian profile cutoff mass at 21/10 exceeds 81470555/100000000.
Combine the kernel-verified 16,000-node integer sum with the analytic curvature
error and nonnegative tails. Exact rational comparison leaves positive slack.
This discharges the cutoff-integral input of the P2 Gaussian denominator. -/
theorem gaussianGammaCutoff_mass_gt_target :
    (81470555 / 100000000 : ℝ) <
      ∫ u in (0 : ℝ)..(21 / 10), gaussianGammaProfile u / Real.sqrt u := by
  have h := gaussianCutoffMidpointLower_le_mass
  rw [← gaussianCutoffMidpointLowerFast_eq, gaussianCutoffMidpointLowerFast_value,
    gaussianCutoffNodeScale] at h
  have hn :
    (81470555 / 100000000 : ℝ) <
      (8147136487896092080199149897249194016357 : ℝ) / (10 ^ 40 : ℕ) - 97 / 12000000 := by
    norm_num only
  exact hn.trans_le h

end PseudoPrime.Analysis
