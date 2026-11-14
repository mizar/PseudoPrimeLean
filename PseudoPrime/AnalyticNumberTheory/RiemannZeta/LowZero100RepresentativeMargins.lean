/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FourthMargin
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100LastMargin

/-! # Representative low-zero endpoint margins -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The fourth and twenty-ninth lower endpoints satisfy their prescribed opposite normalized
zeta margins. Both unconditional estimates are proved from internally checked finite sums. -/
theorem low_zero_representative_margins :
    (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (31155 / 1024) ∧
      RiemannXi.normalizedZeta (101203 / 1024) < -(9 / 100000 : ℝ) := by
  exact ⟨low_zero_fourth_lower_margin, low_zero_last_lower_margin⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
