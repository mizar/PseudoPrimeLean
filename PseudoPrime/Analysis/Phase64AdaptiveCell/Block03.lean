/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.AdaptivePhaseIntervalTree
public import PseudoPrime.Analysis.Phase64FirstScaleCell

/-! # Adaptive Gamma phase certificate block 03 -/

@[expose] public section

namespace PseudoPrime.Analysis.Phase64AdaptiveCell.Block03

/-- A dyadic partition of this block's ordinate interval.
Role: store only the tree shape; all rational endpoint calculations remain in the checker. -/
def tree : RationalIntervalTree :=
  (.split (.split .leaf .leaf) (.split .leaf (.split .leaf .leaf)))

/-- Claim: every leaf satisfies the exact rational Gamma-phase interpolation inequalities.
Proof: compute the rational checker in the kernel.
Role: certify continuous coverage after applying interval-tree soundness. -/
theorem checked :
    rationalIntervalTreeCheck
        (scaledPhaseIntervalCheck (10 ^ 12) phaseCell64Center phaseCell64Uncertainty) (15 / 16)
        (5 / 4) tree =
      true := by
  decide +kernel

end PseudoPrime.Analysis.Phase64AdaptiveCell.Block03
