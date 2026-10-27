/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.AdaptivePhaseIntervalTree
public import PseudoPrime.Analysis.Phase64FirstScaleCell
public import PseudoPrime.Analysis.Phase64AdaptiveCell.Block09

/-! # Adaptive Gamma phase certificate block 13 -/

@[expose] public section

namespace PseudoPrime.Analysis.Phase64AdaptiveCell.Block13

/-- A dyadic partition of this block's ordinate interval.
Role: store only the tree shape; all rational endpoint calculations remain in the checker. -/
def tree : RationalIntervalTree :=
  (.split
    (.split
      (.split (.split (.split .leaf .leaf) (.split .leaf .leaf))
        (.split (.split .leaf .leaf) (.split .leaf .leaf)))
      (.split (.split (.split .leaf .leaf) (.split .leaf (.split .leaf .leaf)))
        (.split (.split (.split .leaf .leaf) (.split .leaf .leaf))
          (.split (.split .leaf .leaf) (.split .leaf .leaf)))))
    (.split
      (.split
        (.split (.split (.split .leaf .leaf) (.split .leaf .leaf))
          (.split (.split .leaf .leaf) (.split .leaf .leaf)))
        (.split (.split (.split .leaf .leaf) (.split .leaf .leaf))
          (.split (.split .leaf .leaf) (.split (.split .leaf .leaf) (.split .leaf .leaf)))))
      (.split
        (.split
          (.split (.split (.split .leaf .leaf) (.split .leaf .leaf))
            (.split (.split .leaf .leaf) (.split .leaf .leaf)))
          (.split (.split (.split .leaf .leaf) (.split .leaf .leaf))
            (.split (.split .leaf .leaf) (.split .leaf .leaf))))
        (.split
          (.split (.split (.split .leaf .leaf) (.split .leaf .leaf))
            (.split (.split .leaf .leaf) (.split .leaf .leaf)))
          (.split
            (.split (.split (.split .leaf .leaf) (.split .leaf .leaf))
              (.split (.split .leaf .leaf) (.split .leaf .leaf)))
            (.split (.split (.split .leaf .leaf) (.split .leaf .leaf))
              (.split (.split .leaf .leaf) (.split .leaf .leaf))))))))

/-- Claim: every leaf satisfies the exact rational Gamma-phase interpolation inequalities.
Proof: compute the rational checker in the kernel.
Role: certify continuous coverage after applying interval-tree soundness. -/
theorem checked :
    rationalIntervalTreeCheck
        (scaledPhaseIntervalCheck (10 ^ 12) phaseCell64Center phaseCell64Uncertainty) (65 / 16)
        (35 / 8) tree =
      true := by
  decide +kernel

end PseudoPrime.Analysis.Phase64AdaptiveCell.Block13
