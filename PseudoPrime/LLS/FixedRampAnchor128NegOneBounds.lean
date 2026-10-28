/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FixedRampAnchor128Bounds
public import PseudoPrime.PseudoSquare.Bounds.TwoPoleConductorPrefixNegOneBounds

/-! # Negative Jacobi witnesses from the fixed-width certified anchor -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The conductor-prefix negative root is monotone on positive real inputs. Use logarithmic
monotonicity and positive coefficients. This transfers the common ambient level to the explicit
input-bound logarithm in the Jacobi witness theorem. -/
theorem fixedAnchorNegativeRoot_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    fixedAnchorNegativeRoot x ≤ fixedAnchorNegativeRoot y := by
  have h := Real.log_le_log hx hxy
  dsimp only [fixedAnchorNegativeRoot]
  linarith only [h, hxy]

end PseudoPrime.LLS
