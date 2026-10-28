/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularFiniteZeroMass
public import PseudoPrime.LLS.TriangularArchimedeanBounds

/-! # Signed arithmetic formula for triangular absolute zero mass

Keep the character and inverse-character arithmetic sums on the left.
Only the two gamma integrals remain in addition to the conductor.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a nonzero real parameter the entire triangular transform is even.
Expand the exponential quotient away from zero and treat zero separately.
This identifies reflected vertical integrals without taking norms. -/
theorem triangularMellinFunction_neg {a : ℝ} (ha : a ≠ 0) (s : ℂ) :
    triangularMellinFunction a (-s) = triangularMellinFunction a s := by
  by_cases hs : s = 0
  · subst s
    rw [neg_zero]
  · rw [triangularMellinFunction_of_ne_zero ha (neg_ne_zero.mpr hs),
      triangularMellinFunction_of_ne_zero ha hs]
    simp only [mul_neg, neg_neg, div_neg]
    congr 1
    ring

end PseudoPrime.Analysis
