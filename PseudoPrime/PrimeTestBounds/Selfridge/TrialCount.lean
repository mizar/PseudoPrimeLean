/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.Selfridge.TrialCount
import PseudoPrime.PrimeTestBounds.Selfridge.MaximumBridge
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Unconditional maximum and real trial counts
-/

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Apply `PrimeTest.classicalTrialCountThrough` to the largest classical `≠1` stopping value up
    to `B`.
This is the aggregate count used in `classicalTrialMaximum_elementary_bound_explicit`.
If the admissible input set is empty, its stopping-value supremum is `0` and this definition
returns `1`, by the convention in `PrimeTest.classicalTrialCountThrough`. -/
noncomputable def classicalNeOneTrialMaximum (B : ℕ) : ℕ :=
  PrimeTest.classicalTrialCountThrough (classicalNeOneMaximum B)

/-- Apply `PrimeTest.classicalTrialCountThrough` to the largest classical pure `-1` stopping
    value up to `B`.
This is the aggregate count bounded by `classicalNegOneTrialMaximum_real_le`.
If the admissible input set is empty, its stopping-value supremum is `0` and this definition
returns `1`, by the convention in `PrimeTest.classicalTrialCountThrough`. -/
noncomputable def classicalNegOneTrialMaximum (B : ℕ) : ℕ :=
  PrimeTest.classicalTrialCountThrough (classicalNegOneMaximum B)

/-- For every natural `i`, the real trial count is at most `i/2 + 1`.
The proof uses `↑((i-5)/2) ≤ ↑(i-5)/2` from `Nat.cast_div_le` and
`↑(i-5) ≤ ↑i` from `Nat.sub_le`. This supplies the count estimate used by
`classicalNegOneTrialMaximum_real_le`; no candidate assumption is needed. -/
theorem classicalTrialCountThrough_real_le (i : ℕ) :
    (PrimeTest.classicalTrialCountThrough i : ℝ) ≤ (i : ℝ) / 2 + 1 := by
  unfold PrimeTest.classicalTrialCountThrough
  have hdiv : (((i - 5) / 2 : ℕ) : ℝ) ≤ ((i - 5 : ℕ) : ℝ) / 2 := Nat.cast_div_le
  have hsub : ((i - 5 : ℕ) : ℝ) ≤ (i : ℝ) := by exact Nat.cast_le.mpr (Nat.sub_le i 5)
  push_cast
  linarith only [hdiv, hsub]

end PseudoPrime.PrimeTestBounds.Selfridge
