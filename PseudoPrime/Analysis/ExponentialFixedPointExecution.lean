/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointSignedBounds

/-! # Explicit execution APIs for fixed-point Taylor sums -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The current lower Taylor term and the sum of preceding terms, updated together.
The pair recurrence avoids separately computing every prefix during execution. -/
def expFixedPointLowerState (a b scale : ℕ) : ℕ → ℕ × ℕ
  | 0 => (scale, 0)
  | k + 1 =>
    let p := expFixedPointLowerState a b scale k
    (p.1 * a / (b * (k + 1)), p.2 + p.1)

/-- The current upper Taylor term and the sum of preceding terms.
Advance the ceiling recurrence and accumulator together for explicit fast execution. -/
def expFixedPointUpperState (a b scale : ℕ) : ℕ → ℕ × ℕ
  | 0 => (scale, 0)
  | k + 1 =>
    let p := expFixedPointUpperState a b scale k
    ((p.1 * a + b * (k + 1) - 1) / (b * (k + 1)), p.2 + p.1)

/-- The lower state equals the specification term and its finite Taylor sum.
Induction and the sum recurrence prove exact equality of the execution state. -/
theorem expFixedPointLowerState_eq (a b scale n : ℕ) :
    expFixedPointLowerState a b scale n =
      (expFixedPointLowerTerm a b scale n, expFixedPointLowerSum a b scale n) := by
  induction n with
  | zero =>
    simp only [expFixedPointLowerState, expFixedPointLowerTerm, expFixedPointLowerSum,
      Finset.sum_range_zero]
  | succ n ih =>
    simp only [expFixedPointLowerState, ih, expFixedPointLowerTerm, expFixedPointLowerSum,
      Finset.sum_range_succ]

/-- The upper state equals the specification term and the sum of preceding terms.
Induction preserves both components; this justifies the fast upper envelope. -/
theorem expFixedPointUpperState_eq (a b scale n : ℕ) :
    expFixedPointUpperState a b scale n =
      (expFixedPointUpperTerm a b scale n,
        ∑ k ∈ Finset.range n, expFixedPointUpperTerm a b scale k) := by
  induction n with
  | zero => simp only [expFixedPointUpperState, expFixedPointUpperTerm, Finset.sum_range_zero]
  | succ n ih =>
    simp only [expFixedPointUpperState, ih, expFixedPointUpperTerm, Finset.sum_range_succ]

/-- The accumulated lower Taylor sum from the explicit state recurrence.
Its exact equality theorem connects this execution API to the proved specification. -/
def expFixedPointLowerSumFast (a b scale n : ℕ) : ℕ :=
  (expFixedPointLowerState a b scale n).2

/-- The accumulated upper Taylor sum plus twice the current term.
This executable upper envelope uses the same proven remainder as the specification. -/
def expFixedPointUpperSumFast (a b scale n : ℕ) : ℕ :=
  let p := expFixedPointUpperState a b scale n
  p.2 + 2 * p.1

/-- The signed rational lower envelope using the explicit state execution APIs.
Its branches match the specification and retain the same scale and term count. -/
def expFixedPointSignedLowerFast (a : ℤ) (b scale n : ℕ) : ℕ :=
  if 0 ≤ a then expFixedPointLowerSumFast a.toNat b scale n
  else scale * scale / expFixedPointUpperSumFast (-a).toNat b scale n

/-- The explicit lower execution API equals the finite-sum specification.
Project the proved state equality. This transfers all lower-bound theorems. -/
theorem expFixedPointLowerSumFast_eq (a b scale n : ℕ) :
    expFixedPointLowerSumFast a b scale n = expFixedPointLowerSum a b scale n := by
  rw [expFixedPointLowerSumFast, expFixedPointLowerState_eq]

/-- The explicit upper execution API equals the finite-sum specification.
Project the state equality and retain the doubled next term. -/
theorem expFixedPointUpperSumFast_eq (a b scale n : ℕ) :
    expFixedPointUpperSumFast a b scale n = expFixedPointUpperSum a b scale n := by
  rw [expFixedPointUpperSumFast, expFixedPointUpperState_eq]
  rfl

/-- The explicit signed execution API equals its specification.
Replace both branch calculations by their proved equality.
This uses no implicit compiler substitution. -/
theorem expFixedPointSignedLowerFast_eq (a : ℤ) (b scale n : ℕ) :
    expFixedPointSignedLowerFast a b scale n = expFixedPointSignedLower a b scale n := by
  simp only [expFixedPointSignedLowerFast, expFixedPointSignedLower, expFixedPointLowerSumFast_eq,
    expFixedPointUpperSumFast_eq]

end PseudoPrime.Analysis
