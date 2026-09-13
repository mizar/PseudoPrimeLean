/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Finset.Interval

/-!
# Finite domains of positive odd nonsquares

This file defines positive odd nonsquares bounded by a natural endpoint.
It contains no character-theoretic or analytic assumptions.
-/

namespace PseudoPrime.NumberTheory

/--
`Admissible B n` states that `n` is positive, at most
`B`, odd, and not a square.  The four conjuncts expose the hypotheses used by later witness and
Selfridge theorems.
-/
def Admissible (B n : ℕ) : Prop :=
  0 < n ∧ n ≤ B ∧ Odd n ∧ ¬IsSquare n

/--
`admissibleFinset B` is the mathematical finite enumeration of all admissible inputs up to `B`.
It is noncomputable because it filters using the proposition `IsSquare`; executable scans will
use a separate decidable square test in the computation layer.
-/
noncomputable def admissibleFinset (B : ℕ) : Finset ℕ := by
  classical exact (Finset.range (B + 1)).filter (Admissible B)

/-- Membership in `admissibleFinset` is equivalent to the mathematical admissibility predicate. -/
theorem mem_admissibleFinset_iff {B n : ℕ} : n ∈ admissibleFinset B ↔ Admissible B n := by
  classical
  simp only [admissibleFinset, Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
  exact and_iff_right_of_imp fun hn ↦ hn.2.1

/-- An admissible input is positive. -/
theorem Admissible.pos {B n : ℕ} (hn : Admissible B n) : 0 < n :=
  hn.1

/-- An admissible input does not exceed its bound. -/
theorem Admissible.le {B n : ℕ} (hn : Admissible B n) : n ≤ B :=
  hn.2.1

/-- An admissible input is odd. -/
theorem Admissible.odd {B n : ℕ} (hn : Admissible B n) : Odd n :=
  hn.2.2.1

/-- An admissible input is not a square. -/
theorem Admissible.not_isSquare {B n : ℕ} (hn : Admissible B n) : ¬IsSquare n :=
  hn.2.2.2

end PseudoPrime.NumberTheory
