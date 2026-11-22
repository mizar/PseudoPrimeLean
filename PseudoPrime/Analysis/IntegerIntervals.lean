/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalChecks
import Mathlib.Tactic.Linarith

/-! # Composable integer interval certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Integer endpoints at a separately supplied scale. `lower` and `upper`
are candidate bounds; containment, rather than construction, certifies their order.
This representation is used by checked arithmetic expressions. -/
structure IntegerInterval where
  lower : ℤ
  upper : ℤ

/-- Real containment in an integer interval at scale `G`. Positive scale is
required by arithmetic soundness theorems rather than stored in the interval. -/
def IntegerInterval.Contains (I : IntegerInterval) (G : ℤ) (x : ℝ) : Prop :=
  (I.lower : ℝ) / G ≤ x ∧ x ≤ (I.upper : ℝ) / G

/-- Add integer endpoints to represent the sum at the same scale. No rounding
is needed, and the result is consumed by arithmetic expression evaluation. -/
def IntegerInterval.add (I J : IntegerInterval) : IntegerInterval :=
  ⟨I.lower + J.lower, I.upper + J.upper⟩

/-- Reverse and negate endpoints to represent sign reversal at the same scale.
This also supports subtraction and negative reciprocal certificates. -/
def IntegerInterval.neg (I : IntegerInterval) : IntegerInterval :=
  ⟨-I.upper, -I.lower⟩

/-- Containment is preserved by endpoint addition. Cast addition and divide
linearly, then add the two certified bounds. -/
theorem IntegerInterval.add_contains {I J : IntegerInterval} {G : ℤ} {x y : ℝ} (hx : I.Contains G x)
    (hy : J.Contains G y) : (I.add J).Contains G (x + y) := by
  constructor
  · simpa only [add, Int.cast_add, add_div] using add_le_add hx.1 hy.1
  · simpa only [add, Int.cast_add, add_div] using add_le_add hx.2 hy.2

/-- Containment is preserved by sign reversal. Negation reverses both endpoint
inequalities; this supplies the unary arithmetic expression case. -/
theorem IntegerInterval.neg_contains {I : IntegerInterval} {G : ℤ} {x : ℝ} (hx : I.Contains G x) :
    I.neg.Contains G (-x) := by
  constructor
  · simpa only [neg, Int.cast_neg, neg_div] using neg_le_neg hx.2
  · simpa only [neg, Int.cast_neg, neg_div] using neg_le_neg hx.1

/-- A checked four-corner product composes two interval certificates into a
certificate for their real product, using the common integer scale. -/
theorem IntegerInterval.product_contains {I J K : IntegerInterval} {G : ℤ} {x y : ℝ}
    (h : integerProductCheck G I.lower I.upper J.lower J.upper K.lower K.upper = true)
    (hx : I.Contains G x) (hy : J.Contains G y) : K.Contains G (x * y) := by
  exact integerProductCheck_sound h hx hy

/-- Enlarge an integer interval by `r` ticks on both sides. Nonnegative radius
is supplied when this operation is used to transport approximation errors. -/
def IntegerInterval.widen (I : IntegerInterval) (r : ℤ) : IntegerInterval :=
  ⟨I.lower - r, I.upper + r⟩

/-- A certified approximation interval and an absolute error bound enclose the
true value in the widened interval. This transports Taylor and phase errors. -/
theorem IntegerInterval.widen_contains {I : IntegerInterval} {G r : ℤ} {v x : ℝ}
    (hv : I.Contains G v) (he : |x - v| ≤ (r : ℝ) / G) : (I.widen r).Contains G x := by
  have herr := abs_le.mp he
  constructor
  · change (((I.lower - r : ℤ) : ℝ) / G) ≤ x
    rw [Int.cast_sub, sub_div]
    linarith only [hv.1, herr.1]
  · change x ≤ (((I.upper + r : ℤ) : ℝ) / G)
    rw [Int.cast_add, add_div]
    linarith only [hv.2, herr.2]

/-- Scale endpoints by an integer, reversing their order for a negative factor.
This handles signed binary logarithm exponents in interval certificates. -/
def IntegerInterval.scale (I : IntegerInterval) (k : ℤ) : IntegerInterval :=
  if 0 ≤ k then ⟨k * I.lower, k * I.upper⟩ else ⟨k * I.upper, k * I.lower⟩

/-- Integer scalar multiplication transports containment at the same scale.
The sign split accounts for reversed bounds without assuming a nonnegative scalar. -/
theorem IntegerInterval.scale_contains {I : IntegerInterval} {G k : ℤ} {x : ℝ}
    (hx : I.Contains G x) : (I.scale k).Contains G ((k : ℝ) * x) := by
  by_cases hk : 0 ≤ k
  · have hr : (0 : ℝ) ≤ k := by exact_mod_cast hk
    constructor
    · simpa only [scale, ite_eq_left hk, Int.cast_mul, mul_div_assoc] using
        mul_le_mul_of_nonneg_left hx.1 hr
    · simpa only [scale, ite_eq_left hk, Int.cast_mul, mul_div_assoc] using
        mul_le_mul_of_nonneg_left hx.2 hr
  · have hr : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hk)
    constructor
    · simpa only [scale, ite_eq_right hk, Int.cast_mul, mul_div_assoc] using
        mul_le_mul_of_nonpos_left hx.2 hr
    · simpa only [scale, ite_eq_right hk, Int.cast_mul, mul_div_assoc] using
        mul_le_mul_of_nonpos_left hx.1 hr

end PseudoPrime.Analysis
