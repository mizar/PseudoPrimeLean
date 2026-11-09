/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring

/-! Powers of repeated real square roots. -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a nonnegative real number, squaring its square root recovers the number.
Use the real square-root identity as the first repeated-root certificate. -/
theorem sqrt_pow_two {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x) ^ 2 = x := by exact Real.sq_sqrt hx

/-- For a nonnegative real number, two successive square roots raised to the fourth power
recover the original number. Apply the square-root identity twice. -/
theorem sqrt_sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt (Real.sqrt x)) ^ 4 = x := by
  rw [show (Real.sqrt (Real.sqrt x)) ^ 4 = ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 by ring,
    Real.sq_sqrt (Real.sqrt_nonneg x), Real.sq_sqrt hx]

/-- For a nonnegative real number, three successive square roots raised to the eighth power
recover the original number. Three applications of the square-root identity establish the
equality, which can be used in numerical root certificates. -/
theorem sqrt_sqrt_sqrt_pow_eight {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt (Real.sqrt (Real.sqrt x))) ^ 8 = x := by
  have h0 := Real.sq_sqrt hx
  have h1 := Real.sq_sqrt (Real.sqrt_nonneg x)
  have h2 := Real.sq_sqrt (Real.sqrt_nonneg (Real.sqrt x))
  rw [show
      (Real.sqrt (Real.sqrt (Real.sqrt x))) ^ 8 =
        (((Real.sqrt (Real.sqrt (Real.sqrt x))) ^ 2) ^ 2) ^ 2
      by ring,
    h2, h1, h0]

end PseudoPrime.Analysis
